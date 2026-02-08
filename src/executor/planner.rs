//! Query planner.

use crate::catalog::{Catalog, ColumnInfo};
use crate::datum::Type;
use crate::sql::{Expr, FromClause, SelectItem, SelectStmt, TableRef};
use crate::storage::{Replacer, Storage};
use crate::tx::Snapshot;

use super::error::ExecutorError;
use super::expr::{BoundExpr, resolve_column_index};
use super::plan::Plan;
use super::{ColumnDesc, ColumnSource};

/// Plans a SELECT statement into a logical [`Plan`] tree.
///
/// The planner resolves table references, binds column names to positional
/// indices, and constructs Filter/Projection plan nodes. No data is loaded
/// at this stage.
///
/// # Arguments
///
/// * `select` - The parsed SELECT statement
/// * `catalog` - Catalog for table/column metadata access
/// * `snapshot` - MVCC snapshot for catalog visibility checks
///
/// # Errors
///
/// Returns [`ExecutorError`] for unresolvable tables/columns, unsupported
/// features (JOINs, subqueries), or catalog I/O errors.
pub async fn plan_select<S: Storage, R: Replacer>(
    select: &SelectStmt,
    catalog: &Catalog<S, R>,
    snapshot: &Snapshot,
) -> Result<Plan, ExecutorError> {
    // Check for unsupported features
    if select.distinct {
        return Err(ExecutorError::Unsupported("DISTINCT".to_string()));
    }
    if !select.group_by.is_empty() {
        return Err(ExecutorError::Unsupported("GROUP BY".to_string()));
    }
    if select.having.is_some() {
        return Err(ExecutorError::Unsupported("HAVING".to_string()));
    }
    if !select.order_by.is_empty() {
        return Err(ExecutorError::Unsupported("ORDER BY".to_string()));
    }
    if select.limit.is_some() {
        return Err(ExecutorError::Unsupported("LIMIT".to_string()));
    }
    if select.offset.is_some() {
        return Err(ExecutorError::Unsupported("OFFSET".to_string()));
    }
    if select.locking.is_some() {
        return Err(ExecutorError::Unsupported("FOR UPDATE/SHARE".to_string()));
    }

    // Step 1: FROM clause -> base plan
    let mut plan = match &select.from {
        Some(from) => build_from_plan(from, catalog, snapshot).await?,
        None => Plan::ValuesScan,
    };

    // Step 2: WHERE clause -> Filter (bind column names to indices)
    if let Some(where_clause) = &select.where_clause {
        let columns = plan.columns().to_vec();
        let bound_predicate = where_clause.bind(&columns)?;
        plan = Plan::Filter {
            input: Box::new(plan),
            predicate: bound_predicate,
        };
    }

    // Step 3: SELECT list -> Projection
    plan = build_projection_plan(plan, &select.columns)?;

    Ok(plan)
}

/// Builds a plan from a FROM clause.
async fn build_from_plan<S: Storage, R: Replacer>(
    from: &FromClause,
    catalog: &Catalog<S, R>,
    snapshot: &Snapshot,
) -> Result<Plan, ExecutorError> {
    if from.tables.len() != 1 {
        return Err(ExecutorError::Unsupported(
            "multiple tables in FROM (use JOIN)".to_string(),
        ));
    }
    build_table_ref_plan(&from.tables[0], catalog, snapshot).await
}

/// Builds a plan from a table reference.
async fn build_table_ref_plan<S: Storage, R: Replacer>(
    table_ref: &TableRef,
    catalog: &Catalog<S, R>,
    snapshot: &Snapshot,
) -> Result<Plan, ExecutorError> {
    match table_ref {
        TableRef::Table { name, alias } => {
            build_seq_scan_plan(name, alias.as_deref(), catalog, snapshot).await
        }
        TableRef::Join { .. } => Err(ExecutorError::Unsupported("JOIN".to_string())),
        TableRef::Subquery { .. } => {
            Err(ExecutorError::Unsupported("subquery in FROM".to_string()))
        }
    }
}

/// Builds a SeqScan plan by looking up the table in the catalog.
///
/// When `alias` is provided, it is used as the column source table name
/// so that qualified references like `t.id` resolve correctly.
async fn build_seq_scan_plan<S: Storage, R: Replacer>(
    table_name: &str,
    alias: Option<&str>,
    catalog: &Catalog<S, R>,
    snapshot: &Snapshot,
) -> Result<Plan, ExecutorError> {
    // Look up table in catalog
    let table_info = catalog
        .get_table(snapshot, table_name)
        .await?
        .ok_or_else(|| ExecutorError::TableNotFound {
            name: table_name.to_string(),
        })?;

    // Get column metadata
    let column_infos = catalog.get_columns(snapshot, table_info.table_id).await?;

    // Build schema (column types) for record deserialization
    let schema: Vec<Type> = column_infos.iter().map(|c| c.ty).collect();

    // Build column descriptors — use alias for column resolution if provided
    let resolve_name = alias.unwrap_or(table_name);
    let columns = build_column_descs(&column_infos, table_info.table_id, resolve_name);

    Ok(Plan::SeqScan {
        table_name: table_name.to_string(),
        table_id: table_info.table_id,
        first_page: table_info.first_page,
        schema,
        columns,
    })
}

/// Builds column descriptors from catalog column info.
fn build_column_descs(
    column_infos: &[ColumnInfo],
    table_id: u32,
    table_name: &str,
) -> Vec<ColumnDesc> {
    column_infos
        .iter()
        .enumerate()
        .map(|(i, col)| ColumnDesc {
            name: col.column_name.clone(),
            source: Some(ColumnSource {
                table_name: table_name.to_string(),
                table_oid: table_id,
                column_id: (i + 1) as i16,
            }),
            ty: col.ty,
        })
        .collect()
}

/// Builds a Projection plan from the SELECT list.
fn build_projection_plan(input: Plan, select_items: &[SelectItem]) -> Result<Plan, ExecutorError> {
    let input_columns = input.columns().to_vec();
    let mut exprs = Vec::new();
    let mut columns = Vec::new();

    for item in select_items {
        for (expr, desc) in resolve_select_item(item, &input_columns)? {
            exprs.push(expr);
            columns.push(desc);
        }
    }

    Ok(Plan::Projection {
        input: Box::new(input),
        exprs,
        columns,
    })
}

/// Resolves a single [`SelectItem`] into `(BoundExpr, ColumnDesc)` pairs.
///
/// Wildcards expand to all input columns; expressions produce a single pair.
fn resolve_select_item(
    item: &SelectItem,
    input_columns: &[ColumnDesc],
) -> Result<Vec<(BoundExpr, ColumnDesc)>, ExecutorError> {
    match item {
        SelectItem::Wildcard => Ok(expand_columns(input_columns, None)),
        SelectItem::QualifiedWildcard(table_name) => {
            let expanded = expand_columns(input_columns, Some(table_name));
            if expanded.is_empty() {
                return Err(ExecutorError::TableNotFound {
                    name: table_name.clone(),
                });
            }
            Ok(expanded)
        }
        SelectItem::Expr { expr, alias } => {
            let bound = expr.bind(input_columns)?;
            let desc = infer_column_desc(expr, alias.as_deref(), input_columns);
            Ok(vec![(bound, desc)])
        }
    }
}

/// Expands input columns into `(BoundExpr::Column, ColumnDesc)` pairs.
///
/// When `table_name` is `Some`, only columns whose source table matches are
/// included. When `None`, all columns are expanded. The `BoundExpr::Column`
/// index always refers to the position in the full input schema so that
/// downstream evaluation resolves correctly.
fn expand_columns(
    input_columns: &[ColumnDesc],
    table_name: Option<&str>,
) -> Vec<(BoundExpr, ColumnDesc)> {
    input_columns
        .iter()
        .enumerate()
        .filter(|(_, col)| match table_name {
            Some(name) => col.source.as_ref().is_some_and(|s| s.table_name == name),
            None => true,
        })
        .map(|(i, col)| {
            let expr = BoundExpr::Column {
                index: i,
                name: Some(col.name.clone()),
            };
            (expr, col.clone())
        })
        .collect()
}

/// Infers the output [`ColumnDesc`] for an expression.
///
/// For column references, looks up the full metadata (including source table info)
/// from the input columns. For other expressions, infers name and type heuristically
/// with no source table info.
fn infer_column_desc(expr: &Expr, alias: Option<&str>, input_columns: &[ColumnDesc]) -> ColumnDesc {
    let mut desc = match expr {
        Expr::ColumnRef { table, column } => {
            match resolve_column_index(table.as_deref(), column, input_columns) {
                Ok(i) => input_columns[i].clone(),
                Err(_) => ColumnDesc {
                    name: column.clone(),
                    source: None,
                    ty: Type::Text,
                },
            }
        }
        Expr::Function { name, .. } => ColumnDesc {
            name: name.clone(),
            source: None,
            ty: infer_type(expr, input_columns),
        },
        Expr::Cast { data_type, .. } => ColumnDesc {
            name: data_type.display_name().to_lowercase(),
            source: None,
            ty: infer_type(expr, input_columns),
        },
        _ => ColumnDesc {
            name: "?column?".to_string(),
            source: None,
            ty: infer_type(expr, input_columns),
        },
    };

    if let Some(alias) = alias {
        desc.name = alias.to_string();
    }

    desc
}

/// Infers the output type from an expression.
///
/// For column references, uses the known column type. For other expressions,
/// uses a heuristic based on the expression kind. The actual type will be
/// determined at evaluation time and may differ.
fn infer_type(expr: &Expr, columns: &[ColumnDesc]) -> Type {
    match expr {
        Expr::ColumnRef { table, column } => {
            match resolve_column_index(table.as_deref(), column, columns) {
                Ok(i) => columns[i].ty,
                Err(_) => Type::Text,
            }
        }
        Expr::Integer(_) => Type::Bigint,
        Expr::Float(_) => Type::DoublePrecision,
        Expr::Boolean(_) => Type::Bool,
        Expr::String(_) => Type::Text,
        Expr::Null => Type::Text,
        Expr::BinaryOp { op, left, .. } => match op {
            crate::sql::BinaryOperator::Eq
            | crate::sql::BinaryOperator::Neq
            | crate::sql::BinaryOperator::Lt
            | crate::sql::BinaryOperator::LtEq
            | crate::sql::BinaryOperator::Gt
            | crate::sql::BinaryOperator::GtEq
            | crate::sql::BinaryOperator::And
            | crate::sql::BinaryOperator::Or => Type::Bool,
            crate::sql::BinaryOperator::Concat => Type::Text,
            _ => infer_type(left, columns),
        },
        Expr::UnaryOp { operand, .. } => infer_type(operand, columns),
        Expr::IsNull { .. } | Expr::InList { .. } | Expr::Between { .. } | Expr::Like { .. } => {
            Type::Bool
        }
        Expr::Cast { data_type, .. } => data_type.to_type(),
        // NOTE: Unrecognized expressions fall back to Text, similar to PostgreSQL's
        // "unknown" type. This may cause issues in Step 11 (DML) where INSERT needs
        // accurate type inference for literal values to match target column types.
        _ => Type::Text,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    use crate::db::Database;
    use crate::sql::{Parser, Statement};
    use crate::storage::MemoryStorage;
    use crate::tx::CommandId;

    async fn setup_test_db() -> (
        Arc<Database<MemoryStorage, crate::storage::LruReplacer>>,
        Snapshot,
    ) {
        let storage = MemoryStorage::new();
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        (db, snapshot)
    }

    fn parse_select(sql: &str) -> SelectStmt {
        let stmt = Parser::new(sql).parse().unwrap().unwrap();
        let Statement::Select(select) = stmt else {
            panic!("expected SELECT statement");
        };
        *select
    }

    #[tokio::test]
    async fn test_plan_select_from_sys_tables() {
        let (db, snapshot) = setup_test_db().await;
        let select = parse_select("SELECT * FROM sys_tables");

        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();

        assert_eq!(plan.columns().len(), 3);
        assert_eq!(plan.columns()[0].name, "table_id");
        assert_eq!(plan.columns()[1].name, "table_name");
        assert_eq!(plan.columns()[2].name, "first_page");
    }

    #[tokio::test]
    async fn test_plan_select_no_from() {
        let (db, snapshot) = setup_test_db().await;
        let select = parse_select("SELECT 42");

        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();

        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].name, "?column?");
    }

    #[tokio::test]
    async fn test_plan_select_table_not_found() {
        let (db, snapshot) = setup_test_db().await;
        let select = parse_select("SELECT * FROM nonexistent");

        let result = plan_select(&select, db.catalog(), &snapshot).await;
        assert!(matches!(result, Err(ExecutorError::TableNotFound { .. })));
    }

    #[tokio::test]
    async fn test_plan_select_with_where() {
        let (db, snapshot) = setup_test_db().await;
        let select = parse_select("SELECT table_name FROM sys_tables WHERE table_id = 1");

        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();

        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].name, "table_name");
        let source = plan.columns()[0]
            .source
            .as_ref()
            .expect("should have source");
        assert_eq!(source.table_name, "sys_tables");
        assert_ne!(source.table_oid, 0);
        assert_ne!(source.column_id, 0);
    }

    #[tokio::test]
    async fn test_plan_select_expr_has_no_table_metadata() {
        let (db, snapshot) = setup_test_db().await;
        let select = parse_select("SELECT 1 + table_id FROM sys_tables");

        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();

        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].name, "?column?");
        assert!(plan.columns()[0].source.is_none());
    }

    #[tokio::test]
    async fn test_plan_select_qualified_column_ref() {
        let (db, snapshot) = setup_test_db().await;
        let select = parse_select("SELECT sys_tables.table_name FROM sys_tables");

        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();

        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].name, "table_name");
        let source = plan.columns()[0]
            .source
            .as_ref()
            .expect("should have source");
        assert_eq!(source.table_name, "sys_tables");
        assert_ne!(source.table_oid, 0);
        assert_ne!(source.column_id, 0);
    }

    #[tokio::test]
    async fn test_plan_select_qualified_wildcard() {
        let (db, snapshot) = setup_test_db().await;
        let select = parse_select("SELECT sys_tables.* FROM sys_tables");

        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();

        assert_eq!(plan.columns().len(), 3);
        assert_eq!(plan.columns()[0].name, "table_id");
        assert_eq!(plan.columns()[1].name, "table_name");
        assert_eq!(plan.columns()[2].name, "first_page");
    }

    #[tokio::test]
    async fn test_plan_select_qualified_wildcard_wrong_table() {
        let (db, snapshot) = setup_test_db().await;
        let select = parse_select("SELECT nonexistent.* FROM sys_tables");

        let result = plan_select(&select, db.catalog(), &snapshot).await;
        assert!(matches!(result, Err(ExecutorError::TableNotFound { .. })));
    }

    #[tokio::test]
    async fn test_plan_select_with_table_alias() {
        let (db, snapshot) = setup_test_db().await;
        let select = parse_select("SELECT t.table_name FROM sys_tables AS t");

        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();

        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].name, "table_name");
        let source = plan.columns()[0]
            .source
            .as_ref()
            .expect("should have source");
        assert_eq!(source.table_name, "t");
    }

    #[tokio::test]
    async fn test_plan_select_alias_hides_original_name() {
        let (db, snapshot) = setup_test_db().await;
        let select = parse_select("SELECT sys_tables.table_name FROM sys_tables AS t");

        let result = plan_select(&select, db.catalog(), &snapshot).await;
        assert!(matches!(result, Err(ExecutorError::ColumnNotFound { .. })));
    }

    #[tokio::test]
    async fn test_infer_data_type_literals() {
        let (db, snapshot) = setup_test_db().await;

        // Integer literal → bigint
        let select = parse_select("SELECT 42");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bigint);

        // Float literal → DoublePrecision
        let select = parse_select("SELECT 3.14");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::DoublePrecision);

        // Boolean literal → Bool
        let select = parse_select("SELECT TRUE");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bool);

        // String literal → Text
        let select = parse_select("SELECT 'hello'");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Text);

        // NULL → Text (fallback)
        let select = parse_select("SELECT NULL");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Text);
    }

    #[tokio::test]
    async fn test_infer_data_type_operators() {
        let (db, snapshot) = setup_test_db().await;

        // Comparison → Bool
        let select = parse_select("SELECT 1 = 1");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bool);

        // Arithmetic → inherits left operand type (Bigint)
        let select = parse_select("SELECT 1 + 2");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bigint);

        // Concatenation → Text
        let select = parse_select("SELECT 'a' || 'b'");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Text);

        // IS NULL → Bool
        let select = parse_select("SELECT 1 IS NULL");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bool);

        // IN list → Bool
        let select = parse_select("SELECT 1 IN (1, 2)");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bool);

        // BETWEEN → Bool
        let select = parse_select("SELECT 1 BETWEEN 0 AND 2");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bool);

        // LIKE → Bool
        let select = parse_select("SELECT 'a' LIKE '%'");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bool);

        // CAST → target type
        let select = parse_select("SELECT CAST(1 AS TEXT)");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Text);

        // Unary minus → inherits operand type
        let select = parse_select("SELECT -42");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bigint);
    }

    #[tokio::test]
    async fn test_infer_data_type_column_ref() {
        let (db, snapshot) = setup_test_db().await;

        // Column reference preserves source type
        let select = parse_select("SELECT table_id FROM sys_tables");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Integer);

        let select = parse_select("SELECT table_name FROM sys_tables");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Text);
    }

    #[tokio::test]
    async fn test_plan_select_alias_qualified_wildcard() {
        let (db, snapshot) = setup_test_db().await;
        let select = parse_select("SELECT t.* FROM sys_tables AS t");

        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();

        assert_eq!(plan.columns().len(), 3);
        assert_eq!(plan.columns()[0].name, "table_id");
    }
}
