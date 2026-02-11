//! Query planner.

use std::collections::HashSet;

use crate::catalog::{Catalog, ColumnInfo};
use crate::datum::Type;
use crate::sql::{
    BinaryOperator, DeleteStmt, Expr, FromClause, InsertStmt, SelectItem, SelectStmt, TableRef,
    UpdateStmt,
};
use crate::storage::{Replacer, Storage};
use crate::tx::Snapshot;

use super::error::ExecutorError;
use super::expr::{BoundExpr, resolve_column_index};
use super::plan::{DmlPlan, QueryPlan};
use super::{ColumnDesc, ColumnSource};

/// Plans a SELECT statement into a logical [`QueryPlan`] tree.
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
) -> Result<QueryPlan, ExecutorError> {
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
        None => QueryPlan::ValuesScan,
    };

    // Step 2: WHERE clause -> Filter (bind column names to indices)
    if let Some(where_clause) = &select.where_clause {
        let columns = plan.columns().to_vec();
        let bound_predicate = where_clause.bind(&columns)?;
        plan = QueryPlan::Filter {
            input: Box::new(plan),
            predicate: bound_predicate,
        };
    }

    // Step 3: SELECT list -> Projection
    plan = build_projection_plan(plan, &select.columns)?;

    Ok(plan)
}

/// Plans an INSERT statement into a logical [`DmlPlan::Insert`].
///
/// Resolves column names to positions, handles SERIAL auto-population,
/// binds value expressions, and applies type coercion to match target
/// column types.
///
/// # Arguments
///
/// * `insert` - The parsed INSERT statement
/// * `catalog` - Catalog for table/column metadata access
/// * `snapshot` - MVCC snapshot for catalog visibility checks
///
/// # Errors
///
/// Returns [`ExecutorError`] for unknown tables/columns, column count
/// mismatches, duplicate columns, or type coercion failures.
pub async fn plan_insert<S: Storage, R: Replacer>(
    insert: &InsertStmt,
    catalog: &Catalog<S, R>,
    snapshot: &Snapshot,
) -> Result<DmlPlan, ExecutorError> {
    // Look up the target table
    let table_info = catalog
        .get_table(snapshot, &insert.table)
        .await?
        .ok_or_else(|| ExecutorError::TableNotFound {
            name: insert.table.clone(),
        })?;

    let column_infos = catalog.get_columns(snapshot, table_info.table_id).await?;
    let column_count = column_infos.len();

    // Determine the column mapping: which table column each value expression maps to.
    // If no column list is specified, values map 1:1 to table columns.
    let column_mapping = if insert.columns.is_empty() {
        // No column list: values must match table column count
        (0..column_count).collect::<Vec<_>>()
    } else {
        resolve_insert_columns(&insert.columns, &column_infos)?
    };

    // Identify SERIAL columns for auto-population
    let serial_columns: Vec<(usize, u32)> = column_infos
        .iter()
        .enumerate()
        .filter(|(_, col)| col.is_serial())
        .map(|(i, col)| (i, col.seq_id))
        .collect();

    // Columns explicitly provided by the user
    let provided_columns: HashSet<usize> = column_mapping.iter().copied().collect();

    // Build schema (column types) for type coercion
    let schema: Vec<Type> = column_infos.iter().map(|c| c.ty).collect();

    // Bind each row of values
    let mut bound_rows = Vec::with_capacity(insert.values.len());
    for row_exprs in &insert.values {
        if row_exprs.len() != column_mapping.len() {
            return Err(ExecutorError::ColumnCountMismatch {
                expected: column_mapping.len(),
                found: row_exprs.len(),
            });
        }

        // Start with NULL for all columns
        let mut bound_row = vec![BoundExpr::Null; column_count];

        // Fill in provided values with type coercion
        // NOTE: VALUES expressions are bound with an empty column list because
        // they cannot reference table columns. Column refs in VALUES would
        // produce ColumnNotFound. INSERT ... SELECT (which needs column
        // resolution) would require a different binding approach.
        for (expr_idx, &col_idx) in column_mapping.iter().enumerate() {
            let bound = row_exprs[expr_idx].bind(&[])?;
            let target_type = schema[col_idx];
            let coerced = coerce_expr(bound, target_type);
            bound_row[col_idx] = coerced;
        }

        // SERIAL columns that were not explicitly provided remain as Null —
        // the executor will call nextval for these.

        bound_rows.push(bound_row);
    }

    Ok(DmlPlan::Insert {
        table_name: insert.table.clone(),
        table_id: table_info.table_id,
        first_page: table_info.first_page,
        schema,
        values: bound_rows,
        serial_columns: serial_columns
            .into_iter()
            .filter(|(i, _)| !provided_columns.contains(i))
            .collect(),
    })
}

/// Plans an UPDATE statement into a logical [`DmlPlan::Update`].
///
/// Builds a SeqScan (with optional Filter for WHERE), resolves SET assignment
/// column names, binds value expressions against the scan schema, and applies
/// type coercion for target column types.
///
/// # Errors
///
/// Returns [`ExecutorError`] for unknown tables/columns, or expression binding
/// errors.
pub async fn plan_update<S: Storage, R: Replacer>(
    update: &UpdateStmt,
    catalog: &Catalog<S, R>,
    snapshot: &Snapshot,
) -> Result<DmlPlan, ExecutorError> {
    // Build the input scan plan
    let scan_plan = build_seq_scan_plan(&update.table, None, catalog, snapshot).await?;

    // Wrap with Filter if WHERE clause exists
    let input = if let Some(where_clause) = &update.where_clause {
        let columns = scan_plan.columns().to_vec();
        let bound_predicate = where_clause.bind(&columns)?;
        QueryPlan::Filter {
            input: Box::new(scan_plan),
            predicate: bound_predicate,
        }
    } else {
        scan_plan
    };

    let input_columns = input.columns().to_vec();

    // Get column metadata for type coercion
    let table_info = catalog
        .get_table(snapshot, &update.table)
        .await?
        .ok_or_else(|| ExecutorError::TableNotFound {
            name: update.table.clone(),
        })?;
    let column_infos = catalog.get_columns(snapshot, table_info.table_id).await?;
    let schema: Vec<Type> = column_infos.iter().map(|c| c.ty).collect();

    // Build assignments: start with identity (preserve original values)
    let mut bound_assignments: Vec<BoundExpr> = (0..column_infos.len())
        .map(|i| BoundExpr::Column {
            index: i,
            name: Some(column_infos[i].column_name.clone()),
        })
        .collect();

    // Apply SET assignments
    for assignment in &update.assignments {
        let col_idx = column_infos
            .iter()
            .position(|c| c.column_name.to_lowercase() == assignment.column.to_lowercase())
            .ok_or_else(|| ExecutorError::ColumnNotFound {
                name: assignment.column.clone(),
            })?;

        let bound = assignment.value.bind(&input_columns)?;
        let target_type = schema[col_idx];
        bound_assignments[col_idx] = coerce_expr(bound, target_type);
    }

    Ok(DmlPlan::Update {
        table_name: update.table.clone(),
        input: Box::new(input),
        assignments: bound_assignments,
        schema,
        first_page: table_info.first_page,
    })
}

/// Plans a DELETE statement into a logical [`DmlPlan::Delete`].
///
/// Builds a SeqScan (with optional Filter for WHERE) as the input plan.
///
/// # Errors
///
/// Returns [`ExecutorError`] for unknown tables or expression binding errors.
pub async fn plan_delete<S: Storage, R: Replacer>(
    delete: &DeleteStmt,
    catalog: &Catalog<S, R>,
    snapshot: &Snapshot,
) -> Result<DmlPlan, ExecutorError> {
    // Build the input scan plan
    let scan_plan = build_seq_scan_plan(&delete.table, None, catalog, snapshot).await?;

    // Wrap with Filter if WHERE clause exists
    let input = if let Some(where_clause) = &delete.where_clause {
        let columns = scan_plan.columns().to_vec();
        let bound_predicate = where_clause.bind(&columns)?;
        QueryPlan::Filter {
            input: Box::new(scan_plan),
            predicate: bound_predicate,
        }
    } else {
        scan_plan
    };

    Ok(DmlPlan::Delete {
        table_name: delete.table.clone(),
        input: Box::new(input),
    })
}

/// Resolves column names from an INSERT column list to table column indices.
///
/// Returns a Vec of table column indices in the order specified by the user.
/// Validates that all column names exist and no column is specified more than once.
fn resolve_insert_columns(
    column_names: &[String],
    column_infos: &[ColumnInfo],
) -> Result<Vec<usize>, ExecutorError> {
    let mut seen = HashSet::new();
    let mut mapping = Vec::with_capacity(column_names.len());

    for name in column_names {
        let lower = name.to_lowercase();
        if !seen.insert(lower.clone()) {
            return Err(ExecutorError::DuplicateColumn { name: name.clone() });
        }

        let col_idx = column_infos
            .iter()
            .position(|c| c.column_name.to_lowercase() == lower)
            .ok_or_else(|| ExecutorError::ColumnNotFound { name: name.clone() })?;

        mapping.push(col_idx);
    }

    Ok(mapping)
}

/// Wraps a bound expression in a cast if the expression's type doesn't match
/// the target column type.
///
/// For literal values, this inserts a `BoundExpr::Cast` node so that runtime
/// evaluation will apply the conversion. NULL values pass through without casting.
fn coerce_expr(expr: BoundExpr, target_type: Type) -> BoundExpr {
    // NULL doesn't need coercion
    if matches!(&expr, BoundExpr::Null) {
        return expr;
    }

    // If the expression already has a cast to the right type, no additional wrapping needed
    if let BoundExpr::Cast { ref ty, .. } = expr
        && *ty == target_type
    {
        return expr;
    }

    // Infer the expression type — if it matches target, no cast needed
    if let Some(et) = infer_bound_expr_type(&expr)
        && et == target_type
    {
        return expr;
    }

    BoundExpr::Cast {
        expr: Box::new(expr),
        ty: target_type,
    }
}

/// Infers the type of a bound expression.
fn infer_bound_expr_type(expr: &BoundExpr) -> Option<Type> {
    match expr {
        BoundExpr::Integer(_) => Some(Type::Bigint),
        BoundExpr::Float(_) => Some(Type::Double),
        BoundExpr::Boolean(_) => Some(Type::Bool),
        BoundExpr::String(_) => Some(Type::Text),
        BoundExpr::Cast { ty, .. } => Some(*ty),
        _ => None,
    }
}

/// Builds a plan from a FROM clause.
async fn build_from_plan<S: Storage, R: Replacer>(
    from: &FromClause,
    catalog: &Catalog<S, R>,
    snapshot: &Snapshot,
) -> Result<QueryPlan, ExecutorError> {
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
) -> Result<QueryPlan, ExecutorError> {
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
) -> Result<QueryPlan, ExecutorError> {
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

    Ok(QueryPlan::SeqScan {
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
fn build_projection_plan(
    input: QueryPlan,
    select_items: &[SelectItem],
) -> Result<QueryPlan, ExecutorError> {
    let input_columns = input.columns().to_vec();
    let mut exprs = Vec::new();
    let mut columns = Vec::new();

    for item in select_items {
        for (expr, desc) in resolve_select_item(item, &input_columns)? {
            exprs.push(expr);
            columns.push(desc);
        }
    }

    Ok(QueryPlan::Projection {
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
/// For column references, uses the known column type. For arithmetic
/// operations, applies [`numeric_promotion`] to both operands so that the
/// inferred type matches the runtime evaluation result.
fn infer_type(expr: &Expr, columns: &[ColumnDesc]) -> Type {
    match expr {
        Expr::ColumnRef { table, column } => {
            match resolve_column_index(table.as_deref(), column, columns) {
                Ok(i) => columns[i].ty,
                Err(_) => Type::Text,
            }
        }
        Expr::Integer(_) => Type::Bigint,
        Expr::Float(_) => Type::Double,
        Expr::Boolean(_) => Type::Bool,
        Expr::String(_) => Type::Text,
        Expr::Null => Type::Text,
        Expr::BinaryOp { op, left, right } => match op {
            BinaryOperator::Eq
            | BinaryOperator::Neq
            | BinaryOperator::Lt
            | BinaryOperator::LtEq
            | BinaryOperator::Gt
            | BinaryOperator::GtEq
            | BinaryOperator::And
            | BinaryOperator::Or => Type::Bool,
            BinaryOperator::Concat => Type::Text,
            BinaryOperator::Add
            | BinaryOperator::Sub
            | BinaryOperator::Mul
            | BinaryOperator::Div
            | BinaryOperator::Mod => {
                infer_arithmetic_type(infer_type(left, columns), infer_type(right, columns))
            }
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

fn infer_arithmetic_type(left: Type, right: Type) -> Type {
    let (Some(left), Some(right)) = (left.to_wide_numeric(), right.to_wide_numeric()) else {
        // Non-numeric operand: keep the inferred type and let eval report the error.
        return left;
    };
    match (left, right) {
        (Type::Bigint, Type::Bigint) => Type::Bigint,
        _ => Type::Double,
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

        // Float literal → Double
        let select = parse_select("SELECT 3.14");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Double);

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

        // Arithmetic (int + int) → Bigint
        let select = parse_select("SELECT 1 + 2");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bigint);

        // Arithmetic (int + float) → Double via numeric promotion
        let select = parse_select("SELECT 1 + 2.5");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Double);

        // Arithmetic (float + int) → Double via numeric promotion
        let select = parse_select("SELECT 2.5 + 1");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Double);

        // Arithmetic (float + float) → Double
        let select = parse_select("SELECT 1.0 * 2.5");
        let plan = plan_select(&select, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Double);

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

    // --- INSERT planner tests ---

    /// Sets up a database with a user-defined table for INSERT tests.
    async fn setup_db_with_table(
        ddl: &str,
    ) -> (
        Arc<Database<MemoryStorage, crate::storage::LruReplacer>>,
        Snapshot,
    ) {
        let storage = MemoryStorage::new();
        let db = Arc::new(Database::open(storage, 100).await.unwrap());

        let txid = db.tx_manager().begin();
        let stmt = Parser::new(ddl).parse().unwrap().unwrap();
        let Statement::CreateTable(create_stmt) = stmt else {
            panic!("expected CREATE TABLE");
        };
        db.catalog()
            .create_table(txid, CommandId::FIRST, &create_stmt)
            .await
            .unwrap();
        db.tx_manager().commit(txid).unwrap();

        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        (db, snapshot)
    }

    fn parse_insert(sql: &str) -> InsertStmt {
        let stmt = Parser::new(sql).parse().unwrap().unwrap();
        let Statement::Insert(insert) = stmt else {
            panic!("expected INSERT statement");
        };
        *insert
    }

    #[tokio::test]
    async fn test_plan_insert_basic() {
        let (db, snapshot) =
            setup_db_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let insert = parse_insert("INSERT INTO users VALUES (1, 'Alice')");

        let plan = plan_insert(&insert, db.catalog(), &snapshot).await.unwrap();

        let DmlPlan::Insert {
            table_name,
            values,
            schema,
            serial_columns,
            ..
        } = &plan
        else {
            panic!("expected DmlPlan::Insert");
        };
        assert_eq!(table_name, "users");
        assert_eq!(values.len(), 1);
        assert_eq!(values[0].len(), 2);
        assert_eq!(schema, &[Type::Integer, Type::Text]);
        assert!(serial_columns.is_empty());
    }

    #[tokio::test]
    async fn test_plan_insert_with_column_list() {
        let (db, snapshot) =
            setup_db_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let insert = parse_insert("INSERT INTO users (name, id) VALUES ('Bob', 2)");

        let plan = plan_insert(&insert, db.catalog(), &snapshot).await.unwrap();

        let DmlPlan::Insert { values, schema, .. } = &plan else {
            panic!("expected DmlPlan::Insert");
        };
        assert_eq!(schema.len(), 2);
        assert_eq!(values.len(), 1);
        // Value at index 0 (id) should be integer 2 cast to Integer
        // (Bigint literal → Integer column)
        let BoundExpr::Cast { ty, .. } = &values[0][0] else {
            panic!("expected Cast for id column, got {:?}", &values[0][0]);
        };
        assert_eq!(*ty, Type::Integer);
        // Value at index 1 (name) should be the string 'Bob' (no cast needed, Text→Text)
        assert!(matches!(&values[0][1], BoundExpr::String(s) if s == "Bob"));
    }

    #[tokio::test]
    async fn test_plan_insert_fewer_columns() {
        let (db, snapshot) =
            setup_db_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        // Only specify id, name should default to NULL
        let insert = parse_insert("INSERT INTO users (id) VALUES (1)");

        let plan = plan_insert(&insert, db.catalog(), &snapshot).await.unwrap();

        let DmlPlan::Insert { values, .. } = &plan else {
            panic!("expected DmlPlan::Insert");
        };
        assert_eq!(values[0].len(), 2);
        // name column (index 1) should be NULL
        assert!(matches!(&values[0][1], BoundExpr::Null));
    }

    #[tokio::test]
    async fn test_plan_insert_serial_auto_populate() {
        let (db, snapshot) = setup_db_with_table("CREATE TABLE users (id SERIAL, name TEXT)").await;
        // Don't specify id — should be auto-populated
        let insert = parse_insert("INSERT INTO users (name) VALUES ('Alice')");

        let plan = plan_insert(&insert, db.catalog(), &snapshot).await.unwrap();

        let DmlPlan::Insert {
            serial_columns,
            values,
            ..
        } = &plan
        else {
            panic!("expected DmlPlan::Insert");
        };
        // SERIAL column should be in the auto-populate list
        assert_eq!(serial_columns.len(), 1);
        assert_eq!(serial_columns[0].0, 0); // column index 0 (id)
        assert!(serial_columns[0].1 > 0); // non-zero seq_id
        // id column should be NULL (to be replaced by nextval at execution)
        assert!(matches!(&values[0][0], BoundExpr::Null));
    }

    #[tokio::test]
    async fn test_plan_insert_serial_explicit_value() {
        let (db, snapshot) = setup_db_with_table("CREATE TABLE users (id SERIAL, name TEXT)").await;
        // Explicitly provide id — should NOT auto-populate
        let insert = parse_insert("INSERT INTO users (id, name) VALUES (99, 'Bob')");

        let plan = plan_insert(&insert, db.catalog(), &snapshot).await.unwrap();

        let DmlPlan::Insert { serial_columns, .. } = &plan else {
            panic!("expected DmlPlan::Insert");
        };
        // SERIAL column explicitly provided → not in auto-populate list
        assert!(serial_columns.is_empty());
    }

    #[tokio::test]
    async fn test_plan_insert_column_count_mismatch() {
        let (db, snapshot) =
            setup_db_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        // 3 values but only 2 columns
        let insert = parse_insert("INSERT INTO users VALUES (1, 'Alice', 'extra')");

        let result = plan_insert(&insert, db.catalog(), &snapshot).await;
        assert!(matches!(
            result,
            Err(ExecutorError::ColumnCountMismatch {
                expected: 2,
                found: 3
            })
        ));
    }

    #[tokio::test]
    async fn test_plan_insert_duplicate_column() {
        let (db, snapshot) =
            setup_db_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let insert = parse_insert("INSERT INTO users (id, id) VALUES (1, 2)");

        let result = plan_insert(&insert, db.catalog(), &snapshot).await;
        assert!(matches!(result, Err(ExecutorError::DuplicateColumn { .. })));
    }

    #[tokio::test]
    async fn test_plan_insert_column_not_found() {
        let (db, snapshot) =
            setup_db_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let insert = parse_insert("INSERT INTO users (id, nonexistent) VALUES (1, 'x')");

        let result = plan_insert(&insert, db.catalog(), &snapshot).await;
        assert!(matches!(result, Err(ExecutorError::ColumnNotFound { .. })));
    }

    #[tokio::test]
    async fn test_plan_insert_table_not_found() {
        let (db, snapshot) = setup_test_db().await;
        let insert = parse_insert("INSERT INTO nonexistent VALUES (1)");

        let result = plan_insert(&insert, db.catalog(), &snapshot).await;
        assert!(matches!(result, Err(ExecutorError::TableNotFound { .. })));
    }

    #[tokio::test]
    async fn test_plan_insert_type_coercion() {
        let (db, snapshot) = setup_db_with_table("CREATE TABLE t (val SMALLINT)").await;
        // Integer literal 42 (Bigint) → should be coerced to Smallint
        let insert = parse_insert("INSERT INTO t VALUES (42)");

        let plan = plan_insert(&insert, db.catalog(), &snapshot).await.unwrap();

        let DmlPlan::Insert { values, .. } = &plan else {
            panic!("expected DmlPlan::Insert");
        };
        // Should have a Cast wrapping the integer literal
        let BoundExpr::Cast { ty, .. } = &values[0][0] else {
            panic!(
                "expected Cast expression for type coercion, got {:?}",
                &values[0][0]
            );
        };
        assert_eq!(*ty, Type::Smallint);
    }

    #[tokio::test]
    async fn test_plan_insert_multi_row() {
        let (db, snapshot) =
            setup_db_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let insert =
            parse_insert("INSERT INTO users VALUES (1, 'Alice'), (2, 'Bob'), (3, 'Carol')");

        let plan = plan_insert(&insert, db.catalog(), &snapshot).await.unwrap();

        let DmlPlan::Insert { values, .. } = &plan else {
            panic!("expected DmlPlan::Insert");
        };
        assert_eq!(values.len(), 3);
    }

    #[tokio::test]
    async fn test_plan_insert_null_no_cast() {
        let (db, snapshot) = setup_db_with_table("CREATE TABLE t (val INTEGER)").await;
        // NULL should pass through without a Cast wrapper
        let insert = parse_insert("INSERT INTO t VALUES (NULL)");

        let plan = plan_insert(&insert, db.catalog(), &snapshot).await.unwrap();

        let DmlPlan::Insert { values, .. } = &plan else {
            panic!("expected DmlPlan::Insert");
        };
        assert!(matches!(&values[0][0], BoundExpr::Null));
    }

    #[tokio::test]
    async fn test_plan_insert_explain() {
        let (db, snapshot) =
            setup_db_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let insert = parse_insert("INSERT INTO users VALUES (1, 'Alice'), (2, 'Bob')");

        let plan = plan_insert(&insert, db.catalog(), &snapshot).await.unwrap();
        assert_eq!(plan.explain(), "Insert on users (2 rows)");
    }

    // --- UPDATE planner tests ---

    fn parse_update(sql: &str) -> UpdateStmt {
        let stmt = Parser::new(sql).parse().unwrap().unwrap();
        let Statement::Update(update) = stmt else {
            panic!("expected UPDATE statement");
        };
        *update
    }

    #[tokio::test]
    async fn test_plan_update_basic() {
        let (db, snapshot) =
            setup_db_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let update = parse_update("UPDATE users SET name = 'Bob'");

        let plan = plan_update(&update, db.catalog(), &snapshot).await.unwrap();

        let DmlPlan::Update {
            table_name,
            schema,
            assignments,
            ..
        } = &plan
        else {
            panic!("expected DmlPlan::Update");
        };
        assert_eq!(table_name, "users");
        assert_eq!(schema, &[Type::Integer, Type::Text]);
        assert_eq!(assignments.len(), 2);
        // id should be identity (Column { index: 0 })
        assert!(matches!(
            &assignments[0],
            BoundExpr::Column { index: 0, .. }
        ));
        // name should be the string literal 'Bob'
        assert!(matches!(&assignments[1], BoundExpr::String(s) if s == "Bob"));
    }

    #[tokio::test]
    async fn test_plan_update_with_where() {
        let (db, snapshot) =
            setup_db_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let update = parse_update("UPDATE users SET name = 'Bob' WHERE id = 1");

        let plan = plan_update(&update, db.catalog(), &snapshot).await.unwrap();

        let DmlPlan::Update { input, .. } = &plan else {
            panic!("expected DmlPlan::Update");
        };
        // Input should be a Filter wrapping a SeqScan
        assert!(matches!(input.as_ref(), QueryPlan::Filter { .. }));
        assert_eq!(
            plan.explain(),
            "Update on users\n  Filter: ($col0 (users.id) = 1)\n    SeqScan on users (cols: id, name)"
        );
    }

    #[tokio::test]
    async fn test_plan_update_type_coercion() {
        let (db, snapshot) = setup_db_with_table("CREATE TABLE t (val SMALLINT)").await;
        // Integer literal 42 (Bigint) → should be coerced to Smallint
        let update = parse_update("UPDATE t SET val = 42");

        let plan = plan_update(&update, db.catalog(), &snapshot).await.unwrap();

        let DmlPlan::Update { assignments, .. } = &plan else {
            panic!("expected DmlPlan::Update");
        };
        let BoundExpr::Cast { ty, .. } = &assignments[0] else {
            panic!("expected Cast for type coercion, got {:?}", &assignments[0]);
        };
        assert_eq!(*ty, Type::Smallint);
    }

    #[tokio::test]
    async fn test_plan_update_referencing_column() {
        let (db, snapshot) =
            setup_db_with_table("CREATE TABLE counters (id INTEGER, count INTEGER)").await;
        // SET count = count + 1 — references existing column
        let update = parse_update("UPDATE counters SET count = count + 1");

        let plan = plan_update(&update, db.catalog(), &snapshot).await.unwrap();

        let DmlPlan::Update { assignments, .. } = &plan else {
            panic!("expected DmlPlan::Update");
        };
        // id should be identity
        assert!(matches!(
            &assignments[0],
            BoundExpr::Column { index: 0, .. }
        ));
        // count should be a Cast(BinaryOp(Column + Integer)) since count+1 infers as Bigint
        // and target is Integer
        assert!(matches!(&assignments[1], BoundExpr::Cast { .. }));
    }

    #[tokio::test]
    async fn test_plan_update_column_not_found() {
        let (db, snapshot) =
            setup_db_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let update = parse_update("UPDATE users SET nonexistent = 1");

        let result = plan_update(&update, db.catalog(), &snapshot).await;
        assert!(matches!(result, Err(ExecutorError::ColumnNotFound { .. })));
    }

    #[tokio::test]
    async fn test_plan_update_table_not_found() {
        let (db, snapshot) = setup_test_db().await;
        let update = parse_update("UPDATE nonexistent SET x = 1");

        let result = plan_update(&update, db.catalog(), &snapshot).await;
        assert!(matches!(result, Err(ExecutorError::TableNotFound { .. })));
    }

    // --- DELETE planner tests ---

    fn parse_delete(sql: &str) -> DeleteStmt {
        let stmt = Parser::new(sql).parse().unwrap().unwrap();
        let Statement::Delete(delete) = stmt else {
            panic!("expected DELETE statement");
        };
        *delete
    }

    #[tokio::test]
    async fn test_plan_delete_basic() {
        let (db, snapshot) =
            setup_db_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let delete = parse_delete("DELETE FROM users");

        let plan = plan_delete(&delete, db.catalog(), &snapshot).await.unwrap();

        let DmlPlan::Delete {
            table_name, input, ..
        } = &plan
        else {
            panic!("expected DmlPlan::Delete");
        };
        assert_eq!(table_name, "users");
        // No WHERE → input is bare SeqScan
        assert!(matches!(input.as_ref(), QueryPlan::SeqScan { .. }));
    }

    #[tokio::test]
    async fn test_plan_delete_with_where() {
        let (db, snapshot) =
            setup_db_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let delete = parse_delete("DELETE FROM users WHERE id = 1");

        let plan = plan_delete(&delete, db.catalog(), &snapshot).await.unwrap();

        let DmlPlan::Delete { input, .. } = &plan else {
            panic!("expected DmlPlan::Delete");
        };
        assert!(matches!(input.as_ref(), QueryPlan::Filter { .. }));
        assert_eq!(
            plan.explain(),
            "Delete on users\n  Filter: ($col0 (users.id) = 1)\n    SeqScan on users (cols: id, name)"
        );
    }

    #[tokio::test]
    async fn test_plan_delete_table_not_found() {
        let (db, snapshot) = setup_test_db().await;
        let delete = parse_delete("DELETE FROM nonexistent");

        let result = plan_delete(&delete, db.catalog(), &snapshot).await;
        assert!(matches!(result, Err(ExecutorError::TableNotFound { .. })));
    }
}
