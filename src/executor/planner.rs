//! Query planner for SELECT statements.
//!
//! Transforms a parsed [`SelectStmt`] AST into a logical [`Plan`] tree
//! by resolving table references via the catalog and binding column names.

use crate::catalog::ColumnInfo;
use crate::datum::Type;
use crate::db::Database;
use crate::sql::{Expr, FromClause, SelectItem, SelectStmt, TableRef};
use crate::storage::{Replacer, Storage};
use crate::tx::Snapshot;

use super::ColumnDesc;
use super::error::ExecutorError;
use super::expr::{BoundExpr, resolve_column_index};
use super::plan::Plan;

/// Plans a SELECT statement into a logical [`Plan`] tree.
///
/// The planner resolves table references, binds column names to positional
/// indices, and constructs Filter/Projection plan nodes. No data is loaded
/// at this stage.
///
/// # Arguments
///
/// * `select` - The parsed SELECT statement
/// * `database` - Database for catalog access
/// * `snapshot` - MVCC snapshot for catalog visibility checks
///
/// # Errors
///
/// Returns [`ExecutorError`] for unresolvable tables/columns, unsupported
/// features (JOINs, subqueries), or catalog I/O errors.
pub async fn plan_select<S: Storage, R: Replacer>(
    select: &SelectStmt,
    database: &Database<S, R>,
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
        Some(from) => build_from_plan(from, database, snapshot).await?,
        None => Plan::ValuesScan,
    };

    // Step 2: WHERE clause -> Filter (bind column names to indices)
    if let Some(where_clause) = &select.where_clause {
        let columns = plan.columns().to_vec();
        let bound_predicate = BoundExpr::bind(where_clause, &columns)?;
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
    database: &Database<S, R>,
    snapshot: &Snapshot,
) -> Result<Plan, ExecutorError> {
    if from.tables.len() != 1 {
        return Err(ExecutorError::Unsupported(
            "multiple tables in FROM (use JOIN)".to_string(),
        ));
    }
    build_table_ref_plan(&from.tables[0], database, snapshot).await
}

/// Builds a plan from a table reference.
async fn build_table_ref_plan<S: Storage, R: Replacer>(
    table_ref: &TableRef,
    database: &Database<S, R>,
    snapshot: &Snapshot,
) -> Result<Plan, ExecutorError> {
    match table_ref {
        TableRef::Table { name, alias: _ } => build_seq_scan_plan(name, database, snapshot).await,
        TableRef::Join { .. } => Err(ExecutorError::Unsupported("JOIN".to_string())),
        TableRef::Subquery { .. } => {
            Err(ExecutorError::Unsupported("subquery in FROM".to_string()))
        }
    }
}

/// Builds a SeqScan plan by looking up the table in the catalog.
async fn build_seq_scan_plan<S: Storage, R: Replacer>(
    table_name: &str,
    database: &Database<S, R>,
    snapshot: &Snapshot,
) -> Result<Plan, ExecutorError> {
    // Look up table in catalog
    let table_info = database
        .catalog()
        .get_table(snapshot, table_name)
        .await?
        .ok_or_else(|| ExecutorError::TableNotFound {
            name: table_name.to_string(),
        })?;

    // Get column metadata
    let column_infos = database
        .catalog()
        .get_columns(snapshot, table_info.table_id)
        .await?;

    // Build schema (data types) for record deserialization
    let schema: Vec<Type> = column_infos.iter().map(|c| c.data_type).collect();

    // Build column descriptors
    let columns = build_column_descs(&column_infos, table_info.table_id, table_name);

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
            table_name: Some(table_name.to_string()),
            table_oid: table_id as i32,
            column_id: (i + 1) as i16,
            data_type: col.data_type,
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
        SelectItem::Wildcard => Ok(expand_all_columns(input_columns)),
        SelectItem::QualifiedWildcard(table_name) => {
            // NOTE: Currently expands all input columns regardless of table_name,
            // since only single-table queries are supported. JOINs would require
            // filtering by table_name here.
            let expanded = expand_all_columns(input_columns);
            if expanded.is_empty() {
                return Err(ExecutorError::TableNotFound {
                    name: table_name.clone(),
                });
            }
            Ok(expanded)
        }
        SelectItem::Expr { expr, alias } => {
            let bound = BoundExpr::bind(expr, input_columns)?;
            let desc = infer_column_desc(expr, alias.as_deref(), input_columns);
            Ok(vec![(bound, desc)])
        }
    }
}

/// Expands all input columns into `(BoundExpr::Column, ColumnDesc)` pairs.
fn expand_all_columns(input_columns: &[ColumnDesc]) -> Vec<(BoundExpr, ColumnDesc)> {
    input_columns
        .iter()
        .enumerate()
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
                    table_name: None,
                    table_oid: 0,
                    column_id: 0,
                    data_type: Type::Text,
                },
            }
        }
        Expr::Function { name, .. } => ColumnDesc {
            name: name.clone(),
            table_name: None,
            table_oid: 0,
            column_id: 0,
            data_type: infer_data_type(expr, input_columns),
        },
        Expr::Cast { data_type, .. } => ColumnDesc {
            name: data_type.display_name().to_lowercase(),
            table_name: None,
            table_oid: 0,
            column_id: 0,
            data_type: infer_data_type(expr, input_columns),
        },
        _ => ColumnDesc {
            name: "?column?".to_string(),
            table_name: None,
            table_oid: 0,
            column_id: 0,
            data_type: infer_data_type(expr, input_columns),
        },
    };

    if let Some(alias) = alias {
        desc.name = alias.to_string();
    }

    desc
}

/// Infers the output data type from an expression.
///
/// For column references, uses the known column type. For other expressions,
/// uses a heuristic based on the expression kind. The actual type will be
/// determined at evaluation time and may differ.
fn infer_data_type(expr: &Expr, columns: &[ColumnDesc]) -> Type {
    match expr {
        Expr::ColumnRef { table, column } => {
            match resolve_column_index(table.as_deref(), column, columns) {
                Ok(i) => columns[i].data_type,
                Err(_) => Type::Text,
            }
        }
        Expr::Integer(_) => Type::Int8,
        Expr::Float(_) => Type::Float8,
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
            _ => infer_data_type(left, columns),
        },
        Expr::UnaryOp { operand, .. } => infer_data_type(operand, columns),
        Expr::IsNull { .. } | Expr::InList { .. } | Expr::Between { .. } | Expr::Like { .. } => {
            Type::Bool
        }
        Expr::Cast { data_type, .. } => data_type.to_type(),
        _ => Type::Text,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    use crate::db::Database;
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

    #[tokio::test]
    async fn test_plan_select_from_sys_tables() {
        let (db, snapshot) = setup_test_db().await;

        let select = SelectStmt {
            distinct: false,
            columns: vec![SelectItem::Wildcard],
            from: Some(FromClause {
                tables: vec![TableRef::Table {
                    name: "sys_tables".to_string(),
                    alias: None,
                }],
            }),
            where_clause: None,
            group_by: vec![],
            having: None,
            order_by: vec![],
            limit: None,
            offset: None,
            locking: None,
        };

        let plan = plan_select(&select, &db, &snapshot).await.unwrap();

        // Projection over SeqScan with 3 columns
        assert_eq!(plan.columns().len(), 3);
        assert_eq!(plan.columns()[0].name, "table_id");
        assert_eq!(plan.columns()[1].name, "table_name");
        assert_eq!(plan.columns()[2].name, "first_page");
    }

    #[tokio::test]
    async fn test_plan_select_no_from() {
        let (db, snapshot) = setup_test_db().await;

        let select = SelectStmt {
            distinct: false,
            columns: vec![SelectItem::Expr {
                expr: Expr::Integer(42),
                alias: None,
            }],
            from: None,
            where_clause: None,
            group_by: vec![],
            having: None,
            order_by: vec![],
            limit: None,
            offset: None,
            locking: None,
        };

        let plan = plan_select(&select, &db, &snapshot).await.unwrap();

        // Projection over ValuesScan with 1 expression column
        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].name, "?column?");
    }

    #[tokio::test]
    async fn test_plan_select_table_not_found() {
        let (db, snapshot) = setup_test_db().await;

        let select = SelectStmt {
            distinct: false,
            columns: vec![SelectItem::Wildcard],
            from: Some(FromClause {
                tables: vec![TableRef::Table {
                    name: "nonexistent".to_string(),
                    alias: None,
                }],
            }),
            where_clause: None,
            group_by: vec![],
            having: None,
            order_by: vec![],
            limit: None,
            offset: None,
            locking: None,
        };

        let result = plan_select(&select, &db, &snapshot).await;
        assert!(matches!(result, Err(ExecutorError::TableNotFound { .. })));
    }

    #[tokio::test]
    async fn test_plan_select_with_where() {
        let (db, snapshot) = setup_test_db().await;

        // SELECT table_name FROM sys_tables WHERE table_id = 1
        let select = SelectStmt {
            distinct: false,
            columns: vec![SelectItem::Expr {
                expr: Expr::ColumnRef {
                    table: None,
                    column: "table_name".to_string(),
                },
                alias: None,
            }],
            from: Some(FromClause {
                tables: vec![TableRef::Table {
                    name: "sys_tables".to_string(),
                    alias: None,
                }],
            }),
            where_clause: Some(Expr::BinaryOp {
                left: Box::new(Expr::ColumnRef {
                    table: None,
                    column: "table_id".to_string(),
                }),
                op: crate::sql::BinaryOperator::Eq,
                right: Box::new(Expr::Integer(1)),
            }),
            group_by: vec![],
            having: None,
            order_by: vec![],
            limit: None,
            offset: None,
            locking: None,
        };

        let plan = plan_select(&select, &db, &snapshot).await.unwrap();

        // Projection over Filter over SeqScan, output has 1 column
        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].name, "table_name");
        // ColumnRef inherits source table metadata from input
        assert_eq!(plan.columns()[0].table_name.as_deref(), Some("sys_tables"));
        assert_ne!(plan.columns()[0].table_oid, 0);
        assert_ne!(plan.columns()[0].column_id, 0);
    }

    #[tokio::test]
    async fn test_plan_select_expr_has_no_table_metadata() {
        let (db, snapshot) = setup_test_db().await;

        // SELECT 1 + table_id FROM sys_tables
        let select = SelectStmt {
            distinct: false,
            columns: vec![SelectItem::Expr {
                expr: Expr::BinaryOp {
                    left: Box::new(Expr::Integer(1)),
                    op: crate::sql::BinaryOperator::Add,
                    right: Box::new(Expr::ColumnRef {
                        table: None,
                        column: "table_id".to_string(),
                    }),
                },
                alias: None,
            }],
            from: Some(FromClause {
                tables: vec![TableRef::Table {
                    name: "sys_tables".to_string(),
                    alias: None,
                }],
            }),
            where_clause: None,
            group_by: vec![],
            having: None,
            order_by: vec![],
            limit: None,
            offset: None,
            locking: None,
        };

        let plan = plan_select(&select, &db, &snapshot).await.unwrap();

        // Computed expressions have no source table info
        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].name, "?column?");
        assert_eq!(plan.columns()[0].table_name, None);
        assert_eq!(plan.columns()[0].table_oid, 0);
        assert_eq!(plan.columns()[0].column_id, 0);
    }

    #[tokio::test]
    async fn test_plan_select_qualified_column_ref() {
        let (db, snapshot) = setup_test_db().await;

        // SELECT sys_tables.table_name FROM sys_tables
        let select = SelectStmt {
            distinct: false,
            columns: vec![SelectItem::Expr {
                expr: Expr::ColumnRef {
                    table: Some("sys_tables".to_string()),
                    column: "table_name".to_string(),
                },
                alias: None,
            }],
            from: Some(FromClause {
                tables: vec![TableRef::Table {
                    name: "sys_tables".to_string(),
                    alias: None,
                }],
            }),
            where_clause: None,
            group_by: vec![],
            having: None,
            order_by: vec![],
            limit: None,
            offset: None,
            locking: None,
        };

        let plan = plan_select(&select, &db, &snapshot).await.unwrap();

        // Qualified ColumnRef resolves with full source table metadata
        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].name, "table_name");
        assert_eq!(plan.columns()[0].table_name.as_deref(), Some("sys_tables"));
        assert_ne!(plan.columns()[0].table_oid, 0);
        assert_ne!(plan.columns()[0].column_id, 0);
    }
}
