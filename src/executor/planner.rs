//! Query planner for SELECT statements.
//!
//! Transforms a parsed [`SelectStmt`] AST into a logical [`Plan`] tree
//! by resolving table references via the catalog and binding column names.
//! The plan is then materialized into an [`ExecutorNode`] tree by
//! [`build_executor`].

use std::future::Future;
use std::pin::Pin;

use crate::catalog::ColumnInfo;
use crate::datum::Type;
use crate::db::Database;
use crate::heap::HeapPage;
use crate::sql::{Expr, FromClause, SelectItem, SelectStmt, TableRef};
use crate::storage::{PageId, Replacer, Storage};
use crate::tx::Snapshot;

use crate::heap::{Tuple, TupleId};

use super::error::ExecutorError;
use super::eval::bind_expr;
use super::expr::BoundExpr;
use super::node::{ExecutorNode, Filter, Projection, SeqScan, ValuesScan};
use super::plan::Plan;
use super::ColumnDesc;

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
        let bound_predicate = bind_expr(where_clause, &columns)?;
        plan = Plan::Filter {
            input: Box::new(plan),
            predicate: bound_predicate,
        };
    }

    // Step 3: SELECT list -> Projection
    plan = build_projection_plan(plan, &select.columns)?;

    Ok(plan)
}

/// Materializes a logical [`Plan`] into a physical [`ExecutorNode`] tree.
///
/// Currently pre-loads all tuples from heap pages into memory. For future
/// streaming support:
///
/// 1. Define a `HeapScanner` trait or `Pin<Box<dyn Stream<Item = ...>>>`
/// 2. Inject a scanner into SeqScan instead of pre-loaded `Vec`
/// 3. `SeqScan::next().await` fetches pages lazily via the scanner
/// 4. Plan, explain, and all other nodes remain unchanged
///
/// The async `next()` introduced here is the prerequisite that makes
/// this transition non-breaking.
pub fn build_executor<'a, S: Storage, R: Replacer>(
    plan: Plan,
    database: &'a Database<S, R>,
    snapshot: &'a Snapshot,
) -> Pin<Box<dyn Future<Output = Result<ExecutorNode, ExecutorError>> + Send + 'a>> {
    Box::pin(async move {
        match plan {
            Plan::SeqScan {
                table_name,
                first_page,
                schema,
                columns,
                ..
            } => {
                let tuples = scan_visible_tuples(database, snapshot, first_page, &schema).await?;
                Ok(ExecutorNode::SeqScan(SeqScan::new(
                    table_name, columns, tuples,
                )))
            }
            Plan::Filter { input, predicate } => {
                let child = build_executor(*input, database, snapshot).await?;
                Ok(ExecutorNode::Filter(Filter::new(child, predicate)))
            }
            Plan::Projection {
                input,
                exprs,
                columns,
            } => {
                let child = build_executor(*input, database, snapshot).await?;
                Ok(ExecutorNode::Projection(Projection::new(
                    child, exprs, columns,
                )))
            }
            Plan::ValuesScan => Ok(ExecutorNode::ValuesScan(ValuesScan::new())),
        }
    })
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
///
/// No data is loaded — only catalog metadata is gathered.
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
    let columns = build_column_descs(&column_infos, table_info.table_id);

    Ok(Plan::SeqScan {
        table_name: table_name.to_string(),
        table_id: table_info.table_id,
        first_page: table_info.first_page,
        schema,
        columns,
    })
}

/// Builds column descriptors from catalog column info.
fn build_column_descs(column_infos: &[ColumnInfo], table_id: u32) -> Vec<ColumnDesc> {
    column_infos
        .iter()
        .enumerate()
        .map(|(i, col)| ColumnDesc {
            name: col.column_name.clone(),
            table_oid: table_id as i32,
            column_id: (i + 1) as i16,
            data_type: col.data_type,
        })
        .collect()
}

/// Scans a heap page and returns all visible tuples.
async fn scan_visible_tuples<S: Storage, R: Replacer>(
    database: &Database<S, R>,
    snapshot: &Snapshot,
    page_id: PageId,
    schema: &[Type],
) -> Result<Vec<Tuple>, ExecutorError> {
    let page_guard = database.pool().fetch_page(page_id).await?;
    let page = HeapPage::new(page_guard);

    let mut tuples = Vec::new();
    for (slot_id, header, record) in page.scan(schema) {
        if !snapshot.is_tuple_visible(&header, database.tx_manager()) {
            continue;
        }
        let tid = TupleId { page_id, slot_id };
        tuples.push(Tuple::from_heap(tid, record));
    }

    Ok(tuples)
}

/// Builds a Projection plan from the SELECT list.
///
/// Column names and types are inferred from the AST expression *before* binding,
/// then the expression is bound to positional indices for efficient evaluation.
fn build_projection_plan(input: Plan, select_items: &[SelectItem]) -> Result<Plan, ExecutorError> {
    let input_columns = input.columns().to_vec();
    let mut exprs = Vec::new();
    let mut out_columns = Vec::new();

    for item in select_items {
        match item {
            SelectItem::Wildcard => {
                // Expand to all input columns using positional indices
                for (i, col) in input_columns.iter().enumerate() {
                    exprs.push(BoundExpr::Column(i));
                    out_columns.push(ColumnDesc {
                        name: col.name.clone(),
                        table_oid: col.table_oid,
                        column_id: col.column_id,
                        data_type: col.data_type,
                    });
                }
            }
            SelectItem::QualifiedWildcard(table_name) => {
                // Expand to all columns from the specified table
                let mut found = false;
                for (i, col) in input_columns.iter().enumerate() {
                    // For single-table queries, we match by checking if the child is a
                    // SeqScan with the matching table name. Since we only support
                    // single-table queries now, all columns belong to the table.
                    // A more sophisticated check would be needed for JOINs.
                    let _ = table_name;
                    found = true;
                    exprs.push(BoundExpr::Column(i));
                    out_columns.push(ColumnDesc {
                        name: col.name.clone(),
                        table_oid: col.table_oid,
                        column_id: col.column_id,
                        data_type: col.data_type,
                    });
                }
                if !found {
                    return Err(ExecutorError::TableNotFound {
                        name: table_name.clone(),
                    });
                }
            }
            SelectItem::Expr { expr, alias } => {
                // Infer name and type from AST before binding
                let col_name = alias.clone().unwrap_or_else(|| infer_column_name(expr));
                let col_data_type = infer_data_type(expr, &input_columns);

                // Bind column names to positional indices
                let bound = bind_expr(expr, &input_columns)?;

                exprs.push(bound);
                out_columns.push(ColumnDesc {
                    name: col_name,
                    table_oid: 0,
                    column_id: 0,
                    data_type: col_data_type,
                });
            }
        }
    }

    Ok(Plan::Projection {
        input: Box::new(input),
        exprs,
        columns: out_columns,
    })
}

/// Infers a column name from an expression (for un-aliased expressions).
fn infer_column_name(expr: &Expr) -> String {
    match expr {
        Expr::ColumnRef { column, .. } => column.clone(),
        Expr::Function { name, .. } => name.clone(),
        Expr::Cast { data_type, .. } => data_type.display_name().to_lowercase(),
        _ => "?column?".to_string(),
    }
}

/// Infers the output data type from an expression.
///
/// For column references, uses the known column type. For other expressions,
/// uses a heuristic based on the expression kind. The actual type will be
/// determined at evaluation time and may differ.
fn infer_data_type(expr: &Expr, columns: &[ColumnDesc]) -> Type {
    match expr {
        Expr::ColumnRef { column, .. } => {
            // Look up the column type
            for col in columns {
                if col.name.eq_ignore_ascii_case(column) {
                    return col.data_type;
                }
            }
            Type::Text
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

        // Should have 3 columns (table_id, table_name, first_page)
        assert_eq!(plan.columns().len(), 3);
        assert_eq!(plan.columns()[0].name, "table_id");
        assert_eq!(plan.columns()[1].name, "table_name");
        assert_eq!(plan.columns()[2].name, "first_page");

        // Materialize and verify rows
        let mut node = build_executor(plan, &db, &snapshot).await.unwrap();
        let mut count = 0;
        while node.next().await.unwrap().is_some() {
            count += 1;
        }
        assert!(
            count >= 3,
            "expected at least 3 catalog tables, got {}",
            count
        );
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
        let mut node = build_executor(plan, &db, &snapshot).await.unwrap();

        let tuple = node.next().await.unwrap().unwrap();
        assert_eq!(tuple.record.values.len(), 1);
        assert_eq!(tuple.record.values[0], crate::datum::Value::Int64(42));
        assert!(node.next().await.unwrap().is_none());
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
        let mut node = build_executor(plan, &db, &snapshot).await.unwrap();

        let tuple = node.next().await.unwrap().unwrap();
        assert_eq!(tuple.record.values.len(), 1);
        assert_eq!(
            tuple.record.values[0],
            crate::datum::Value::Text("sys_tables".to_string())
        );
        assert!(node.next().await.unwrap().is_none());
    }
}
