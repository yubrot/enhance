//! Query planner for converting AST to execution plan.
//!
//! This is a simple direct translation planner without optimization.
//! Rule-based optimization for index selection comes in Step 17.

use std::sync::Arc;

use crate::catalog::{Catalog, ColumnInfo};
use crate::executor::plan::{Executor, Filter, OutputColumn, Projection, SeqScan};
use crate::executor::ExecutorError;
use crate::protocol::type_oid;
use crate::sql::{Expr, SelectItem, SelectStmt, TableRef};
use crate::storage::{BufferPool, Replacer, Storage};
use crate::tx::{Snapshot, TransactionManager};

/// Result type for projection building: (expressions with aliases, output column metadata).
type ProjectionResult = Result<(Vec<(Expr, String)>, Vec<OutputColumn>), ExecutorError>;

/// Plans a SELECT statement into an executor tree.
///
/// # Arguments
///
/// * `stmt` - The SELECT statement to plan.
/// * `snapshot` - MVCC snapshot for visibility.
/// * `catalog` - Catalog for table/column lookups.
/// * `pool` - Buffer pool for page access.
/// * `tx_manager` - Transaction manager.
///
/// # Errors
///
/// Returns an error if the table is not found or the query is unsupported.
pub async fn plan_select<S: Storage + 'static, R: Replacer + 'static>(
    stmt: &SelectStmt,
    snapshot: Snapshot,
    catalog: &Catalog<S, R>,
    pool: Arc<BufferPool<S, R>>,
    tx_manager: Arc<TransactionManager>,
) -> Result<Box<dyn Executor>, ExecutorError> {
    // Validate unsupported features
    if stmt.distinct {
        return Err(ExecutorError::Unsupported {
            feature: "DISTINCT".to_string(),
        });
    }
    if !stmt.group_by.is_empty() {
        return Err(ExecutorError::Unsupported {
            feature: "GROUP BY".to_string(),
        });
    }
    if stmt.having.is_some() {
        return Err(ExecutorError::Unsupported {
            feature: "HAVING".to_string(),
        });
    }
    if !stmt.order_by.is_empty() {
        return Err(ExecutorError::Unsupported {
            feature: "ORDER BY".to_string(),
        });
    }
    if stmt.limit.is_some() {
        return Err(ExecutorError::Unsupported {
            feature: "LIMIT".to_string(),
        });
    }
    if stmt.offset.is_some() {
        return Err(ExecutorError::Unsupported {
            feature: "OFFSET".to_string(),
        });
    }
    if stmt.locking.is_some() {
        return Err(ExecutorError::Unsupported {
            feature: "FOR UPDATE/SHARE".to_string(),
        });
    }

    // Get the source table
    let from = stmt.from.as_ref().ok_or_else(|| ExecutorError::Unsupported {
        feature: "SELECT without FROM".to_string(),
    })?;

    if from.tables.len() != 1 {
        return Err(ExecutorError::Unsupported {
            feature: "multiple tables (JOINs)".to_string(),
        });
    }

    let table_ref = &from.tables[0];
    let (table_name, _alias) = match table_ref {
        TableRef::Table { name, alias } => (name.clone(), alias.clone()),
        TableRef::Join { .. } => {
            return Err(ExecutorError::Unsupported {
                feature: "JOINs".to_string(),
            });
        }
        TableRef::Subquery { .. } => {
            return Err(ExecutorError::Unsupported {
                feature: "subqueries in FROM".to_string(),
            });
        }
    };

    // Look up table in catalog
    let table_info = catalog
        .get_table(&snapshot, &table_name)
        .await?
        .ok_or_else(|| ExecutorError::TableNotFound {
            name: table_name.clone(),
        })?;

    let columns = catalog.get_columns(&snapshot, table_info.table_id).await?;

    // Build projection for SELECT columns
    let (output_exprs, output_columns) =
        build_projection(&stmt.columns, &columns, &table_name)?;

    // Create SeqScan
    let scan = SeqScan::new(
        table_name.clone(),
        columns.clone(),
        table_info.first_page,
        snapshot,
        pool,
        tx_manager,
    );

    // Build the executor tree based on whether we have a WHERE clause
    // We need to handle types carefully since Filter and Projection are generic
    if let Some(where_clause) = &stmt.where_clause {
        let filter = Filter::new(scan, columns.clone(), where_clause.clone());
        let projection = Projection::new(filter, columns, output_exprs, output_columns);
        Ok(Box::new(projection))
    } else {
        let projection = Projection::new(scan, columns, output_exprs, output_columns);
        Ok(Box::new(projection))
    }
}

/// Builds the projection expressions and output column metadata.
fn build_projection(
    select_items: &[SelectItem],
    columns: &[ColumnInfo],
    table_name: &str,
) -> ProjectionResult {
    let mut output_exprs = Vec::new();
    let mut output_columns = Vec::new();

    for item in select_items {
        match item {
            SelectItem::Wildcard => {
                // SELECT * - include all columns
                for col in columns {
                    let expr = Expr::ColumnRef {
                        table: None,
                        column: col.column_name.clone(),
                    };
                    output_exprs.push((expr, col.column_name.clone()));
                    output_columns.push(OutputColumn::new(
                        col.column_name.clone(),
                        col.type_oid,
                    ));
                }
            }
            SelectItem::QualifiedWildcard(qual_table) => {
                // SELECT table.* - include all columns from that table
                if qual_table != table_name {
                    return Err(ExecutorError::TableNotFound {
                        name: qual_table.clone(),
                    });
                }
                for col in columns {
                    let expr = Expr::ColumnRef {
                        table: Some(qual_table.clone()),
                        column: col.column_name.clone(),
                    };
                    output_exprs.push((expr, col.column_name.clone()));
                    output_columns.push(OutputColumn::new(
                        col.column_name.clone(),
                        col.type_oid,
                    ));
                }
            }
            SelectItem::Expr { expr, alias } => {
                // Determine output name: alias if provided, else derive from expression
                let name = alias.clone().unwrap_or_else(|| expr_to_name(expr));
                let type_oid = infer_type(expr, columns);
                output_exprs.push((expr.clone(), name.clone()));
                output_columns.push(OutputColumn::new(name, type_oid));
            }
        }
    }

    Ok((output_exprs, output_columns))
}

/// Derives a column name from an expression.
fn expr_to_name(expr: &Expr) -> String {
    match expr {
        Expr::ColumnRef { column, .. } => column.clone(),
        Expr::Integer(_) => "int4".to_string(),
        Expr::Float(_) => "float8".to_string(),
        Expr::String(_) => "text".to_string(),
        Expr::Boolean(_) => "bool".to_string(),
        Expr::Null => "null".to_string(),
        _ => "?column?".to_string(),
    }
}

/// Infers the type OID of an expression.
fn infer_type(expr: &Expr, columns: &[ColumnInfo]) -> i32 {
    match expr {
        Expr::ColumnRef { column, .. } => {
            // Find the column and return its type
            columns
                .iter()
                .find(|c| &c.column_name == column)
                .map(|c| c.type_oid)
                .unwrap_or(type_oid::UNKNOWN)
        }
        Expr::Null => type_oid::UNKNOWN,
        Expr::Boolean(_) => type_oid::BOOL,
        Expr::Integer(n) => {
            if *n >= i32::MIN as i64 && *n <= i32::MAX as i64 {
                type_oid::INT4
            } else {
                type_oid::INT8
            }
        }
        Expr::Float(_) => type_oid::FLOAT8,
        Expr::String(_) => type_oid::TEXT,
        Expr::BinaryOp { left, op, .. } => {
            use crate::sql::BinaryOperator::*;
            match op {
                // Comparison operators return boolean
                Eq | Neq | Lt | LtEq | Gt | GtEq | And | Or => type_oid::BOOL,
                // Arithmetic operators: use left operand's type (simplified)
                Add | Sub | Mul | Div | Mod => infer_type(left, columns),
                // Concatenation returns text
                Concat => type_oid::TEXT,
            }
        }
        Expr::UnaryOp { op, operand } => {
            use crate::sql::UnaryOperator::*;
            match op {
                Not => type_oid::BOOL,
                Minus | Plus => infer_type(operand, columns),
            }
        }
        Expr::IsNull { .. } => type_oid::BOOL,
        Expr::Between { .. } => type_oid::BOOL,
        Expr::InList { .. } => type_oid::BOOL,
        _ => type_oid::UNKNOWN,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protocol::type_oid;

    #[test]
    fn test_expr_to_name() {
        assert_eq!(
            expr_to_name(&Expr::ColumnRef {
                table: None,
                column: "id".to_string()
            }),
            "id"
        );
        assert_eq!(expr_to_name(&Expr::Integer(42)), "int4");
        assert_eq!(expr_to_name(&Expr::Float(3.14)), "float8");
        assert_eq!(
            expr_to_name(&Expr::String("hello".to_string())),
            "text"
        );
    }

    #[test]
    fn test_infer_type() {
        let columns = vec![
            ColumnInfo::new(1, 0, "id".to_string(), type_oid::INT4, 0),
            ColumnInfo::new(1, 1, "name".to_string(), type_oid::TEXT, 0),
        ];

        // Column reference
        assert_eq!(
            infer_type(
                &Expr::ColumnRef {
                    table: None,
                    column: "id".to_string()
                },
                &columns
            ),
            type_oid::INT4
        );

        // Literals
        assert_eq!(infer_type(&Expr::Integer(42), &columns), type_oid::INT4);
        assert_eq!(infer_type(&Expr::Float(3.14), &columns), type_oid::FLOAT8);
        assert_eq!(
            infer_type(&Expr::String("hi".to_string()), &columns),
            type_oid::TEXT
        );
        assert_eq!(infer_type(&Expr::Boolean(true), &columns), type_oid::BOOL);

        // Comparison returns bool
        assert_eq!(
            infer_type(
                &Expr::BinaryOp {
                    left: Box::new(Expr::Integer(1)),
                    op: crate::sql::BinaryOperator::Eq,
                    right: Box::new(Expr::Integer(2)),
                },
                &columns
            ),
            type_oid::BOOL
        );
    }

    #[test]
    fn test_build_projection_wildcard() {
        let columns = vec![
            ColumnInfo::new(1, 0, "id".to_string(), type_oid::INT4, 0),
            ColumnInfo::new(1, 1, "name".to_string(), type_oid::TEXT, 0),
        ];

        let (exprs, output_cols) =
            build_projection(&[SelectItem::Wildcard], &columns, "users").unwrap();

        assert_eq!(exprs.len(), 2);
        assert_eq!(output_cols.len(), 2);
        assert_eq!(output_cols[0].name, "id");
        assert_eq!(output_cols[0].type_oid, type_oid::INT4);
        assert_eq!(output_cols[1].name, "name");
        assert_eq!(output_cols[1].type_oid, type_oid::TEXT);
    }

    #[test]
    fn test_build_projection_expr_with_alias() {
        let columns = vec![ColumnInfo::new(
            1,
            0,
            "id".to_string(),
            type_oid::INT4,
            0,
        )];

        let (exprs, output_cols) = build_projection(
            &[SelectItem::Expr {
                expr: Expr::ColumnRef {
                    table: None,
                    column: "id".to_string(),
                },
                alias: Some("user_id".to_string()),
            }],
            &columns,
            "users",
        )
        .unwrap();

        assert_eq!(exprs.len(), 1);
        assert_eq!(output_cols[0].name, "user_id");
    }
}
