//! Query planner: AST to Plan conversion.
//!
//! The planner converts parsed SQL statements (AST) into execution plans.
//! It resolves column names to indices, looks up table metadata, and
//! validates query structure.

use std::sync::Arc;

use super::error::ExecutorError;
use super::expr::BoundExpr;
use super::plan::{ColumnDesc, Plan};
use crate::catalog::ColumnInfo;
use crate::db::Database;
use crate::sql::{Expr, SelectItem, SelectStmt};
use crate::storage::{Replacer, Storage};
use crate::tx::Snapshot;

/// Query planner for converting AST to Plan.
///
/// The planner holds references to the database for catalog lookups
/// and a snapshot for MVCC-consistent metadata reads.
pub struct Planner<'a, S: Storage, R: Replacer> {
    database: Arc<Database<S, R>>,
    snapshot: &'a Snapshot,
}

impl<'a, S: Storage, R: Replacer> Planner<'a, S, R> {
    /// Creates a new planner.
    pub fn new(database: Arc<Database<S, R>>, snapshot: &'a Snapshot) -> Self {
        Self { database, snapshot }
    }

    /// Plans a SELECT statement.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The table doesn't exist
    /// - A referenced column doesn't exist
    /// - An unsupported feature is used
    pub async fn plan_select(&self, stmt: &SelectStmt) -> Result<Plan, ExecutorError> {
        // We only support single-table SELECTs for now
        let table_name = self.extract_table_name(stmt)?;

        // Get table metadata
        let table_info = self
            .database
            .catalog()
            .get_table(self.snapshot, &table_name)
            .await
            .map_err(|e| ExecutorError::Internal {
                message: format!("catalog error: {}", e),
            })?
            .ok_or_else(|| ExecutorError::TableNotFound {
                name: table_name.clone(),
            })?;

        // Get column metadata
        let columns = self
            .database
            .catalog()
            .get_columns(self.snapshot, table_info.table_id)
            .await
            .map_err(|e| ExecutorError::Internal {
                message: format!("catalog error: {}", e),
            })?;

        // Build schema (type OIDs) for deserialization
        let schema: Vec<i32> = columns.iter().map(|c| c.type_oid).collect();

        // Build output column descriptors for SeqScan
        let scan_output_columns: Vec<ColumnDesc> = columns
            .iter()
            .map(|c| ColumnDesc::new(&c.column_name, c.type_oid))
            .collect();

        // Start with SeqScan
        let mut plan = Plan::SeqScan {
            table_name: table_name.clone(),
            table_id: table_info.table_id,
            first_page: table_info.first_page,
            schema,
            output_columns: scan_output_columns.clone(),
        };

        // Apply WHERE filter if present
        if let Some(ref where_clause) = stmt.where_clause {
            let predicate = self.bind_expr(where_clause, &columns)?;
            plan = Plan::Filter {
                input: Box::new(plan),
                predicate,
            };
        }

        // Apply projection if not SELECT *
        let (projection_exprs, projection_columns) =
            self.plan_select_list(&stmt.columns, &columns)?;

        // Only add projection if it's not just a pass-through of all columns
        if !self.is_identity_projection(&projection_exprs, &columns) {
            plan = Plan::Projection {
                input: Box::new(plan),
                exprs: projection_exprs,
                output_columns: projection_columns,
            };
        }

        Ok(plan)
    }

    /// Extracts the table name from a SELECT statement.
    fn extract_table_name(&self, stmt: &SelectStmt) -> Result<String, ExecutorError> {
        let from = stmt.from.as_ref().ok_or_else(|| ExecutorError::Unsupported {
            message: "SELECT without FROM is not supported".to_string(),
        })?;

        if from.tables.len() != 1 {
            return Err(ExecutorError::Unsupported {
                message: "only single-table SELECTs are supported".to_string(),
            });
        }

        match &from.tables[0] {
            crate::sql::TableRef::Table { name, .. } => Ok(name.clone()),
            _ => Err(ExecutorError::Unsupported {
                message: "only simple table references are supported".to_string(),
            }),
        }
    }

    /// Plans the SELECT list.
    fn plan_select_list(
        &self,
        items: &[SelectItem],
        columns: &[ColumnInfo],
    ) -> Result<(Vec<BoundExpr>, Vec<ColumnDesc>), ExecutorError> {
        let mut exprs = Vec::new();
        let mut output_columns = Vec::new();

        for item in items {
            match item {
                SelectItem::Wildcard => {
                    // SELECT * - include all columns
                    for (i, col) in columns.iter().enumerate() {
                        exprs.push(BoundExpr::Column(i));
                        output_columns.push(ColumnDesc::new(&col.column_name, col.type_oid));
                    }
                }
                SelectItem::QualifiedWildcard(_table) => {
                    // table.* - for single-table, same as *
                    for (i, col) in columns.iter().enumerate() {
                        exprs.push(BoundExpr::Column(i));
                        output_columns.push(ColumnDesc::new(&col.column_name, col.type_oid));
                    }
                }
                SelectItem::Expr { expr, alias } => {
                    let bound_expr = self.bind_expr(expr, columns)?;
                    let col_name = alias
                        .clone()
                        .unwrap_or_else(|| self.expr_to_name(expr));
                    let type_oid = self.infer_expr_type(&bound_expr, columns);
                    exprs.push(bound_expr);
                    output_columns.push(ColumnDesc::new(col_name, type_oid));
                }
            }
        }

        Ok((exprs, output_columns))
    }

    /// Checks if the projection is an identity (pass-through of all columns in order).
    fn is_identity_projection(&self, exprs: &[BoundExpr], columns: &[ColumnInfo]) -> bool {
        if exprs.len() != columns.len() {
            return false;
        }

        exprs.iter().enumerate().all(|(i, expr)| {
            matches!(expr, BoundExpr::Column(idx) if *idx == i)
        })
    }

    /// Binds an AST expression to a BoundExpr with resolved column indices.
    fn bind_expr(&self, expr: &Expr, columns: &[ColumnInfo]) -> Result<BoundExpr, ExecutorError> {
        match expr {
            Expr::Null => Ok(BoundExpr::Null),
            Expr::Boolean(b) => Ok(BoundExpr::Boolean(*b)),
            Expr::Integer(n) => Ok(BoundExpr::Integer(*n)),
            Expr::Float(f) => Ok(BoundExpr::Float(*f)),
            Expr::String(s) => Ok(BoundExpr::String(s.clone())),

            Expr::ColumnRef { table: _, column } => {
                // Find column by name
                let idx = columns
                    .iter()
                    .position(|c| c.column_name == *column)
                    .ok_or_else(|| ExecutorError::ColumnNotFound {
                        name: column.clone(),
                    })?;
                Ok(BoundExpr::Column(idx))
            }

            Expr::BinaryOp { left, op, right } => {
                let bound_left = self.bind_expr(left, columns)?;
                let bound_right = self.bind_expr(right, columns)?;
                Ok(BoundExpr::BinaryOp {
                    left: Box::new(bound_left),
                    op: *op,
                    right: Box::new(bound_right),
                })
            }

            Expr::UnaryOp { op, operand } => {
                let bound_operand = self.bind_expr(operand, columns)?;
                Ok(BoundExpr::UnaryOp {
                    op: *op,
                    operand: Box::new(bound_operand),
                })
            }

            Expr::IsNull { expr, negated } => {
                let bound_expr = self.bind_expr(expr, columns)?;
                Ok(BoundExpr::IsNull {
                    expr: Box::new(bound_expr),
                    negated: *negated,
                })
            }

            Expr::Cast { expr, data_type } => {
                let bound_expr = self.bind_expr(expr, columns)?;
                Ok(BoundExpr::Cast {
                    expr: Box::new(bound_expr),
                    target_type: data_type.clone(),
                })
            }

            // Unsupported expressions
            Expr::Parameter(_) => Err(ExecutorError::Unsupported {
                message: "parameter expressions are not yet supported".to_string(),
            }),
            Expr::InList { .. } => Err(ExecutorError::Unsupported {
                message: "IN list expressions are not yet supported".to_string(),
            }),
            Expr::InSubquery { .. } => Err(ExecutorError::Unsupported {
                message: "IN subquery expressions are not yet supported".to_string(),
            }),
            Expr::Between { .. } => Err(ExecutorError::Unsupported {
                message: "BETWEEN expressions are not yet supported".to_string(),
            }),
            Expr::Like { .. } => Err(ExecutorError::Unsupported {
                message: "LIKE expressions are not yet supported".to_string(),
            }),
            Expr::Exists { .. } => Err(ExecutorError::Unsupported {
                message: "EXISTS expressions are not yet supported".to_string(),
            }),
            Expr::Case { .. } => Err(ExecutorError::Unsupported {
                message: "CASE expressions are not yet supported".to_string(),
            }),
            Expr::Function { .. } => Err(ExecutorError::Unsupported {
                message: "function calls are not yet supported".to_string(),
            }),
            Expr::Subquery(_) => Err(ExecutorError::Unsupported {
                message: "subqueries are not yet supported".to_string(),
            }),
        }
    }

    /// Generates a name for an expression (for column headers).
    fn expr_to_name(&self, expr: &Expr) -> String {
        match expr {
            Expr::ColumnRef { column, .. } => column.clone(),
            Expr::Null => "null".to_string(),
            Expr::Boolean(b) => b.to_string(),
            Expr::Integer(n) => n.to_string(),
            Expr::Float(f) => f.to_string(),
            Expr::String(s) => format!("'{}'", s),
            Expr::BinaryOp { left, op, right } => {
                format!(
                    "({} {} {})",
                    self.expr_to_name(left),
                    op.as_str(),
                    self.expr_to_name(right)
                )
            }
            Expr::UnaryOp { op, operand } => {
                format!("{}{}", op.as_str(), self.expr_to_name(operand))
            }
            Expr::Cast { expr, data_type } => {
                format!(
                    "{}::{}",
                    self.expr_to_name(expr),
                    data_type.display_name()
                )
            }
            Expr::IsNull { expr, negated } => {
                let suffix = if *negated { " IS NOT NULL" } else { " IS NULL" };
                format!("{}{}", self.expr_to_name(expr), suffix)
            }
            _ => "?column?".to_string(),
        }
    }

    /// Infers the output type of an expression.
    fn infer_expr_type(&self, expr: &BoundExpr, columns: &[ColumnInfo]) -> i32 {
        use crate::protocol::type_oid;
        use crate::sql::BinaryOperator;

        match expr {
            BoundExpr::Null => type_oid::UNKNOWN,
            BoundExpr::Boolean(_) => type_oid::BOOL,
            BoundExpr::Integer(_) => type_oid::INT8,
            BoundExpr::Float(_) => type_oid::FLOAT8,
            BoundExpr::String(_) => type_oid::TEXT,
            BoundExpr::Column(idx) => {
                columns.get(*idx).map(|c| c.type_oid).unwrap_or(type_oid::UNKNOWN)
            }
            BoundExpr::BinaryOp { left, op, .. } => {
                match op {
                    // Comparison operators return boolean
                    BinaryOperator::Eq
                    | BinaryOperator::Neq
                    | BinaryOperator::Lt
                    | BinaryOperator::LtEq
                    | BinaryOperator::Gt
                    | BinaryOperator::GtEq
                    | BinaryOperator::And
                    | BinaryOperator::Or => type_oid::BOOL,
                    // Arithmetic operators return the left operand type (simplified)
                    BinaryOperator::Add
                    | BinaryOperator::Sub
                    | BinaryOperator::Mul
                    | BinaryOperator::Div
                    | BinaryOperator::Mod => self.infer_expr_type(left, columns),
                    // Concat returns text
                    BinaryOperator::Concat => type_oid::TEXT,
                }
            }
            BoundExpr::UnaryOp { op, operand } => {
                use crate::sql::UnaryOperator;
                match op {
                    UnaryOperator::Not => type_oid::BOOL,
                    UnaryOperator::Minus | UnaryOperator::Plus => {
                        self.infer_expr_type(operand, columns)
                    }
                }
            }
            BoundExpr::IsNull { .. } => type_oid::BOOL,
            BoundExpr::Cast { target_type, .. } => target_type.to_oid(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sql::Parser;
    use crate::storage::MemoryStorage;
    use crate::tx::CommandId;

    async fn create_test_db() -> Arc<Database<Arc<MemoryStorage>, crate::storage::LruReplacer>> {
        let storage = Arc::new(MemoryStorage::new());
        Arc::new(Database::open(storage, 100).await.unwrap())
    }

    #[tokio::test]
    async fn test_plan_select_star() {
        let db = create_test_db().await;

        // Create table
        let mut session = crate::db::Session::new(db.clone());
        session
            .execute_query("CREATE TABLE test (id INT, name TEXT)")
            .await
            .unwrap();

        // Plan SELECT *
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        let planner = Planner::new(db.clone(), &snapshot);

        let stmt = match Parser::new("SELECT * FROM test").parse().unwrap() {
            Some(crate::sql::Statement::Select(s)) => s,
            _ => panic!("expected SELECT"),
        };

        let plan = planner.plan_select(&stmt).await.unwrap();

        // Should be just a SeqScan (no projection needed for SELECT *)
        match plan {
            Plan::SeqScan { table_name, output_columns, .. } => {
                assert_eq!(table_name, "test");
                assert_eq!(output_columns.len(), 2);
                assert_eq!(output_columns[0].name, "id");
                assert_eq!(output_columns[1].name, "name");
            }
            _ => panic!("expected SeqScan"),
        }
    }

    #[tokio::test]
    async fn test_plan_select_columns() {
        let db = create_test_db().await;

        // Create table
        let mut session = crate::db::Session::new(db.clone());
        session
            .execute_query("CREATE TABLE test (id INT, name TEXT)")
            .await
            .unwrap();

        // Plan SELECT name FROM test
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        let planner = Planner::new(db.clone(), &snapshot);

        let stmt = match Parser::new("SELECT name FROM test").parse().unwrap() {
            Some(crate::sql::Statement::Select(s)) => s,
            _ => panic!("expected SELECT"),
        };

        let plan = planner.plan_select(&stmt).await.unwrap();

        // Should be Projection -> SeqScan
        match plan {
            Plan::Projection { output_columns, .. } => {
                assert_eq!(output_columns.len(), 1);
                assert_eq!(output_columns[0].name, "name");
            }
            _ => panic!("expected Projection"),
        }
    }

    #[tokio::test]
    async fn test_plan_select_where() {
        let db = create_test_db().await;

        // Create table
        let mut session = crate::db::Session::new(db.clone());
        session
            .execute_query("CREATE TABLE test (id INT, name TEXT)")
            .await
            .unwrap();

        // Plan SELECT * FROM test WHERE id > 5
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        let planner = Planner::new(db.clone(), &snapshot);

        let stmt = match Parser::new("SELECT * FROM test WHERE id > 5").parse().unwrap() {
            Some(crate::sql::Statement::Select(s)) => s,
            _ => panic!("expected SELECT"),
        };

        let plan = planner.plan_select(&stmt).await.unwrap();

        // Should be Filter -> SeqScan
        match plan {
            Plan::Filter { predicate, .. } => {
                // Verify predicate structure
                match predicate {
                    BoundExpr::BinaryOp { left, op, right } => {
                        assert!(matches!(*left, BoundExpr::Column(0)));
                        assert_eq!(op, crate::sql::BinaryOperator::Gt);
                        assert!(matches!(*right, BoundExpr::Integer(5)));
                    }
                    _ => panic!("expected binary op"),
                }
            }
            _ => panic!("expected Filter"),
        }
    }

    #[tokio::test]
    async fn test_plan_table_not_found() {
        let db = create_test_db().await;

        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        let planner = Planner::new(db.clone(), &snapshot);

        let stmt = match Parser::new("SELECT * FROM nonexistent").parse().unwrap() {
            Some(crate::sql::Statement::Select(s)) => s,
            _ => panic!("expected SELECT"),
        };

        let result = planner.plan_select(&stmt).await;
        assert!(matches!(
            result,
            Err(ExecutorError::TableNotFound { name }) if name == "nonexistent"
        ));
    }

    #[tokio::test]
    async fn test_plan_column_not_found() {
        let db = create_test_db().await;

        // Create table
        let mut session = crate::db::Session::new(db.clone());
        session
            .execute_query("CREATE TABLE test (id INT)")
            .await
            .unwrap();

        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        let planner = Planner::new(db.clone(), &snapshot);

        let stmt = match Parser::new("SELECT nonexistent FROM test").parse().unwrap() {
            Some(crate::sql::Statement::Select(s)) => s,
            _ => panic!("expected SELECT"),
        };

        let result = planner.plan_select(&stmt).await;
        assert!(matches!(
            result,
            Err(ExecutorError::ColumnNotFound { name }) if name == "nonexistent"
        ));
    }
}
