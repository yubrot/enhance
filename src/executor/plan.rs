//! Plan nodes for query execution.
//!
//! This module implements the Volcano-style iterator model where each plan node
//! provides a `next()` method that returns one tuple at a time.

use std::sync::Arc;

use async_trait::async_trait;

use crate::catalog::ColumnInfo;
use crate::executor::value::{evaluate, is_truthy};
use crate::executor::ExecutorError;
use crate::heap::{HeapPage, Value};
use crate::sql::Expr;
use crate::storage::{BufferPool, PageId, Replacer, Storage};
use crate::tx::{Snapshot, TransactionManager};

/// Output column metadata for executor results.
#[derive(Debug, Clone)]
pub struct OutputColumn {
    /// Column name (may be alias or generated).
    pub name: String,
    /// PostgreSQL type OID.
    pub type_oid: i32,
}

impl OutputColumn {
    /// Creates a new output column.
    pub fn new(name: String, type_oid: i32) -> Self {
        Self { name, type_oid }
    }
}

/// A tuple of values produced by an executor.
#[derive(Debug, Clone)]
pub struct Tuple {
    /// The values in this tuple.
    pub values: Vec<Value>,
}

impl Tuple {
    /// Creates a new tuple with the given values.
    pub fn new(values: Vec<Value>) -> Self {
        Self { values }
    }
}

/// The Executor trait defines the Volcano-style iterator interface.
///
/// Each executor produces tuples one at a time via `next()`.
#[async_trait]
pub trait Executor: Send {
    /// Returns the next tuple, or None if exhausted.
    async fn next(&mut self) -> Result<Option<Tuple>, ExecutorError>;

    /// Returns output column metadata.
    fn schema(&self) -> &[OutputColumn];

    /// Returns EXPLAIN text for this operator.
    fn explain(&self, indent: usize) -> String;
}

/// Sequential scan of a heap table.
///
/// Iterates through all tuples in a table's heap page(s) with MVCC visibility checks.
pub struct SeqScan<S: Storage, R: Replacer> {
    /// Table name for EXPLAIN output.
    table_name: String,
    /// Output column metadata.
    output_columns: Vec<OutputColumn>,
    /// Column info from catalog (for expression evaluation).
    columns: Vec<ColumnInfo>,
    /// Type OIDs for record deserialization.
    schema: Vec<i32>,
    /// First page of the table.
    first_page: PageId,
    /// MVCC snapshot.
    snapshot: Snapshot,
    /// Buffer pool reference.
    pool: Arc<BufferPool<S, R>>,
    /// Transaction manager reference.
    tx_manager: Arc<TransactionManager>,
    /// Current position: (page_loaded, slot_index).
    /// When page_loaded is false, we haven't loaded the page yet.
    state: ScanState,
    /// Loaded tuples from current page (with visibility already checked).
    buffer: Vec<Tuple>,
    /// Current index into buffer.
    buffer_idx: usize,
}

enum ScanState {
    /// Haven't started scanning yet.
    NotStarted,
    /// Currently scanning a page.
    Scanning,
    /// Finished scanning all pages.
    Finished,
}

impl<S: Storage, R: Replacer> SeqScan<S, R> {
    /// Creates a new sequential scan executor.
    pub fn new(
        table_name: String,
        columns: Vec<ColumnInfo>,
        first_page: PageId,
        snapshot: Snapshot,
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
    ) -> Self {
        let output_columns: Vec<OutputColumn> = columns
            .iter()
            .map(|c| OutputColumn::new(c.column_name.clone(), c.type_oid))
            .collect();
        let schema: Vec<i32> = columns.iter().map(|c| c.type_oid).collect();

        Self {
            table_name,
            output_columns,
            columns,
            schema,
            first_page,
            snapshot,
            pool,
            tx_manager,
            state: ScanState::NotStarted,
            buffer: Vec::new(),
            buffer_idx: 0,
        }
    }

    /// Returns the columns info for expression evaluation.
    pub fn columns(&self) -> &[ColumnInfo] {
        &self.columns
    }

    /// Loads all visible tuples from the current page into the buffer.
    async fn load_page(&mut self) -> Result<(), ExecutorError> {
        let guard = self.pool.fetch_page(self.first_page).await?;
        let page = HeapPage::new(guard.data());

        self.buffer.clear();
        self.buffer_idx = 0;

        for (_slot_id, header, record) in page.scan(&self.schema) {
            if self.snapshot.is_tuple_visible(&header, &self.tx_manager) {
                self.buffer.push(Tuple::new(record.values));
            }
        }

        Ok(())
    }
}

#[async_trait]
impl<S: Storage, R: Replacer> Executor for SeqScan<S, R> {
    async fn next(&mut self) -> Result<Option<Tuple>, ExecutorError> {
        loop {
            match self.state {
                ScanState::NotStarted => {
                    self.load_page().await?;
                    self.state = ScanState::Scanning;
                }
                ScanState::Scanning => {
                    if self.buffer_idx < self.buffer.len() {
                        let tuple = self.buffer[self.buffer_idx].clone();
                        self.buffer_idx += 1;
                        return Ok(Some(tuple));
                    }
                    // NOTE: Multi-page tables will be supported in Step 15 (FSM).
                    // For now, tables are limited to a single page.
                    self.state = ScanState::Finished;
                }
                ScanState::Finished => {
                    return Ok(None);
                }
            }
        }
    }

    fn schema(&self) -> &[OutputColumn] {
        &self.output_columns
    }

    fn explain(&self, indent: usize) -> String {
        format!("{}Seq Scan on {}", " ".repeat(indent), self.table_name)
    }
}

/// Filter executor that applies a WHERE predicate.
///
/// Wraps a child executor and only passes through tuples where the predicate
/// evaluates to TRUE.
pub struct Filter<E: Executor> {
    /// Child executor.
    child: E,
    /// Column info for expression evaluation.
    columns: Vec<ColumnInfo>,
    /// Filter predicate.
    predicate: Expr,
}

impl<E: Executor> Filter<E> {
    /// Creates a new filter executor.
    pub fn new(child: E, columns: Vec<ColumnInfo>, predicate: Expr) -> Self {
        Self {
            child,
            columns,
            predicate,
        }
    }
}

#[async_trait]
impl<E: Executor> Executor for Filter<E> {
    async fn next(&mut self) -> Result<Option<Tuple>, ExecutorError> {
        loop {
            match self.child.next().await? {
                Some(tuple) => {
                    let result = evaluate(&self.predicate, &tuple.values, &self.columns)?;
                    if is_truthy(&result) {
                        return Ok(Some(tuple));
                    }
                    // Tuple filtered out, continue to next
                }
                None => return Ok(None),
            }
        }
    }

    fn schema(&self) -> &[OutputColumn] {
        self.child.schema()
    }

    fn explain(&self, indent: usize) -> String {
        let filter_str = format_expr(&self.predicate);
        format!(
            "{}Filter: {}\n{}",
            " ".repeat(indent),
            filter_str,
            self.child.explain(indent + 2)
        )
    }
}

/// Projection executor that computes output columns from expressions.
pub struct Projection<E: Executor> {
    /// Child executor.
    child: E,
    /// Column info for expression evaluation.
    columns: Vec<ColumnInfo>,
    /// Output column definitions (expression + alias).
    output_exprs: Vec<(Expr, String)>,
    /// Output column metadata.
    output_columns: Vec<OutputColumn>,
}

impl<E: Executor> Projection<E> {
    /// Creates a new projection executor.
    pub fn new(
        child: E,
        columns: Vec<ColumnInfo>,
        output_exprs: Vec<(Expr, String)>,
        output_columns: Vec<OutputColumn>,
    ) -> Self {
        Self {
            child,
            columns,
            output_exprs,
            output_columns,
        }
    }
}

#[async_trait]
impl<E: Executor> Executor for Projection<E> {
    async fn next(&mut self) -> Result<Option<Tuple>, ExecutorError> {
        match self.child.next().await? {
            Some(tuple) => {
                let mut output_values = Vec::with_capacity(self.output_exprs.len());
                for (expr, _alias) in &self.output_exprs {
                    let val = evaluate(expr, &tuple.values, &self.columns)?;
                    output_values.push(val);
                }
                Ok(Some(Tuple::new(output_values)))
            }
            None => Ok(None),
        }
    }

    fn schema(&self) -> &[OutputColumn] {
        &self.output_columns
    }

    fn explain(&self, indent: usize) -> String {
        // For SELECT *, don't add explicit Projection in EXPLAIN
        // For other projections, show the column list
        self.child.explain(indent)
    }
}

/// Formats an expression for EXPLAIN output.
fn format_expr(expr: &Expr) -> String {
    match expr {
        Expr::Null => "NULL".to_string(),
        Expr::Boolean(b) => b.to_string().to_uppercase(),
        Expr::Integer(n) => n.to_string(),
        Expr::Float(f) => f.to_string(),
        Expr::String(s) => format!("'{}'", s.replace('\'', "''")),
        Expr::ColumnRef { table, column } => {
            if let Some(t) = table {
                format!("{}.{}", t, column)
            } else {
                column.clone()
            }
        }
        Expr::Parameter(n) => format!("${}", n),
        Expr::BinaryOp { left, op, right } => {
            format!(
                "({} {} {})",
                format_expr(left),
                op.as_str(),
                format_expr(right)
            )
        }
        Expr::UnaryOp { op, operand } => {
            format!("{} {}", op.as_str(), format_expr(operand))
        }
        Expr::IsNull { expr, negated } => {
            if *negated {
                format!("({} IS NOT NULL)", format_expr(expr))
            } else {
                format!("({} IS NULL)", format_expr(expr))
            }
        }
        Expr::Between {
            expr,
            low,
            high,
            negated,
        } => {
            if *negated {
                format!(
                    "({} NOT BETWEEN {} AND {})",
                    format_expr(expr),
                    format_expr(low),
                    format_expr(high)
                )
            } else {
                format!(
                    "({} BETWEEN {} AND {})",
                    format_expr(expr),
                    format_expr(low),
                    format_expr(high)
                )
            }
        }
        Expr::InList {
            expr,
            list,
            negated,
        } => {
            let items: Vec<String> = list.iter().map(format_expr).collect();
            if *negated {
                format!("({} NOT IN ({}))", format_expr(expr), items.join(", "))
            } else {
                format!("({} IN ({}))", format_expr(expr), items.join(", "))
            }
        }
        _ => "<expr>".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_output_column() {
        let col = OutputColumn::new("id".to_string(), 23);
        assert_eq!(col.name, "id");
        assert_eq!(col.type_oid, 23);
    }

    #[test]
    fn test_tuple() {
        let tuple = Tuple::new(vec![Value::Int32(1), Value::Text("Alice".to_string())]);
        assert_eq!(tuple.values.len(), 2);
        assert_eq!(tuple.values[0], Value::Int32(1));
    }

    #[test]
    fn test_format_expr() {
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::ColumnRef {
                table: None,
                column: "id".to_string(),
            }),
            op: crate::sql::BinaryOperator::Gt,
            right: Box::new(Expr::Integer(5)),
        };
        assert_eq!(format_expr(&expr), "(id > 5)");
    }

    #[test]
    fn test_format_expr_is_null() {
        let expr = Expr::IsNull {
            expr: Box::new(Expr::ColumnRef {
                table: None,
                column: "name".to_string(),
            }),
            negated: false,
        };
        assert_eq!(format_expr(&expr), "(name IS NULL)");

        let expr = Expr::IsNull {
            expr: Box::new(Expr::ColumnRef {
                table: None,
                column: "name".to_string(),
            }),
            negated: true,
        };
        assert_eq!(format_expr(&expr), "(name IS NOT NULL)");
    }
}
