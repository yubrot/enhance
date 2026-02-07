//! Executor nodes implementing the Volcano iterator model.
//!
//! Each node produces rows one at a time via [`ExecutorNode::next()`].
//! Nodes are composed into a tree (e.g., Projection -> Filter -> SeqScan)
//! where each parent pulls rows from its child.

use crate::datum::Value;
use crate::heap::Record;

use super::error::ExecutorError;
use super::eval::{format_bound_expr_with_columns, BoundExpr};
use super::types::{ColumnDesc, Row};

/// A query executor node.
///
/// Uses enum dispatch instead of `dyn Trait` to avoid boxing async methods.
/// This is sufficient since the number of node types is small and fixed.
pub enum ExecutorNode {
    /// Sequential heap scan with pre-loaded rows.
    SeqScan(SeqScan),
    /// Row filter (WHERE clause).
    Filter(Filter),
    /// Column projection (SELECT list).
    Projection(Projection),
    /// Single-row scan for queries without FROM (e.g., `SELECT 1+1`).
    ValuesScan(ValuesScan),
}

impl ExecutorNode {
    /// Returns the next row, or `None` if exhausted.
    ///
    /// This method follows the Volcano iterator model naming convention,
    /// not `std::iter::Iterator`, because it returns `Result<Option<_>>`.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Result<Option<Row>, ExecutorError> {
        match self {
            ExecutorNode::SeqScan(n) => n.next(),
            ExecutorNode::Filter(n) => n.next(),
            ExecutorNode::Projection(n) => n.next(),
            ExecutorNode::ValuesScan(n) => n.next(),
        }
    }

    /// Returns the column descriptors for this node's output.
    pub fn columns(&self) -> &[ColumnDesc] {
        match self {
            ExecutorNode::SeqScan(n) => &n.columns,
            ExecutorNode::Filter(n) => n.child.columns(),
            ExecutorNode::Projection(n) => &n.columns,
            ExecutorNode::ValuesScan(n) => &n.columns,
        }
    }

    /// Produces a human-readable EXPLAIN output for this node.
    pub fn explain(&self, indent: usize) -> String {
        let prefix = "  ".repeat(indent);
        match self {
            ExecutorNode::SeqScan(n) => {
                format!("{}SeqScan on {} ({} rows)", prefix, n.table_name, n.rows.len())
            }
            ExecutorNode::Filter(n) => {
                let child_columns = n.child.columns();
                let filter_str =
                    format_bound_expr_with_columns(&n.predicate, child_columns);
                let child_str = n.child.explain(indent + 1);
                format!("{}Filter: {}\n{}", prefix, filter_str, child_str)
            }
            ExecutorNode::Projection(n) => {
                let child_columns = n.child.columns();
                let cols: Vec<String> = n
                    .exprs
                    .iter()
                    .map(|e| format_bound_expr_with_columns(e, child_columns))
                    .collect();
                let child_str = n.child.explain(indent + 1);
                format!("{}Projection: {}\n{}", prefix, cols.join(", "), child_str)
            }
            ExecutorNode::ValuesScan(_) => {
                format!("{}ValuesScan (1 row)", prefix)
            }
        }
    }
}

/// Sequential scan node that pre-loads all visible tuples from a heap page.
///
/// Pre-loading avoids holding page latches across `next()` calls and
/// sidesteps lifetime issues with page guards.
pub struct SeqScan {
    /// Table name (for EXPLAIN output).
    pub table_name: String,
    /// Column descriptors for the output.
    pub columns: Vec<ColumnDesc>,
    /// Pre-loaded visible rows.
    pub rows: Vec<Row>,
    /// Current cursor position.
    cursor: usize,
}

impl SeqScan {
    /// Creates a new SeqScan with pre-loaded rows.
    pub fn new(table_name: String, columns: Vec<ColumnDesc>, rows: Vec<Row>) -> Self {
        Self {
            table_name,
            columns,
            rows,
            cursor: 0,
        }
    }

    /// Returns the next row.
    fn next(&mut self) -> Result<Option<Row>, ExecutorError> {
        if self.cursor < self.rows.len() {
            let row = self.rows[self.cursor].clone();
            self.cursor += 1;
            Ok(Some(row))
        } else {
            Ok(None)
        }
    }
}

/// Filter node that applies a predicate to each row from its child.
pub struct Filter {
    /// Child node to pull rows from.
    child: Box<ExecutorNode>,
    /// Bound predicate expression (must evaluate to boolean).
    predicate: BoundExpr,
}

impl Filter {
    /// Creates a new Filter node.
    pub fn new(child: ExecutorNode, predicate: BoundExpr) -> Self {
        Self {
            child: Box::new(child),
            predicate,
        }
    }

    /// Returns the next row that satisfies the predicate.
    fn next(&mut self) -> Result<Option<Row>, ExecutorError> {
        loop {
            match self.child.next()? {
                Some(row) => {
                    let result = self.predicate.evaluate(&Record::new(row.clone()))?;
                    if matches!(result, Value::Boolean(true)) {
                        return Ok(Some(row));
                    }
                    // NULL and false both skip the row
                }
                None => return Ok(None),
            }
        }
    }
}

/// Projection node that evaluates bound expressions to produce output columns.
pub struct Projection {
    /// Child node to pull rows from.
    child: Box<ExecutorNode>,
    /// Bound expressions to evaluate for each output column.
    exprs: Vec<BoundExpr>,
    /// Output column descriptors.
    columns: Vec<ColumnDesc>,
}

impl Projection {
    /// Creates a new Projection node.
    pub fn new(child: ExecutorNode, exprs: Vec<BoundExpr>, columns: Vec<ColumnDesc>) -> Self {
        Self {
            child: Box::new(child),
            exprs,
            columns,
        }
    }

    /// Returns the next projected row.
    fn next(&mut self) -> Result<Option<Row>, ExecutorError> {
        match self.child.next()? {
            Some(row) => {
                let record = Record::new(row);
                let mut result = Vec::with_capacity(self.exprs.len());
                for expr in &self.exprs {
                    result.push(expr.evaluate(&record)?);
                }
                Ok(Some(result))
            }
            None => Ok(None),
        }
    }
}

/// Values scan node for queries without a FROM clause.
///
/// Returns exactly one empty row, then `None`. This allows expressions
/// like `SELECT 1+1` to be evaluated via normal Projection.
pub struct ValuesScan {
    /// Output column descriptors (empty for no-FROM queries).
    columns: Vec<ColumnDesc>,
    /// Whether the single row has been returned.
    done: bool,
}

impl ValuesScan {
    /// Creates a new ValuesScan.
    pub fn new() -> Self {
        Self {
            columns: vec![],
            done: false,
        }
    }

    /// Returns the single empty row, then `None`.
    fn next(&mut self) -> Result<Option<Row>, ExecutorError> {
        if self.done {
            Ok(None)
        } else {
            self.done = true;
            Ok(Some(vec![]))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::datum::Type;
    use crate::sql::BinaryOperator;

    fn int_col(name: &str) -> ColumnDesc {
        ColumnDesc {
            name: name.to_string(),
            table_oid: 0,
            column_id: 0,
            data_type: Type::Int8,
        }
    }

    #[test]
    fn test_seq_scan_cursor() {
        let rows = vec![
            vec![Value::Int64(1)],
            vec![Value::Int64(2)],
            vec![Value::Int64(3)],
        ];
        let mut node = ExecutorNode::SeqScan(SeqScan::new(
            "test".to_string(),
            vec![int_col("id")],
            rows,
        ));

        assert_eq!(node.next().unwrap(), Some(vec![Value::Int64(1)]));
        assert_eq!(node.next().unwrap(), Some(vec![Value::Int64(2)]));
        assert_eq!(node.next().unwrap(), Some(vec![Value::Int64(3)]));
        assert_eq!(node.next().unwrap(), None);
        assert_eq!(node.next().unwrap(), None); // Idempotent
    }

    #[test]
    fn test_filter_predicate() {
        let rows = vec![
            vec![Value::Int64(1)],
            vec![Value::Int64(2)],
            vec![Value::Int64(3)],
            vec![Value::Int64(4)],
        ];
        let scan = ExecutorNode::SeqScan(SeqScan::new(
            "test".to_string(),
            vec![int_col("id")],
            rows,
        ));

        // Filter: $col0 > 2
        let predicate = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Column(0)),
            op: BinaryOperator::Gt,
            right: Box::new(BoundExpr::Integer(2)),
        };
        let mut node = ExecutorNode::Filter(Filter::new(scan, predicate));

        assert_eq!(node.next().unwrap(), Some(vec![Value::Int64(3)]));
        assert_eq!(node.next().unwrap(), Some(vec![Value::Int64(4)]));
        assert_eq!(node.next().unwrap(), None);
    }

    #[test]
    fn test_projection() {
        let rows = vec![
            vec![Value::Int64(1), Value::Text("alice".into())],
            vec![Value::Int64(2), Value::Text("bob".into())],
        ];
        let scan = ExecutorNode::SeqScan(SeqScan::new(
            "test".to_string(),
            vec![
                int_col("id"),
                ColumnDesc {
                    name: "name".to_string(),
                    table_oid: 0,
                    column_id: 0,
                    data_type: Type::Text,
                },
            ],
            rows,
        ));

        // Project: just the name column (index 1)
        let exprs = vec![BoundExpr::Column(1)];
        let out_cols = vec![ColumnDesc {
            name: "name".to_string(),
            table_oid: 0,
            column_id: 0,
            data_type: Type::Text,
        }];
        let mut node = ExecutorNode::Projection(Projection::new(scan, exprs, out_cols));

        assert_eq!(
            node.next().unwrap(),
            Some(vec![Value::Text("alice".into())])
        );
        assert_eq!(
            node.next().unwrap(),
            Some(vec![Value::Text("bob".into())])
        );
        assert_eq!(node.next().unwrap(), None);
    }

    #[test]
    fn test_values_scan() {
        let mut node = ExecutorNode::ValuesScan(ValuesScan::new());
        assert_eq!(node.next().unwrap(), Some(vec![]));
        assert_eq!(node.next().unwrap(), None);
    }

    #[test]
    fn test_explain_output() {
        let scan = ExecutorNode::SeqScan(SeqScan::new(
            "users".to_string(),
            vec![int_col("id")],
            vec![vec![Value::Int64(1)], vec![Value::Int64(2)]],
        ));

        let filter = ExecutorNode::Filter(Filter::new(
            scan,
            BoundExpr::BinaryOp {
                left: Box::new(BoundExpr::Column(0)),
                op: BinaryOperator::Gt,
                right: Box::new(BoundExpr::Integer(1)),
            },
        ));

        let explain = filter.explain(0);
        assert!(explain.contains("Filter:"));
        assert!(explain.contains("SeqScan on users"));
    }
}
