//! Executor nodes implementing the Volcano iterator model.
//!
//! Each node produces tuples one at a time via [`ExecutorNode::next()`].
//! Nodes are composed into a tree (e.g., Projection -> Filter -> SeqScan)
//! where each parent pulls tuples from its child.

use crate::datum::Value;
use crate::heap::Record;

use crate::heap::Tuple;

use super::error::ExecutorError;
use super::eval::BoundExpr;
use super::ColumnDesc;

/// A query executor node.
///
/// Uses enum dispatch instead of `dyn Trait` to avoid boxing async methods.
/// This is sufficient since the number of node types is small and fixed.
pub enum ExecutorNode {
    /// Sequential heap scan with pre-loaded tuples.
    SeqScan(SeqScan),
    /// Tuple filter (WHERE clause).
    Filter(Filter),
    /// Column projection (SELECT list).
    Projection(Projection),
    /// Single-row scan for queries without FROM (e.g., `SELECT 1+1`).
    ValuesScan(ValuesScan),
}

impl ExecutorNode {
    /// Returns the next tuple, or `None` if exhausted.
    ///
    /// This method follows the Volcano iterator model naming convention,
    /// not `std::iter::Iterator`, because it returns `Result<Option<_>>`.
    /// The async signature prepares for future page-level streaming where
    /// SeqScan would fetch pages lazily.
    ///
    /// Uses `Pin<Box<...>>` to break the recursive future cycle
    /// (ExecutorNode -> Filter -> ExecutorNode).
    #[allow(clippy::should_implement_trait)]
    pub fn next(
        &mut self,
    ) -> std::pin::Pin<
        Box<dyn std::future::Future<Output = Result<Option<Tuple>, ExecutorError>> + Send + '_>,
    > {
        Box::pin(async move {
            match self {
                ExecutorNode::SeqScan(n) => n.next().await,
                ExecutorNode::Filter(n) => n.next().await,
                ExecutorNode::Projection(n) => n.next().await,
                ExecutorNode::ValuesScan(n) => n.next().await,
            }
        })
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
}

/// Sequential scan node that pre-loads all visible tuples from a heap page.
///
/// Pre-loading avoids holding page latches across `next()` calls and
/// sidesteps lifetime issues with page guards.
///
/// NOTE: For future streaming, this node would accept a `HeapScanner`
/// instead of a pre-loaded `Vec`, fetching pages lazily via `next().await`.
pub struct SeqScan {
    /// Table name (for identification).
    pub table_name: String,
    /// Column descriptors for the output.
    pub columns: Vec<ColumnDesc>,
    /// Pre-loaded visible tuples.
    pub tuples: Vec<Tuple>,
    /// Current cursor position.
    cursor: usize,
}

impl SeqScan {
    /// Creates a new SeqScan with pre-loaded tuples.
    pub fn new(table_name: String, columns: Vec<ColumnDesc>, tuples: Vec<Tuple>) -> Self {
        Self {
            table_name,
            columns,
            tuples,
            cursor: 0,
        }
    }

    /// Returns the next tuple.
    async fn next(&mut self) -> Result<Option<Tuple>, ExecutorError> {
        if self.cursor < self.tuples.len() {
            let tuple = self.tuples[self.cursor].clone();
            self.cursor += 1;
            Ok(Some(tuple))
        } else {
            Ok(None)
        }
    }
}

/// Filter node that applies a predicate to each tuple from its child.
pub struct Filter {
    /// Child node to pull tuples from.
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

    /// Returns the next tuple that satisfies the predicate.
    async fn next(&mut self) -> Result<Option<Tuple>, ExecutorError> {
        loop {
            match self.child.next().await? {
                Some(tuple) => {
                    let result = self.predicate.evaluate(&tuple.record)?;
                    if matches!(result, Value::Boolean(true)) {
                        return Ok(Some(tuple));
                    }
                    // NULL and false both skip the tuple
                }
                None => return Ok(None),
            }
        }
    }
}

/// Projection node that evaluates bound expressions to produce output columns.
pub struct Projection {
    /// Child node to pull tuples from.
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

    /// Returns the next projected tuple.
    async fn next(&mut self) -> Result<Option<Tuple>, ExecutorError> {
        match self.child.next().await? {
            Some(tuple) => {
                let mut values = Vec::with_capacity(self.exprs.len());
                for expr in &self.exprs {
                    values.push(expr.evaluate(&tuple.record)?);
                }
                Ok(Some(Tuple::computed(Record::new(values))))
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

    /// Returns the single empty tuple, then `None`.
    async fn next(&mut self) -> Result<Option<Tuple>, ExecutorError> {
        if self.done {
            Ok(None)
        } else {
            self.done = true;
            Ok(Some(Tuple::computed(Record::new(vec![]))))
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

    fn make_tuples(rows: Vec<Vec<Value>>) -> Vec<Tuple> {
        rows.into_iter()
            .map(|values| Tuple::computed(Record::new(values)))
            .collect()
    }

    #[tokio::test]
    async fn test_seq_scan_cursor() {
        let tuples = make_tuples(vec![
            vec![Value::Int64(1)],
            vec![Value::Int64(2)],
            vec![Value::Int64(3)],
        ]);
        let mut node = ExecutorNode::SeqScan(SeqScan::new(
            "test".to_string(),
            vec![int_col("id")],
            tuples,
        ));

        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Int64(1)]
        );
        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Int64(2)]
        );
        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Int64(3)]
        );
        assert!(node.next().await.unwrap().is_none());
        assert!(node.next().await.unwrap().is_none()); // Idempotent
    }

    #[tokio::test]
    async fn test_filter_predicate() {
        let tuples = make_tuples(vec![
            vec![Value::Int64(1)],
            vec![Value::Int64(2)],
            vec![Value::Int64(3)],
            vec![Value::Int64(4)],
        ]);
        let scan = ExecutorNode::SeqScan(SeqScan::new(
            "test".to_string(),
            vec![int_col("id")],
            tuples,
        ));

        // Filter: $col0 > 2
        let predicate = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Column(0)),
            op: BinaryOperator::Gt,
            right: Box::new(BoundExpr::Integer(2)),
        };
        let mut node = ExecutorNode::Filter(Filter::new(scan, predicate));

        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Int64(3)]
        );
        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Int64(4)]
        );
        assert!(node.next().await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_projection() {
        let tuples = make_tuples(vec![
            vec![Value::Int64(1), Value::Text("alice".into())],
            vec![Value::Int64(2), Value::Text("bob".into())],
        ]);
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
            tuples,
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
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Text("alice".into())]
        );
        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Text("bob".into())]
        );
        assert!(node.next().await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_values_scan() {
        let mut node = ExecutorNode::ValuesScan(ValuesScan::new());
        let tuple = node.next().await.unwrap().unwrap();
        assert!(tuple.record.values.is_empty());
        assert!(tuple.tid.is_none());
        assert!(node.next().await.unwrap().is_none());
    }
}
