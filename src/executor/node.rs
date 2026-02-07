//! Executor nodes implementing the Volcano iterator model.
//!
//! Each node produces tuples one at a time via [`ExecutorNode::next()`].
//! Nodes are composed into a tree (e.g., Projection -> Filter -> SeqScan)
//! where each parent pulls tuples from its child.
//!
//! All nodes are generic over [`ExecContext`], which provides storage
//! operations. This keeps executor logic decoupled from concrete storage types.

use crate::datum::{Type, Value};
use crate::heap::Record;
use crate::storage::PageId;

use super::ColumnDesc;
use super::context::ExecContext;
use super::error::ExecutorError;
use super::expr::BoundExpr;
use super::plan::Plan;
use super::row::Row;

/// A query executor node.
///
/// Uses enum dispatch instead of `dyn Trait` to avoid boxing async methods.
/// This is sufficient since the number of node types is small and fixed.
///
/// Generic over [`ExecContext`] to decouple from concrete storage types.
pub enum ExecutorNode<C: ExecContext> {
    /// Sequential heap scan with lazy page loading.
    SeqScan(SeqScan<C>),
    /// Tuple filter (WHERE clause).
    Filter(Filter<C>),
    /// Column projection (SELECT list).
    Projection(Projection<C>),
    /// Single-row scan for queries without FROM (e.g., `SELECT 1+1`).
    ValuesScan(ValuesScan),
}

impl<C: ExecContext> ExecutorNode<C> {
    /// Converts a logical [`Plan`] into a physical `ExecutorNode` tree.
    ///
    /// This is a synchronous function — no I/O happens here. All storage access
    /// is deferred to [`ExecutorNode::next()`] via the [`ExecContext`].
    pub fn build(plan: Plan, ctx: &C) -> Self {
        match plan {
            Plan::SeqScan {
                table_name,
                first_page,
                schema,
                columns,
                ..
            } => ExecutorNode::SeqScan(SeqScan::new(
                table_name,
                columns,
                ctx.clone(),
                schema,
                first_page,
            )),
            Plan::Filter { input, predicate } => {
                let child = Self::build(*input, ctx);
                ExecutorNode::Filter(Filter::new(child, predicate))
            }
            Plan::Projection {
                input,
                exprs,
                columns,
            } => {
                let child = Self::build(*input, ctx);
                ExecutorNode::Projection(Projection::new(child, exprs, columns))
            }
            Plan::ValuesScan => ExecutorNode::ValuesScan(ValuesScan::new()),
        }
    }

    /// Returns the next tuple, or `None` if exhausted.
    ///
    /// This method follows the Volcano iterator model naming convention,
    /// not `std::iter::Iterator`, because it returns `Result<Option<_>>`.
    ///
    /// Uses `Pin<Box<...>>` to break the recursive future cycle
    /// (ExecutorNode -> Filter -> ExecutorNode).
    #[allow(clippy::should_implement_trait)]
    pub fn next(
        &mut self,
    ) -> std::pin::Pin<
        Box<dyn std::future::Future<Output = Result<Option<Row>, ExecutorError>> + Send + '_>,
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

/// Sequential scan node that lazily loads visible tuples page-by-page.
///
/// Tuples are loaded one page at a time via [`ExecContext::scan_heap_page`],
/// avoiding holding page latches across `next()` calls and keeping memory
/// usage proportional to a single page rather than the entire table.
///
/// NOTE: Multi-page support will read next_page from the page header here.
/// Currently only the first page is scanned.
pub struct SeqScan<C: ExecContext> {
    /// Table name (for identification).
    pub table_name: String,
    /// Column descriptors for the output.
    pub columns: Vec<ColumnDesc>,
    /// Execution context for page I/O.
    ctx: C,
    /// Column data types for record deserialization.
    schema: Vec<Type>,
    /// Next page to scan, or `None` if exhausted.
    next_page_id: Option<PageId>,
    /// Buffer of tuples from the current page (ownership-based, no clone).
    buffer: std::vec::IntoIter<Row>,
}

impl<C: ExecContext> SeqScan<C> {
    /// Creates a new SeqScan targeting a specific first page.
    pub fn new(
        table_name: String,
        columns: Vec<ColumnDesc>,
        ctx: C,
        schema: Vec<Type>,
        first_page: PageId,
    ) -> Self {
        Self {
            table_name,
            columns,
            ctx,
            schema,
            next_page_id: Some(first_page),
            buffer: Vec::new().into_iter(),
        }
    }

    /// Returns the next visible tuple, loading pages lazily as needed.
    async fn next(&mut self) -> Result<Option<Row>, ExecutorError> {
        loop {
            if let Some(tuple) = self.buffer.next() {
                return Ok(Some(tuple));
            }
            let page_id = match self.next_page_id.take() {
                Some(id) => id,
                None => return Ok(None),
            };
            let tuples = self.ctx.scan_heap_page(page_id, &self.schema).await?;
            // NOTE: Multi-page support will read next_page from page header here.
            self.buffer = tuples.into_iter();
        }
    }
}

/// Filter node that applies a predicate to each tuple from its child.
pub struct Filter<C: ExecContext> {
    /// Child node to pull tuples from.
    child: Box<ExecutorNode<C>>,
    /// Bound predicate expression (must evaluate to boolean).
    predicate: BoundExpr,
}

impl<C: ExecContext> Filter<C> {
    /// Creates a new Filter node.
    pub fn new(child: ExecutorNode<C>, predicate: BoundExpr) -> Self {
        Self {
            child: Box::new(child),
            predicate,
        }
    }

    /// Returns the next tuple that satisfies the predicate.
    async fn next(&mut self) -> Result<Option<Row>, ExecutorError> {
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
pub struct Projection<C: ExecContext> {
    /// Child node to pull tuples from.
    child: Box<ExecutorNode<C>>,
    /// Bound expressions to evaluate for each output column.
    exprs: Vec<BoundExpr>,
    /// Output column descriptors.
    columns: Vec<ColumnDesc>,
}

impl<C: ExecContext> Projection<C> {
    /// Creates a new Projection node.
    pub fn new(child: ExecutorNode<C>, exprs: Vec<BoundExpr>, columns: Vec<ColumnDesc>) -> Self {
        Self {
            child: Box::new(child),
            exprs,
            columns,
        }
    }

    /// Returns the next projected tuple.
    async fn next(&mut self) -> Result<Option<Row>, ExecutorError> {
        match self.child.next().await? {
            Some(tuple) => {
                let mut values = Vec::with_capacity(self.exprs.len());
                for expr in &self.exprs {
                    values.push(expr.evaluate(&tuple.record)?);
                }
                Ok(Some(Row::computed(Record::new(values))))
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
    async fn next(&mut self) -> Result<Option<Row>, ExecutorError> {
        if self.done {
            Ok(None)
        } else {
            self.done = true;
            Ok(Some(Row::computed(Record::new(vec![]))))
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::sql::BinaryOperator;

    /// Mock execution context for unit testing executor nodes without real storage.
    #[derive(Clone)]
    struct MockContext {
        /// Pages indexed by page number. Each page is a Vec of tuples.
        pages: Arc<Vec<Vec<Row>>>,
    }

    impl MockContext {
        /// Creates a mock context with a single page of tuples.
        fn single_page(tuples: Vec<Row>) -> Self {
            Self {
                pages: Arc::new(vec![tuples]),
            }
        }
    }

    impl ExecContext for MockContext {
        async fn scan_heap_page(
            &self,
            page_id: PageId,
            _schema: &[Type],
        ) -> Result<Vec<Row>, ExecutorError> {
            Ok(self
                .pages
                .get(page_id.page_num() as usize)
                .cloned()
                .unwrap_or_default())
        }
    }

    fn int_col(name: &str) -> ColumnDesc {
        ColumnDesc {
            name: name.to_string(),
            source: None,
            data_type: Type::Int8,
        }
    }

    fn make_tuples(rows: Vec<Vec<Value>>) -> Vec<Row> {
        rows.into_iter()
            .map(|values| Row::computed(Record::new(values)))
            .collect()
    }

    #[tokio::test]
    async fn test_seq_scan_lazy_loading() {
        let tuples = make_tuples(vec![
            vec![Value::Int64(1)],
            vec![Value::Int64(2)],
            vec![Value::Int64(3)],
        ]);
        let ctx = MockContext::single_page(tuples);
        let mut node = ExecutorNode::SeqScan(SeqScan::new(
            "test".to_string(),
            vec![int_col("id")],
            ctx,
            vec![Type::Int8],
            PageId::new(0),
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
        let ctx = MockContext::single_page(tuples);
        let scan = ExecutorNode::SeqScan(SeqScan::new(
            "test".to_string(),
            vec![int_col("id")],
            ctx,
            vec![Type::Int8],
            PageId::new(0),
        ));

        // Filter: $col0 > 2
        let predicate = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Column {
                index: 0,
                name: None,
            }),
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
        let ctx = MockContext::single_page(tuples);
        let scan = ExecutorNode::SeqScan(SeqScan::new(
            "test".to_string(),
            vec![
                int_col("id"),
                ColumnDesc {
                    name: "name".to_string(),
                    source: None,
                    data_type: Type::Text,
                },
            ],
            ctx,
            vec![Type::Int8, Type::Text],
            PageId::new(0),
        ));

        // Project: just the name column (index 1)
        let exprs = vec![BoundExpr::Column {
            index: 1,
            name: Some("name".into()),
        }];
        let out_cols = vec![ColumnDesc {
            name: "name".to_string(),
            source: None,
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
        let mut node: ExecutorNode<MockContext> = ExecutorNode::ValuesScan(ValuesScan::new());
        let tuple = node.next().await.unwrap().unwrap();
        assert!(tuple.record.values.is_empty());
        assert!(tuple.tid.is_none());
        assert!(node.next().await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_build_seq_scan() {
        let plan = Plan::SeqScan {
            table_name: "test".to_string(),
            table_id: 1,
            first_page: PageId::new(0),
            schema: vec![Type::Int8],
            columns: vec![int_col("id")],
        };

        let tuples = make_tuples(vec![vec![Value::Int64(10)], vec![Value::Int64(20)]]);
        let ctx = MockContext::single_page(tuples);
        let mut node = ExecutorNode::build(plan, &ctx);

        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Int64(10)]
        );
        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Int64(20)]
        );
        assert!(node.next().await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_build_filter() {
        let plan = Plan::Filter {
            input: Box::new(Plan::SeqScan {
                table_name: "test".to_string(),
                table_id: 1,
                first_page: PageId::new(0),
                schema: vec![Type::Int8],
                columns: vec![int_col("id")],
            }),
            predicate: BoundExpr::BinaryOp {
                left: Box::new(BoundExpr::Column {
                    index: 0,
                    name: None,
                }),
                op: BinaryOperator::Gt,
                right: Box::new(BoundExpr::Integer(2)),
            },
        };

        let tuples = make_tuples(vec![
            vec![Value::Int64(1)],
            vec![Value::Int64(2)],
            vec![Value::Int64(3)],
        ]);
        let ctx = MockContext::single_page(tuples);
        let mut node = ExecutorNode::build(plan, &ctx);

        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Int64(3)]
        );
        assert!(node.next().await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_build_projection() {
        let plan = Plan::Projection {
            input: Box::new(Plan::SeqScan {
                table_name: "test".to_string(),
                table_id: 1,
                first_page: PageId::new(0),
                schema: vec![Type::Int8, Type::Text],
                columns: vec![
                    int_col("id"),
                    ColumnDesc {
                        name: "name".to_string(),
                        source: None,
                        data_type: Type::Text,
                    },
                ],
            }),
            exprs: vec![BoundExpr::Column {
                index: 1,
                name: Some("name".into()),
            }],
            columns: vec![ColumnDesc {
                name: "name".to_string(),
                source: None,
                data_type: Type::Text,
            }],
        };

        let tuples = make_tuples(vec![
            vec![Value::Int64(1), Value::Text("alice".into())],
            vec![Value::Int64(2), Value::Text("bob".into())],
        ]);
        let ctx = MockContext::single_page(tuples);
        let mut node = ExecutorNode::build(plan, &ctx);

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
    async fn test_build_values_scan() {
        let plan = Plan::Projection {
            input: Box::new(Plan::ValuesScan),
            exprs: vec![BoundExpr::Integer(42)],
            columns: vec![int_col("?column?")],
        };

        let ctx = MockContext::single_page(vec![]);
        let mut node = ExecutorNode::build(plan, &ctx);

        let tuple = node.next().await.unwrap().unwrap();
        assert_eq!(tuple.record.values, vec![Value::Int64(42)]);
        assert!(node.next().await.unwrap().is_none());
    }
}
