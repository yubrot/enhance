//! Executor nodes implementing the Volcano iterator model.
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

impl Plan {
    /// Converts a logical [`Plan`] into a physical [`ExecutorNode`] tree.
    ///
    /// This is a synchronous function — no I/O happens here. All storage access
    /// is deferred to [`ExecutorNode::next()`] via the [`ExecContext`].
    pub fn prepare_for_execute<C: ExecContext>(self, ctx: &C) -> ExecutorNode<C> {
        match self {
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
                ExecutorNode::Filter(Filter::new(input.prepare_for_execute(ctx), predicate))
            }
            Plan::Projection {
                input,
                exprs,
                columns,
            } => ExecutorNode::Projection(Projection::new(
                input.prepare_for_execute(ctx),
                exprs,
                columns,
            )),
            Plan::ValuesScan => ExecutorNode::ValuesScan(ValuesScan::new()),
            // DML plans are executed via execute_dml(), not prepare_for_execute()
            Plan::Insert { .. } => {
                unreachable!("DML plans should not be converted to executor nodes via prepare_for_execute")
            }
        }
    }
}

impl<C: ExecContext> ExecutorNode<C> {
    /// Returns the next tuple, or `None` if exhausted.
    ///
    /// This method follows the Volcano iterator model naming convention,
    /// not `std::iter::Iterator`, because it returns `Result<Option<_>>`.
    ///
    /// Uses `Pin<Box<...>>` to break the recursive future cycle
    /// (ExecutorNode -> Filter -> ExecutorNode).
    ///
    /// NOTE: Each call heap-allocates a `Box<dyn Future>`. For large scans
    /// (Sort/Aggregate in Step 12), this per-row overhead may be significant.
    /// Consider enum-based future dispatch or manual state machines if profiling
    /// identifies this as a bottleneck.
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
/// The scan follows the heap page chain via `HeapPage::next_page()` linkage,
/// advancing through all pages until the chain is exhausted.
pub struct SeqScan<C: ExecContext> {
    /// Table name (for identification).
    pub table_name: String,
    /// Column descriptors for the output.
    pub columns: Vec<ColumnDesc>,
    /// Execution context for page I/O.
    ctx: C,
    /// Column types for record deserialization.
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
    ///
    /// Follows the heap page chain automatically: when a page is exhausted,
    /// advances to the next page via the chain linkage.
    async fn next(&mut self) -> Result<Option<Row>, ExecutorError> {
        loop {
            if let Some(tuple) = self.buffer.next() {
                return Ok(Some(tuple));
            }
            let page_id = match self.next_page_id.take() {
                Some(id) => id,
                None => return Ok(None),
            };
            let (tuples, next_page) =
                self.ctx.scan_heap_page(page_id, &self.schema).await?;
            self.next_page_id = next_page;
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
    ///
    /// NOTE: Allocates a new Vec and Record per row. For production, consider
    /// arena allocation or a reusable row buffer to reduce GC pressure on
    /// large result sets.
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
    use super::*;
    use crate::datum::{Type, Value};
    use crate::db::Database;
    use crate::executor::ExecContextImpl;
    use crate::heap::{HeapPage, Record};
    use crate::sql::{Parser, Statement};
    use crate::storage::{LruReplacer, MemoryStorage, PageId};
    use crate::tx::CommandId;

    type TestCtx = ExecContextImpl<MemoryStorage, LruReplacer>;
    type TestDb = Database<MemoryStorage, LruReplacer>;

    /// Creates a test database with `CREATE TABLE test (id INT)` and inserts
    /// the given values via direct heap page writes. Returns the database
    /// and the table's first page ID.
    async fn setup_int_table(values: Vec<i64>) -> (TestDb, PageId) {
        let db = Database::open(MemoryStorage::new(), 100).await.unwrap();

        let txid = db.tx_manager().begin();
        let cid = CommandId::FIRST;
        let Statement::CreateTable(stmt) = Parser::new("CREATE TABLE test (id INT)")
            .parse()
            .unwrap()
            .unwrap()
        else {
            panic!("expected CreateTable");
        };
        db.catalog().create_table(txid, cid, &stmt).await.unwrap();
        db.tx_manager().commit(txid).unwrap();

        let txid = db.tx_manager().begin();
        let cid = CommandId::FIRST;
        let snapshot = db.tx_manager().snapshot(txid, cid);
        let table = db
            .catalog()
            .get_table(&snapshot, "test")
            .await
            .unwrap()
            .unwrap();
        let first_page = table.first_page;
        {
            let page = db.pool().fetch_page_mut(first_page, true).await.unwrap();
            let mut heap = HeapPage::new(page);
            for v in values {
                heap.insert(&Record::new(vec![Value::Bigint(v)]), txid, cid)
                    .unwrap();
            }
        }
        db.tx_manager().commit(txid).unwrap();

        (db, first_page)
    }

    /// Creates a test database with `CREATE TABLE test (id INT, name TEXT)` and
    /// inserts the given rows. Returns the database and the table's first page ID.
    async fn setup_two_col_table(rows: Vec<(i64, &str)>) -> (TestDb, PageId) {
        let db = Database::open(MemoryStorage::new(), 100).await.unwrap();

        let txid = db.tx_manager().begin();
        let cid = CommandId::FIRST;
        let Statement::CreateTable(stmt) = Parser::new("CREATE TABLE test (id INT, name TEXT)")
            .parse()
            .unwrap()
            .unwrap()
        else {
            panic!("expected CreateTable");
        };
        db.catalog().create_table(txid, cid, &stmt).await.unwrap();
        db.tx_manager().commit(txid).unwrap();

        let txid = db.tx_manager().begin();
        let cid = CommandId::FIRST;
        let snapshot = db.tx_manager().snapshot(txid, cid);
        let table = db
            .catalog()
            .get_table(&snapshot, "test")
            .await
            .unwrap()
            .unwrap();
        let first_page = table.first_page;
        {
            let page = db.pool().fetch_page_mut(first_page, true).await.unwrap();
            let mut heap = HeapPage::new(page);
            for (id, name) in rows {
                let record = Record::new(vec![Value::Bigint(id), Value::Text(name.into())]);
                heap.insert(&record, txid, cid).unwrap();
            }
        }
        db.tx_manager().commit(txid).unwrap();

        (db, first_page)
    }

    /// Creates an ExecContext from a database with a fresh read-only snapshot.
    fn read_ctx(db: &TestDb) -> TestCtx {
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        db.exec_context(snapshot)
    }

    fn int_col(name: &str) -> ColumnDesc {
        ColumnDesc {
            name: name.to_string(),
            source: None,
            ty: Type::Bigint,
        }
    }

    /// Parses and binds a SQL expression against the given column descriptors.
    fn bind_expr(sql: &str, columns: &[ColumnDesc]) -> BoundExpr {
        Parser::new(sql)
            .parse_expr()
            .expect("parse error")
            .bind(columns)
            .expect("bind error")
    }

    #[tokio::test]
    async fn test_seq_scan_lazy_loading() {
        let (db, first_page) = setup_int_table(vec![1, 2, 3]).await;
        let ctx = read_ctx(&db);
        let mut node = ExecutorNode::SeqScan(SeqScan::new(
            "test".to_string(),
            vec![int_col("id")],
            ctx,
            vec![Type::Bigint],
            first_page,
        ));

        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Bigint(1)]
        );
        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Bigint(2)]
        );
        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Bigint(3)]
        );
        assert!(node.next().await.unwrap().is_none());
        assert!(node.next().await.unwrap().is_none()); // Idempotent
    }

    #[tokio::test]
    async fn test_filter_predicate() {
        let (db, first_page) = setup_int_table(vec![1, 2, 3, 4]).await;
        let ctx = read_ctx(&db);
        let scan = ExecutorNode::SeqScan(SeqScan::new(
            "test".to_string(),
            vec![int_col("id")],
            ctx,
            vec![Type::Bigint],
            first_page,
        ));

        // Filter: id > 2
        let predicate = bind_expr("id > 2", &[int_col("id")]);
        let mut node = ExecutorNode::Filter(Filter::new(scan, predicate));

        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Bigint(3)]
        );
        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Bigint(4)]
        );
        assert!(node.next().await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_filter_null_predicate_skips_row() {
        let (db, first_page) = setup_int_table(vec![1, 2, 3]).await;
        let ctx = read_ctx(&db);
        let scan = ExecutorNode::SeqScan(SeqScan::new(
            "test".to_string(),
            vec![int_col("id")],
            ctx,
            vec![Type::Bigint],
            first_page,
        ));

        // Predicate that always evaluates to NULL: id = NULL
        // NULL comparisons return NULL, which Filter must skip (not treat as true)
        let predicate = bind_expr("id = NULL", &[int_col("id")]);
        let mut node = ExecutorNode::Filter(Filter::new(scan, predicate));

        // All rows should be skipped because NULL is not true
        assert!(node.next().await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_projection() {
        let (db, first_page) = setup_two_col_table(vec![(1, "alice"), (2, "bob")]).await;
        let ctx = read_ctx(&db);
        let scan = ExecutorNode::SeqScan(SeqScan::new(
            "test".to_string(),
            vec![
                int_col("id"),
                ColumnDesc {
                    name: "name".to_string(),
                    source: None,
                    ty: Type::Text,
                },
            ],
            ctx,
            vec![Type::Bigint, Type::Text],
            first_page,
        ));

        // Project: just the name column (index 1)
        let exprs = vec![bind_expr("name", &[int_col("id"), int_col("name")])];
        let out_cols = vec![ColumnDesc {
            name: "name".to_string(),
            source: None,
            ty: Type::Text,
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
        let mut node: ExecutorNode<TestCtx> = ExecutorNode::ValuesScan(ValuesScan::new());
        let tuple = node.next().await.unwrap().unwrap();
        assert!(tuple.record.values.is_empty());
        assert!(tuple.tid.is_none());
        assert!(node.next().await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_build_seq_scan() {
        let (db, first_page) = setup_int_table(vec![10, 20]).await;
        let ctx = read_ctx(&db);

        let plan = Plan::SeqScan {
            table_name: "test".to_string(),
            table_id: 1,
            first_page,
            schema: vec![Type::Bigint],
            columns: vec![int_col("id")],
        };

        let mut node = plan.prepare_for_execute(&ctx);

        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Bigint(10)]
        );
        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Bigint(20)]
        );
        assert!(node.next().await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_build_filter() {
        let (db, first_page) = setup_int_table(vec![1, 2, 3]).await;
        let ctx = read_ctx(&db);

        let plan = Plan::Filter {
            input: Box::new(Plan::SeqScan {
                table_name: "test".to_string(),
                table_id: 1,
                first_page,
                schema: vec![Type::Bigint],
                columns: vec![int_col("id")],
            }),
            predicate: bind_expr("id > 2", &[int_col("id")]),
        };

        let mut node = plan.prepare_for_execute(&ctx);

        assert_eq!(
            node.next().await.unwrap().unwrap().record.values,
            vec![Value::Bigint(3)]
        );
        assert!(node.next().await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_build_projection() {
        let (db, first_page) = setup_two_col_table(vec![(1, "alice"), (2, "bob")]).await;
        let ctx = read_ctx(&db);

        let plan = Plan::Projection {
            input: Box::new(Plan::SeqScan {
                table_name: "test".to_string(),
                table_id: 1,
                first_page,
                schema: vec![Type::Bigint, Type::Text],
                columns: vec![
                    int_col("id"),
                    ColumnDesc {
                        name: "name".to_string(),
                        source: None,
                        ty: Type::Text,
                    },
                ],
            }),
            exprs: vec![bind_expr("name", &[int_col("id"), int_col("name")])],
            columns: vec![ColumnDesc {
                name: "name".to_string(),
                source: None,
                ty: Type::Text,
            }],
        };

        let mut node = plan.prepare_for_execute(&ctx);

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
        let db = Database::open(MemoryStorage::new(), 100).await.unwrap();
        let ctx = read_ctx(&db);

        let plan = Plan::Projection {
            input: Box::new(Plan::ValuesScan),
            exprs: vec![bind_expr("42", &[])],
            columns: vec![int_col("?column?")],
        };

        let mut node = plan.prepare_for_execute(&ctx);

        let tuple = node.next().await.unwrap().unwrap();
        assert_eq!(tuple.record.values, vec![Value::Bigint(42)]);
        assert!(node.next().await.unwrap().is_none());
    }
}
