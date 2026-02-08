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
            Plan::Insert { .. } | Plan::Update { .. } | Plan::Delete { .. } => {
                unreachable!("DML plans should not be converted to executor nodes via prepare_for_execute")
            }
        }
    }
}

impl Plan {
    /// Executes a DML plan (INSERT, UPDATE, DELETE) and returns the affected row count.
    ///
    /// This is the execution entry point for DML statements, in contrast to
    /// [`prepare_for_execute`](Plan::prepare_for_execute) which is used for
    /// SELECT/scan plans that produce rows.
    pub async fn execute_dml<C: ExecContext>(
        self,
        ctx: &C,
    ) -> Result<u64, ExecutorError> {
        match self {
            Plan::Insert {
                first_page,
                schema,
                values,
                serial_columns,
                ..
            } => {
                execute_insert(ctx, first_page, &schema, values, &serial_columns).await
            }
            Plan::Update {
                input,
                assignments,
                first_page,
                ..
            } => {
                execute_update(ctx, *input, &assignments, first_page).await
            }
            Plan::Delete { input, .. } => {
                execute_delete(ctx, *input).await
            }
            _ => unreachable!("non-DML plans should not be passed to execute_dml"),
        }
    }
}

/// Executes an INSERT plan: evaluates value expressions, auto-populates SERIAL
/// columns, and inserts records via the context.
async fn execute_insert<C: ExecContext>(
    ctx: &C,
    first_page: PageId,
    schema: &[Type],
    values: Vec<Vec<BoundExpr>>,
    serial_columns: &[(usize, u32)],
) -> Result<u64, ExecutorError> {
    let empty_record = Record::new(vec![]);
    let mut count = 0u64;

    for row_exprs in &values {
        let mut row_values = Vec::with_capacity(schema.len());
        for expr in row_exprs {
            row_values.push(expr.evaluate(&empty_record)?);
        }

        // Auto-populate SERIAL columns with nextval
        for &(col_idx, seq_id) in serial_columns {
            let val = ctx.nextval(seq_id).await?;
            // Cast the i64 nextval result to match the column type
            row_values[col_idx] = Value::Bigint(val)
                .cast(&schema[col_idx])
                .map_err(|(_, _)| ExecutorError::NumericOutOfRange {
                    type_name: schema[col_idx].display_name().to_string(),
                })?;
        }

        let record = Record::new(row_values);
        ctx.insert_tuple(first_page, &record).await?;
        count += 1;
    }

    Ok(count)
}

/// Executes an UPDATE plan: scans matching rows, evaluates SET expressions,
/// and calls update_tuple for each.
async fn execute_update<C: ExecContext>(
    ctx: &C,
    input: Plan,
    assignments: &[BoundExpr],
    first_page: PageId,
) -> Result<u64, ExecutorError> {
    let mut node = input.prepare_for_execute(ctx);
    let mut count = 0u64;

    while let Some(row) = node.next().await? {
        let tid = row.tid.ok_or_else(|| {
            ExecutorError::Unsupported("UPDATE on rows without physical location".to_string())
        })?;

        // Evaluate assignments against the current row
        let mut new_values = Vec::with_capacity(assignments.len());
        for expr in assignments {
            let val = expr.evaluate(&row.record)?;
            new_values.push(val);
        }

        let new_record = Record::new(new_values);
        ctx.update_tuple(first_page, tid, &new_record).await?;
        count += 1;
    }

    Ok(count)
}

/// Executes a DELETE plan: scans matching rows and calls delete_tuple for each.
async fn execute_delete<C: ExecContext>(
    ctx: &C,
    input: Plan,
) -> Result<u64, ExecutorError> {
    let mut node = input.prepare_for_execute(ctx);
    let mut count = 0u64;

    while let Some(row) = node.next().await? {
        let tid = row.tid.ok_or_else(|| {
            ExecutorError::Unsupported("DELETE on rows without physical location".to_string())
        })?;
        ctx.delete_tuple(tid).await?;
        count += 1;
    }

    Ok(count)
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

    // --- DML execution tests ---

    use crate::executor::planner;

    /// Helper: create a table, plan an INSERT, execute it, then verify by scanning.
    async fn setup_table_and_ctx(
        ddl: &str,
    ) -> (TestDb, crate::tx::Snapshot) {
        let db = Database::open(MemoryStorage::new(), 100).await.unwrap();
        let txid = db.tx_manager().begin();
        let stmt = crate::sql::Parser::new(ddl).parse().unwrap().unwrap();
        let Statement::CreateTable(create_stmt) = stmt else {
            panic!("expected CreateTable");
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

    fn parse_insert_stmt(sql: &str) -> crate::sql::InsertStmt {
        let stmt = crate::sql::Parser::new(sql).parse().unwrap().unwrap();
        let crate::sql::Statement::Insert(insert) = stmt else {
            panic!("expected INSERT");
        };
        *insert
    }

    fn parse_update_stmt(sql: &str) -> crate::sql::UpdateStmt {
        let stmt = crate::sql::Parser::new(sql).parse().unwrap().unwrap();
        let crate::sql::Statement::Update(update) = stmt else {
            panic!("expected UPDATE");
        };
        *update
    }

    fn parse_delete_stmt(sql: &str) -> crate::sql::DeleteStmt {
        let stmt = crate::sql::Parser::new(sql).parse().unwrap().unwrap();
        let crate::sql::Statement::Delete(delete) = stmt else {
            panic!("expected DELETE");
        };
        *delete
    }

    #[tokio::test]
    async fn test_execute_insert() {
        let (db, snapshot) = setup_table_and_ctx(
            "CREATE TABLE t (id INTEGER, name TEXT)",
        )
        .await;

        let insert = parse_insert_stmt("INSERT INTO t VALUES (1, 'Alice'), (2, 'Bob')");
        let plan = planner::plan_insert(&insert, db.catalog(), &snapshot)
            .await
            .unwrap();
        let ctx = db.exec_context(snapshot.clone());
        let count = plan.execute_dml(&ctx).await.unwrap();
        assert_eq!(count, 2);

        // Verify by scanning with a new CID
        let snapshot2 = db.tx_manager().snapshot(snapshot.current_txid, CommandId::new(1));
        let table = db.catalog().get_table(&snapshot2, "t").await.unwrap().unwrap();
        let ctx2 = db.exec_context(snapshot2);
        let (tuples, _) = ctx2
            .scan_heap_page(table.first_page, &[Type::Integer, Type::Text])
            .await
            .unwrap();
        assert_eq!(tuples.len(), 2);
        assert_eq!(tuples[0].record.values[1], Value::Text("Alice".into()));
        assert_eq!(tuples[1].record.values[1], Value::Text("Bob".into()));
    }

    #[tokio::test]
    async fn test_execute_delete() {
        let (db, snapshot) = setup_table_and_ctx(
            "CREATE TABLE t (id INTEGER, name TEXT)",
        )
        .await;

        // First insert some data
        let insert = parse_insert_stmt("INSERT INTO t VALUES (1, 'Alice'), (2, 'Bob'), (3, 'Carol')");
        let plan = planner::plan_insert(&insert, db.catalog(), &snapshot)
            .await
            .unwrap();
        let ctx = db.exec_context(snapshot.clone());
        plan.execute_dml(&ctx).await.unwrap();

        // Delete where id = 2
        let snapshot2 = db.tx_manager().snapshot(snapshot.current_txid, CommandId::new(1));
        let delete = parse_delete_stmt("DELETE FROM t WHERE id = 2");
        let plan = planner::plan_delete(&delete, db.catalog(), &snapshot2)
            .await
            .unwrap();
        let ctx2 = db.exec_context(snapshot2);
        let count = plan.execute_dml(&ctx2).await.unwrap();
        assert_eq!(count, 1);

        // Verify: should have 2 rows remaining
        let snapshot3 = db.tx_manager().snapshot(snapshot.current_txid, CommandId::new(2));
        let table = db.catalog().get_table(&snapshot3, "t").await.unwrap().unwrap();
        let ctx3 = db.exec_context(snapshot3);
        let (tuples, _) = ctx3
            .scan_heap_page(table.first_page, &[Type::Integer, Type::Text])
            .await
            .unwrap();
        assert_eq!(tuples.len(), 2);
        assert_eq!(tuples[0].record.values[0], Value::Integer(1));
        assert_eq!(tuples[1].record.values[0], Value::Integer(3));
    }

    #[tokio::test]
    async fn test_execute_update() {
        let (db, snapshot) = setup_table_and_ctx(
            "CREATE TABLE t (id INTEGER, name TEXT)",
        )
        .await;

        // Insert initial data
        let insert = parse_insert_stmt("INSERT INTO t VALUES (1, 'Alice'), (2, 'Bob')");
        let plan = planner::plan_insert(&insert, db.catalog(), &snapshot)
            .await
            .unwrap();
        let ctx = db.exec_context(snapshot.clone());
        plan.execute_dml(&ctx).await.unwrap();

        // Update: SET name = 'Updated' WHERE id = 1
        let snapshot2 = db.tx_manager().snapshot(snapshot.current_txid, CommandId::new(1));
        let update = parse_update_stmt("UPDATE t SET name = 'Updated' WHERE id = 1");
        let plan = planner::plan_update(&update, db.catalog(), &snapshot2)
            .await
            .unwrap();
        let ctx2 = db.exec_context(snapshot2);
        let count = plan.execute_dml(&ctx2).await.unwrap();
        assert_eq!(count, 1);

        // Verify: Alice should now be Updated, Bob unchanged
        let snapshot3 = db.tx_manager().snapshot(snapshot.current_txid, CommandId::new(2));
        let table = db.catalog().get_table(&snapshot3, "t").await.unwrap().unwrap();
        let ctx3 = db.exec_context(snapshot3);
        let (tuples, _) = ctx3
            .scan_heap_page(table.first_page, &[Type::Integer, Type::Text])
            .await
            .unwrap();
        // Bob should remain, Alice's old version is deleted, new version is inserted
        // Due to same-page priority, we should have 3 physical tuples but only 2 visible
        assert_eq!(tuples.len(), 2);
        let names: Vec<&Value> = tuples.iter().map(|t| &t.record.values[1]).collect();
        assert!(names.contains(&&Value::Text("Updated".into())));
        assert!(names.contains(&&Value::Text("Bob".into())));
    }

    #[tokio::test]
    async fn test_execute_insert_serial() {
        let (db, snapshot) = setup_table_and_ctx(
            "CREATE TABLE t (id SERIAL, name TEXT)",
        )
        .await;

        let insert = parse_insert_stmt("INSERT INTO t (name) VALUES ('Alice'), ('Bob')");
        let plan = planner::plan_insert(&insert, db.catalog(), &snapshot)
            .await
            .unwrap();
        let ctx = db.exec_context(snapshot.clone());
        let count = plan.execute_dml(&ctx).await.unwrap();
        assert_eq!(count, 2);

        // Verify SERIAL ids are auto-incremented
        let snapshot2 = db.tx_manager().snapshot(snapshot.current_txid, CommandId::new(1));
        let table = db.catalog().get_table(&snapshot2, "t").await.unwrap().unwrap();
        let ctx2 = db.exec_context(snapshot2);
        let (tuples, _) = ctx2
            .scan_heap_page(table.first_page, &[Type::Integer, Type::Text])
            .await
            .unwrap();
        assert_eq!(tuples.len(), 2);
        assert_eq!(tuples[0].record.values[0], Value::Integer(1));
        assert_eq!(tuples[1].record.values[0], Value::Integer(2));
    }

    #[tokio::test]
    async fn test_execute_delete_without_where() {
        let (db, snapshot) = setup_table_and_ctx(
            "CREATE TABLE t (id INTEGER)",
        )
        .await;

        // Insert data
        let insert = parse_insert_stmt("INSERT INTO t VALUES (1), (2), (3)");
        let plan = planner::plan_insert(&insert, db.catalog(), &snapshot)
            .await
            .unwrap();
        let ctx = db.exec_context(snapshot.clone());
        plan.execute_dml(&ctx).await.unwrap();

        // Delete all rows
        let snapshot2 = db.tx_manager().snapshot(snapshot.current_txid, CommandId::new(1));
        let delete = parse_delete_stmt("DELETE FROM t");
        let plan = planner::plan_delete(&delete, db.catalog(), &snapshot2)
            .await
            .unwrap();
        let ctx2 = db.exec_context(snapshot2);
        let count = plan.execute_dml(&ctx2).await.unwrap();
        assert_eq!(count, 3);

        // Verify: no visible rows
        let snapshot3 = db.tx_manager().snapshot(snapshot.current_txid, CommandId::new(2));
        let table = db.catalog().get_table(&snapshot3, "t").await.unwrap().unwrap();
        let ctx3 = db.exec_context(snapshot3);
        let (tuples, _) = ctx3
            .scan_heap_page(table.first_page, &[Type::Integer])
            .await
            .unwrap();
        assert_eq!(tuples.len(), 0);
    }
}
