//! Query execution runner.
//!
//! This module provides the physical execution layer:
//!
//! - [`QueryNode`] — Volcano iterator nodes with async `next()`
//! - [`DmlResult`] — result of executing a [`DmlPlan`]
//! - [`DmlPlan::execute_dml`] — DML execution entry point
//! - [`QueryPlan::prepare_for_execute`] — plan-to-executor conversion
//!
//! All nodes are generic over [`ExecContext`], which provides storage
//! operations. This keeps executor logic decoupled from concrete storage types.

use std::collections::{HashMap, HashSet};

use crate::datum::{Type, Value};
use crate::heap::Record;
use crate::storage::PageId;

use super::ColumnDesc;
use super::aggregate::{AggregateOp, GroupKey};
use super::context::ExecContext;
use super::error::ExecutorError;
use super::expr::BoundExpr;
use super::plan::{DmlPlan, QueryPlan};
use super::row::Row;

/// Result of executing a DML plan.
///
/// Each variant corresponds to its DML operation, allowing type-safe
/// access to operation-specific results (e.g., future extensions like
/// returning generated IDs for INSERT).
pub enum DmlResult {
    /// INSERT completed.
    Insert {
        /// Number of rows inserted.
        count: u64,
    },
    /// UPDATE completed.
    Update {
        /// Number of rows updated.
        count: u64,
    },
    /// DELETE completed.
    Delete {
        /// Number of rows deleted.
        count: u64,
    },
}

impl DmlResult {
    /// Formats the PostgreSQL-style command completion tag.
    pub fn command_tag(&self) -> String {
        match self {
            DmlResult::Insert { count } => format!("INSERT 0 {count}"),
            DmlResult::Update { count } => format!("UPDATE {count}"),
            DmlResult::Delete { count } => format!("DELETE {count}"),
        }
    }
}

/// A query executor node.
pub enum QueryNode<C: ExecContext> {
    /// Sequential heap scan with lazy page loading.
    SeqScan(SeqScan<C>),
    /// Row filter (WHERE clause).
    Filter(Filter<C>),
    /// Column projection (SELECT list).
    Projection(Projection<C>),
    /// Hash-aggregate node.
    Aggregate(Aggregate<C>),
    /// Single-row scan for queries without FROM (e.g., `SELECT 1+1`).
    ValuesScan(ValuesScan),
}

impl QueryPlan {
    /// Converts a logical [`QueryPlan`] into a physical [`QueryNode`] tree.
    ///
    /// This is a synchronous function — no I/O happens here. All storage access
    /// is deferred to [`QueryNode::next()`] via the [`ExecContext`].
    pub fn prepare_for_execute<C: ExecContext>(self, ctx: &C) -> QueryNode<C> {
        match self {
            QueryPlan::SeqScan {
                table_name,
                first_page,
                schema,
                columns,
                ..
            } => QueryNode::SeqScan(SeqScan::new(
                table_name,
                columns,
                ctx.clone(),
                schema,
                first_page,
            )),
            QueryPlan::Filter { input, predicate } => {
                QueryNode::Filter(Filter::new(input.prepare_for_execute(ctx), predicate))
            }
            QueryPlan::Projection {
                input,
                exprs,
                columns,
            } => QueryNode::Projection(Projection::new(
                input.prepare_for_execute(ctx),
                exprs,
                columns,
            )),
            QueryPlan::Aggregate {
                input,
                group_by,
                aggregates,
                columns,
            } => QueryNode::Aggregate(Aggregate::new(
                input.prepare_for_execute(ctx),
                group_by,
                aggregates,
                columns,
            )),
            QueryPlan::ValuesScan => QueryNode::ValuesScan(ValuesScan::new()),
        }
    }
}

impl DmlPlan {
    /// Executes a DML plan (INSERT, UPDATE, DELETE) and returns the result.
    ///
    /// This is the execution entry point for DML statements, in contrast to
    /// [`QueryPlan::prepare_for_execute`] which is used for SELECT/scan plans
    /// that produce rows.
    pub async fn execute_dml<C: ExecContext>(self, ctx: &C) -> Result<DmlResult, ExecutorError> {
        match self {
            DmlPlan::Insert {
                first_page,
                schema,
                values,
                serial_columns,
                ..
            } => {
                let count =
                    execute_insert(ctx, first_page, &schema, values, &serial_columns).await?;
                Ok(DmlResult::Insert { count })
            }
            DmlPlan::Update {
                input,
                assignments,
                first_page,
                ..
            } => {
                let count = execute_update(ctx, *input, &assignments, first_page).await?;
                Ok(DmlResult::Update { count })
            }
            DmlPlan::Delete { input, .. } => {
                let count = execute_delete(ctx, *input).await?;
                Ok(DmlResult::Delete { count })
            }
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
    input: QueryPlan,
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
async fn execute_delete<C: ExecContext>(ctx: &C, input: QueryPlan) -> Result<u64, ExecutorError> {
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

impl<C: ExecContext> QueryNode<C> {
    /// Returns the next row, or `None` if exhausted.
    ///
    /// This method follows the Volcano iterator model naming convention,
    /// not `std::iter::Iterator`, because it returns `Result<Option<_>>`.
    ///
    /// Uses `Pin<Box<...>>` to break the recursive future cycle
    /// (QueryNode -> Filter -> QueryNode).
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
                QueryNode::SeqScan(n) => n.next().await,
                QueryNode::Filter(n) => n.next().await,
                QueryNode::Projection(n) => n.next().await,
                QueryNode::Aggregate(n) => n.next().await,
                QueryNode::ValuesScan(n) => n.next().await,
            }
        })
    }

    /// Returns the column descriptors for this node's output.
    pub fn columns(&self) -> &[ColumnDesc] {
        match self {
            QueryNode::SeqScan(n) => &n.columns,
            QueryNode::Filter(n) => n.child.columns(),
            QueryNode::Projection(n) => &n.columns,
            QueryNode::Aggregate(n) => &n.columns,
            QueryNode::ValuesScan(n) => &n.columns,
        }
    }
}

/// Sequential scan node that lazily loads visible rows page-by-page.
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
    /// Buffer of rows from the current page (ownership-based, no clone).
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

    /// Returns the next visible row, loading pages lazily as needed.
    ///
    /// Follows the heap page chain automatically: when a page is exhausted,
    /// advances to the next page via the chain linkage.
    async fn next(&mut self) -> Result<Option<Row>, ExecutorError> {
        loop {
            if let Some(row) = self.buffer.next() {
                return Ok(Some(row));
            }
            let page_id = match self.next_page_id.take() {
                Some(id) => id,
                None => return Ok(None),
            };
            let (tuples, next_page) = self.ctx.scan_heap_page(page_id, &self.schema).await?;
            self.next_page_id = next_page;
            self.buffer = tuples
                .into_iter()
                .map(|(tid, record)| Row::from_heap(tid, record))
                .collect::<Vec<_>>()
                .into_iter();
        }
    }
}

/// Filter node that applies a predicate to each row from its child.
pub struct Filter<C: ExecContext> {
    /// Child node to pull rows from.
    child: Box<QueryNode<C>>,
    /// Bound predicate expression (must evaluate to boolean).
    predicate: BoundExpr,
}

impl<C: ExecContext> Filter<C> {
    /// Creates a new Filter node.
    pub fn new(child: QueryNode<C>, predicate: BoundExpr) -> Self {
        Self {
            child: Box::new(child),
            predicate,
        }
    }

    /// Returns the next row that satisfies the predicate.
    async fn next(&mut self) -> Result<Option<Row>, ExecutorError> {
        loop {
            match self.child.next().await? {
                Some(row) => {
                    let result = self.predicate.evaluate(&row.record)?;
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
pub struct Projection<C: ExecContext> {
    /// Child node to pull rows from.
    child: Box<QueryNode<C>>,
    /// Bound expressions to evaluate for each output column.
    exprs: Vec<BoundExpr>,
    /// Output column descriptors.
    columns: Vec<ColumnDesc>,
}

impl<C: ExecContext> Projection<C> {
    /// Creates a new Projection node.
    pub fn new(child: QueryNode<C>, exprs: Vec<BoundExpr>, columns: Vec<ColumnDesc>) -> Self {
        Self {
            child: Box::new(child),
            exprs,
            columns,
        }
    }

    /// Returns the next projected row.
    ///
    /// NOTE: Allocates a new Vec and Record per row. For production, consider
    /// arena allocation or a reusable row buffer to reduce GC pressure on
    /// large result sets.
    async fn next(&mut self) -> Result<Option<Row>, ExecutorError> {
        match self.child.next().await? {
            Some(row) => {
                let mut values = Vec::with_capacity(self.exprs.len());
                for expr in &self.exprs {
                    values.push(expr.evaluate(&row.record)?);
                }
                Ok(Some(Row::computed(Record::new(values))))
            }
            None => Ok(None),
        }
    }
}

/// Hash-aggregate node.
///
/// Consumes all input rows on first `next()` call, groups them by the
/// GROUP BY key (using [`GroupKey`] for NULL=NULL HashMap semantics),
/// computes aggregate values per group, then emits result rows one
/// at a time.
///
/// Output schema: \[group_key_values..., aggregate_results...\].
///
/// NOTE: Loads all group keys and accumulators into memory. For
/// production, consider sort-based grouping with spill-to-disk for
/// high-cardinality GROUP BY.
pub struct Aggregate<C: ExecContext> {
    /// Child node to pull rows from.
    child: Box<QueryNode<C>>,
    /// GROUP BY expressions (bound against child's output schema).
    group_by: Vec<BoundExpr>,
    /// Aggregate operations to compute.
    aggregates: Vec<AggregateOp>,
    /// Output column descriptors.
    columns: Vec<ColumnDesc>,
    /// Buffered result rows (populated on first `next()` call).
    buffer: Option<std::vec::IntoIter<Row>>,
}

impl<C: ExecContext> Aggregate<C> {
    /// Creates a new Aggregate node.
    pub fn new(
        child: QueryNode<C>,
        group_by: Vec<BoundExpr>,
        aggregates: Vec<AggregateOp>,
        columns: Vec<ColumnDesc>,
    ) -> Self {
        Self {
            child: Box::new(child),
            group_by,
            aggregates,
            columns,
            buffer: None,
        }
    }

    /// Returns the next aggregated row, or `None` if exhausted.
    ///
    /// On the first call, consumes all input rows and builds the aggregation
    /// result. Subsequent calls return buffered rows.
    async fn next(&mut self) -> Result<Option<Row>, ExecutorError> {
        if let Some(ref mut iter) = self.buffer {
            return Ok(iter.next());
        }

        // --- First call: consume all input and compute aggregates ---

        // Per-group state:
        // - accumulators: one per aggregate operation
        // - distinct_sets: one HashSet per DISTINCT aggregate (None for non-DISTINCT)
        struct GroupState {
            accumulators: Vec<Box<dyn super::aggregate::Accumulator>>,
            distinct_sets: Vec<Option<HashSet<GroupKey>>>,
        }

        let mut groups: HashMap<GroupKey, GroupState> = HashMap::new();
        // Track insertion order for deterministic output (important for scalar aggregates)
        let mut group_order: Vec<GroupKey> = Vec::new();

        // Consume all input rows
        while let Some(row) = self.child.next().await? {
            // Evaluate GROUP BY expressions to form the group key
            let key_values: Vec<Value> = self
                .group_by
                .iter()
                .map(|expr| expr.evaluate(&row.record))
                .collect::<Result<_, _>>()?;
            let key = GroupKey(key_values);

            // Get or create group state (one clone for the HashMap key,
            // move the original into group_order for vacant entries)
            let state = match groups.entry(key.clone()) {
                std::collections::hash_map::Entry::Occupied(e) => e.into_mut(),
                std::collections::hash_map::Entry::Vacant(e) => {
                    group_order.push(key);
                    e.insert(GroupState {
                        accumulators: self
                            .aggregates
                            .iter()
                            .map(|op| op.create_accumulator())
                            .collect(),
                        distinct_sets: self
                            .aggregates
                            .iter()
                            .map(|op| {
                                if op.distinct {
                                    Some(HashSet::new())
                                } else {
                                    None
                                }
                            })
                            .collect(),
                    })
                }
            };

            // Feed each aggregate
            for (i, op) in self.aggregates.iter().enumerate() {
                if op.args.is_empty() {
                    // COUNT(*): feed once per row (value is ignored)
                    state.accumulators[i].feed(&Value::Null)?;
                } else {
                    // Evaluate aggregate argument
                    let val = op.args[0].evaluate(&row.record)?;

                    // Skip NULLs for non-COUNT(*) aggregates
                    if val.is_null() {
                        continue;
                    }

                    // DISTINCT dedup check
                    if let Some(ref mut dedup_set) = state.distinct_sets[i] {
                        let dedup_key = GroupKey(vec![val.clone()]);
                        if !dedup_set.insert(dedup_key) {
                            continue; // Duplicate value, skip
                        }
                    }

                    state.accumulators[i].feed(&val)?;
                }
            }
        }

        // If no groups were created and no GROUP BY (scalar aggregate),
        // produce one row with default accumulator results
        if groups.is_empty() && self.group_by.is_empty() {
            let accumulators: Vec<Box<dyn super::aggregate::Accumulator>> = self
                .aggregates
                .iter()
                .map(|op| op.create_accumulator())
                .collect();
            let mut values = Vec::with_capacity(self.aggregates.len());
            for acc in &accumulators {
                values.push(acc.finish());
            }
            let rows = vec![Row::computed(Record::new(values))];
            self.buffer = Some(rows.into_iter());
            return Ok(self.buffer.as_mut().unwrap().next());
        }

        // Build result rows in insertion order
        let mut rows = Vec::with_capacity(groups.len());
        for key in &group_order {
            let state = groups.remove(key).unwrap();
            let mut values = Vec::with_capacity(self.group_by.len() + self.aggregates.len());

            // Group key values first
            for v in &key.0 {
                values.push(v.clone());
            }

            // Then aggregate results
            for acc in &state.accumulators {
                values.push(acc.finish());
            }

            rows.push(Row::computed(Record::new(values)));
        }

        self.buffer = Some(rows.into_iter());
        Ok(self.buffer.as_mut().unwrap().next())
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
    //! NOTE: This module depends on `crate::engine` (a higher layer) for test
    //! setup. Constructing `ExecContext` implementors and their prerequisites
    //! (buffer pool, transaction snapshots, catalog, etc.) by hand would be
    //! prohibitively verbose, so we use `Engine` helpers as a pragmatic
    //! exception to the normal layering direction.

    use super::*;
    use crate::datum::{Type, Value};
    use std::sync::Arc;

    use crate::engine::ExecutionPoint;
    use crate::engine::tests::{TestEngine, open_test_engine};
    use crate::executor::planner;
    use crate::executor::tests::{bind_expr, int_col};
    use crate::heap::{HeapPage, Record};
    use crate::sql::tests::{parse_delete, parse_insert, parse_update};
    use crate::storage::{LruReplacer, MemoryStorage, PageId};

    use crate::tx::CommandId;

    type TestCtx = ExecutionPoint<MemoryStorage, LruReplacer>;

    /// Creates a test database with `CREATE TABLE test (id INT)` and inserts
    /// the given values via direct heap page writes. Returns the database
    /// and the table's first page ID.
    async fn setup_int_table(values: Vec<i64>) -> (Arc<TestEngine>, PageId) {
        let db = open_test_engine().await;
        db.create_test_table("CREATE TABLE test (id INT)").await;

        let txid = db.tx_manager().begin();
        let cid = CommandId::FIRST;
        let snapshot = db.tx_manager().snapshot(txid, cid);
        let catalog = db.catalog(&snapshot).await.unwrap();
        let table = &catalog.resolve_table("test").unwrap();
        let first_page = table.info.first_page;
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
    async fn setup_two_col_table(rows: Vec<(i64, &str)>) -> (Arc<TestEngine>, PageId) {
        let db = open_test_engine().await;
        db.create_test_table("CREATE TABLE test (id INT, name TEXT)")
            .await;

        let txid = db.tx_manager().begin();
        let cid = CommandId::FIRST;
        let snapshot = db.tx_manager().snapshot(txid, cid);
        let catalog = db.catalog(&snapshot).await.unwrap();
        let table = &catalog.resolve_table("test").unwrap();
        let first_page = table.info.first_page;
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

    /// Creates an execution point from a database with a fresh read-only snapshot.
    fn read_ctx(db: &Arc<TestEngine>) -> TestCtx {
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        db.execution_point(snapshot)
    }

    /// Helper: create a table and return db, snapshot, and catalog snapshot for planning.
    async fn setup_table_and_ctx(
        ddl: &str,
    ) -> (
        Arc<TestEngine>,
        crate::tx::Snapshot,
        Arc<crate::catalog::Catalog>,
    ) {
        let db = open_test_engine().await;
        db.create_test_table(ddl).await;

        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        let catalog = db.catalog(&snapshot).await.unwrap();
        (db, snapshot, catalog)
    }

    #[tokio::test]
    async fn test_seq_scan_lazy_loading() {
        let (db, first_page) = setup_int_table(vec![1, 2, 3]).await;
        let ctx = read_ctx(&db);
        let mut node = QueryNode::SeqScan(SeqScan::new(
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
        let scan = QueryNode::SeqScan(SeqScan::new(
            "test".to_string(),
            vec![int_col("id")],
            ctx,
            vec![Type::Bigint],
            first_page,
        ));

        // Filter: id > 2
        let predicate = bind_expr("id > 2", &[int_col("id")]);
        let mut node = QueryNode::Filter(Filter::new(scan, predicate));

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
        let scan = QueryNode::SeqScan(SeqScan::new(
            "test".to_string(),
            vec![int_col("id")],
            ctx,
            vec![Type::Bigint],
            first_page,
        ));

        // Predicate that always evaluates to NULL: id = NULL
        // NULL comparisons return NULL, which Filter must skip (not treat as true)
        let predicate = bind_expr("id = NULL", &[int_col("id")]);
        let mut node = QueryNode::Filter(Filter::new(scan, predicate));

        // All rows should be skipped because NULL is not true
        assert!(node.next().await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_projection() {
        let (db, first_page) = setup_two_col_table(vec![(1, "alice"), (2, "bob")]).await;
        let ctx = read_ctx(&db);
        let scan = QueryNode::SeqScan(SeqScan::new(
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
        let mut node = QueryNode::Projection(Projection::new(scan, exprs, out_cols));

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
        let mut node: QueryNode<TestCtx> = QueryNode::ValuesScan(ValuesScan::new());
        let tuple = node.next().await.unwrap().unwrap();
        assert!(tuple.record.values.is_empty());
        assert!(tuple.tid.is_none());
        assert!(node.next().await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_build_seq_scan() {
        let (db, first_page) = setup_int_table(vec![10, 20]).await;
        let ctx = read_ctx(&db);

        let plan = QueryPlan::SeqScan {
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

        let plan = QueryPlan::Filter {
            input: Box::new(QueryPlan::SeqScan {
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

        let plan = QueryPlan::Projection {
            input: Box::new(QueryPlan::SeqScan {
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
        let db = open_test_engine().await;
        let ctx = read_ctx(&db);

        let plan = QueryPlan::Projection {
            input: Box::new(QueryPlan::ValuesScan),
            exprs: vec![bind_expr("42", &[])],
            columns: vec![int_col("?column?")],
        };

        let mut node = plan.prepare_for_execute(&ctx);

        let tuple = node.next().await.unwrap().unwrap();
        assert_eq!(tuple.record.values, vec![Value::Bigint(42)]);
        assert!(node.next().await.unwrap().is_none());
    }

    // --- DML execution tests ---

    #[tokio::test]
    async fn test_execute_insert() {
        let (db, snapshot, catalog) =
            setup_table_and_ctx("CREATE TABLE t (id INTEGER, name TEXT)").await;

        let insert = parse_insert("INSERT INTO t VALUES (1, 'Alice'), (2, 'Bob')");
        let plan = planner::plan_insert(&insert, &catalog).unwrap();
        let ctx = db.execution_point(snapshot.clone());
        let DmlResult::Insert { count } = plan.execute_dml(&ctx).await.unwrap() else {
            panic!("expected DmlResult::Insert");
        };
        assert_eq!(count, 2);

        // Verify by scanning with a new CID
        let snapshot2 = db
            .tx_manager()
            .snapshot(snapshot.current_txid, CommandId::new(1));
        let table = &catalog.resolve_table("t").unwrap();
        let ctx2 = db.execution_point(snapshot2);
        let (tuples, _) = ctx2
            .scan_heap_page(table.info.first_page, &[Type::Integer, Type::Text])
            .await
            .unwrap();
        assert_eq!(tuples.len(), 2);
        assert_eq!(tuples[0].1.values[1], Value::Text("Alice".into()));
        assert_eq!(tuples[1].1.values[1], Value::Text("Bob".into()));
    }

    #[tokio::test]
    async fn test_execute_delete() {
        let (db, snapshot, catalog) =
            setup_table_and_ctx("CREATE TABLE t (id INTEGER, name TEXT)").await;

        // First insert some data
        let insert = parse_insert("INSERT INTO t VALUES (1, 'Alice'), (2, 'Bob'), (3, 'Carol')");
        let plan = planner::plan_insert(&insert, &catalog).unwrap();
        let ctx = db.execution_point(snapshot.clone());
        plan.execute_dml(&ctx).await.unwrap();

        // Delete where id = 2
        let snapshot2 = db
            .tx_manager()
            .snapshot(snapshot.current_txid, CommandId::new(1));
        let delete = parse_delete("DELETE FROM t WHERE id = 2");
        let plan = planner::plan_delete(&delete, &catalog).unwrap();
        let ctx2 = db.execution_point(snapshot2);
        let DmlResult::Delete { count } = plan.execute_dml(&ctx2).await.unwrap() else {
            panic!("expected DmlResult::Delete");
        };
        assert_eq!(count, 1);

        // Verify: should have 2 rows remaining
        let snapshot3 = db
            .tx_manager()
            .snapshot(snapshot.current_txid, CommandId::new(2));
        let table = &catalog.resolve_table("t").unwrap();
        let ctx3 = db.execution_point(snapshot3);
        let (tuples, _) = ctx3
            .scan_heap_page(table.info.first_page, &[Type::Integer, Type::Text])
            .await
            .unwrap();
        assert_eq!(tuples.len(), 2);
        assert_eq!(tuples[0].1.values[0], Value::Integer(1));
        assert_eq!(tuples[1].1.values[0], Value::Integer(3));
    }

    #[tokio::test]
    async fn test_execute_update() {
        let (db, snapshot, catalog) =
            setup_table_and_ctx("CREATE TABLE t (id INTEGER, name TEXT)").await;

        // Insert initial data
        let insert = parse_insert("INSERT INTO t VALUES (1, 'Alice'), (2, 'Bob')");
        let plan = planner::plan_insert(&insert, &catalog).unwrap();
        let ctx = db.execution_point(snapshot.clone());
        plan.execute_dml(&ctx).await.unwrap();

        // Update: SET name = 'Updated' WHERE id = 1
        let snapshot2 = db
            .tx_manager()
            .snapshot(snapshot.current_txid, CommandId::new(1));
        let update = parse_update("UPDATE t SET name = 'Updated' WHERE id = 1");
        let plan = planner::plan_update(&update, &catalog).unwrap();
        let ctx2 = db.execution_point(snapshot2);
        let DmlResult::Update { count } = plan.execute_dml(&ctx2).await.unwrap() else {
            panic!("expected DmlResult::Update");
        };
        assert_eq!(count, 1);

        // Verify: Alice should now be Updated, Bob unchanged
        let snapshot3 = db
            .tx_manager()
            .snapshot(snapshot.current_txid, CommandId::new(2));
        let table = &catalog.resolve_table("t").unwrap();
        let ctx3 = db.execution_point(snapshot3);
        let (tuples, _) = ctx3
            .scan_heap_page(table.info.first_page, &[Type::Integer, Type::Text])
            .await
            .unwrap();
        // Bob should remain, Alice's old version is deleted, new version is inserted
        // Due to same-page priority, we should have 3 physical tuples but only 2 visible
        assert_eq!(tuples.len(), 2);
        let names: Vec<&Value> = tuples.iter().map(|t| &t.1.values[1]).collect();
        assert!(names.contains(&&Value::Text("Updated".into())));
        assert!(names.contains(&&Value::Text("Bob".into())));
    }

    #[tokio::test]
    async fn test_execute_insert_serial() {
        let (db, snapshot, catalog) =
            setup_table_and_ctx("CREATE TABLE t (id SERIAL, name TEXT)").await;

        let insert = parse_insert("INSERT INTO t (name) VALUES ('Alice'), ('Bob')");
        let plan = planner::plan_insert(&insert, &catalog).unwrap();
        let ctx = db.execution_point(snapshot.clone());
        let DmlResult::Insert { count } = plan.execute_dml(&ctx).await.unwrap() else {
            panic!("expected DmlResult::Insert");
        };
        assert_eq!(count, 2);

        // Verify SERIAL ids are auto-incremented
        let snapshot2 = db
            .tx_manager()
            .snapshot(snapshot.current_txid, CommandId::new(1));
        let table = &catalog.resolve_table("t").unwrap();
        let ctx2 = db.execution_point(snapshot2);
        let (tuples, _) = ctx2
            .scan_heap_page(table.info.first_page, &[Type::Integer, Type::Text])
            .await
            .unwrap();
        assert_eq!(tuples.len(), 2);
        assert_eq!(tuples[0].1.values[0], Value::Integer(1));
        assert_eq!(tuples[1].1.values[0], Value::Integer(2));
    }

    #[tokio::test]
    async fn test_execute_delete_without_where() {
        let (db, snapshot, catalog) = setup_table_and_ctx("CREATE TABLE t (id INTEGER)").await;

        // Insert data
        let insert = parse_insert("INSERT INTO t VALUES (1), (2), (3)");
        let plan = planner::plan_insert(&insert, &catalog).unwrap();
        let ctx = db.execution_point(snapshot.clone());
        plan.execute_dml(&ctx).await.unwrap();

        // Delete all rows
        let snapshot2 = db
            .tx_manager()
            .snapshot(snapshot.current_txid, CommandId::new(1));
        let delete = parse_delete("DELETE FROM t");
        let plan = planner::plan_delete(&delete, &catalog).unwrap();
        let ctx2 = db.execution_point(snapshot2);
        let DmlResult::Delete { count } = plan.execute_dml(&ctx2).await.unwrap() else {
            panic!("expected DmlResult::Delete");
        };
        assert_eq!(count, 3);

        // Verify: no visible rows
        let snapshot3 = db
            .tx_manager()
            .snapshot(snapshot.current_txid, CommandId::new(2));
        let table = &catalog.resolve_table("t").unwrap();
        let ctx3 = db.execution_point(snapshot3);
        let (tuples, _) = ctx3
            .scan_heap_page(table.info.first_page, &[Type::Integer])
            .await
            .unwrap();
        assert_eq!(tuples.len(), 0);
    }

    // --- Aggregate execution tests ---

    /// Helper to collect all rows from a QueryNode into a Vec of value Vecs.
    async fn collect_rows(mut node: QueryNode<TestCtx>) -> Vec<Vec<Value>> {
        let mut rows = Vec::new();
        while let Some(row) = node.next().await.unwrap() {
            rows.push(row.record.values);
        }
        rows
    }

    /// Helper to set up a table with data and plan+execute a SELECT query,
    /// returning all result rows.
    async fn query_rows(ddl: &str, inserts: &[&str], select_sql: &str) -> Vec<Vec<Value>> {
        use crate::sql::tests::parse_select;

        let (db, snapshot, catalog) = setup_table_and_ctx(ddl).await;

        // Insert data
        let mut cid_counter = 0u32;
        for &sql in inserts {
            let insert = parse_insert(sql);
            let plan = planner::plan_insert(&insert, &catalog).unwrap();
            let snap = db
                .tx_manager()
                .snapshot(snapshot.current_txid, CommandId::new(cid_counter));
            let ctx = db.execution_point(snap);
            plan.execute_dml(&ctx).await.unwrap();
            cid_counter += 1;
        }

        // Execute select query
        let select = parse_select(select_sql);
        let plan = planner::plan_select(&select, &catalog).unwrap();
        let snap = db
            .tx_manager()
            .snapshot(snapshot.current_txid, CommandId::new(cid_counter));
        let ctx = db.execution_point(snap);
        let node = plan.prepare_for_execute(&ctx);
        collect_rows(node).await
    }

    #[tokio::test]
    async fn test_aggregate_scalar_count() {
        let rows = query_rows(
            "CREATE TABLE t (id INTEGER)",
            &["INSERT INTO t VALUES (1), (2), (3)"],
            "SELECT COUNT(*) FROM t",
        )
        .await;

        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0], vec![Value::Bigint(3)]);
    }

    #[tokio::test]
    async fn test_aggregate_scalar_sum() {
        let rows = query_rows(
            "CREATE TABLE t (val INTEGER)",
            &["INSERT INTO t VALUES (10), (20), (30)"],
            "SELECT SUM(val) FROM t",
        )
        .await;

        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0], vec![Value::Bigint(60)]);
    }

    #[tokio::test]
    async fn test_aggregate_scalar_empty_table() {
        let rows = query_rows(
            "CREATE TABLE t (val INTEGER)",
            &[],
            "SELECT COUNT(*), SUM(val), AVG(val), MIN(val), MAX(val) FROM t",
        )
        .await;

        assert_eq!(rows.len(), 1);
        // COUNT(*) on empty = 0; SUM/AVG/MIN/MAX on empty = NULL
        assert_eq!(rows[0][0], Value::Bigint(0));
        assert!(rows[0][1].is_null());
        assert!(rows[0][2].is_null());
        assert!(rows[0][3].is_null());
        assert!(rows[0][4].is_null());
    }

    #[tokio::test]
    async fn test_aggregate_group_by() {
        let rows = query_rows(
            "CREATE TABLE t (dept TEXT, salary INTEGER)",
            &[
                "INSERT INTO t VALUES ('eng', 100)",
                "INSERT INTO t VALUES ('eng', 200)",
                "INSERT INTO t VALUES ('sales', 300)",
            ],
            "SELECT dept, COUNT(*), SUM(salary) FROM t GROUP BY dept",
        )
        .await;

        assert_eq!(rows.len(), 2);
        // Order depends on insertion order of group keys
        let eng_row = rows.iter().find(|r| r[0] == Value::Text("eng".into()));
        let sales_row = rows.iter().find(|r| r[0] == Value::Text("sales".into()));
        assert!(eng_row.is_some());
        assert!(sales_row.is_some());
        let eng = eng_row.unwrap();
        assert_eq!(eng[1], Value::Bigint(2)); // COUNT
        assert_eq!(eng[2], Value::Bigint(300)); // SUM(100+200)
        let sales = sales_row.unwrap();
        assert_eq!(sales[1], Value::Bigint(1)); // COUNT
        assert_eq!(sales[2], Value::Bigint(300)); // SUM(300)
    }

    #[tokio::test]
    async fn test_aggregate_having_filter() {
        let rows = query_rows(
            "CREATE TABLE t (dept TEXT, salary INTEGER)",
            &[
                "INSERT INTO t VALUES ('eng', 100)",
                "INSERT INTO t VALUES ('eng', 200)",
                "INSERT INTO t VALUES ('sales', 300)",
            ],
            "SELECT dept, COUNT(*) FROM t GROUP BY dept HAVING COUNT(*) > 1",
        )
        .await;

        // Only 'eng' has COUNT > 1
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0][0], Value::Text("eng".into()));
        assert_eq!(rows[0][1], Value::Bigint(2));
    }

    #[tokio::test]
    async fn test_aggregate_avg() {
        let rows = query_rows(
            "CREATE TABLE t (val INTEGER)",
            &["INSERT INTO t VALUES (10), (20), (30)"],
            "SELECT AVG(val) FROM t",
        )
        .await;

        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0][0], Value::Double(20.0));
    }

    #[tokio::test]
    async fn test_aggregate_min_max() {
        let rows = query_rows(
            "CREATE TABLE t (val INTEGER)",
            &["INSERT INTO t VALUES (30), (10), (20)"],
            "SELECT MIN(val), MAX(val) FROM t",
        )
        .await;

        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0][0], Value::Integer(10));
        assert_eq!(rows[0][1], Value::Integer(30));
    }
}
