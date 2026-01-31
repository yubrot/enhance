//! Volcano-style query executor.
//!
//! The executor processes queries by building a tree of operators that produce
//! tuples on demand via the `next()` method. This is the classic iterator model
//! (Volcano model) used in most database systems.

use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;

use super::error::ExecutorError;
use super::expr::BoundExpr;
use super::plan::{ColumnDesc, Plan};
use super::tuple::{Tuple, TupleId};
use crate::db::Database;
use crate::heap::{HeapPage, Record};
use crate::storage::{PageId, Replacer, Storage};
use crate::tx::{Snapshot, TupleHeader};

/// Execution context passed to executors.
///
/// Contains references to the database components needed for query execution.
pub struct ExecutionContext<S: Storage, R: Replacer> {
    /// Reference to the database.
    pub database: Arc<Database<S, R>>,
    /// MVCC snapshot for visibility determination.
    pub snapshot: Snapshot,
}

impl<S: Storage, R: Replacer> ExecutionContext<S, R> {
    /// Creates a new execution context.
    pub fn new(database: Arc<Database<S, R>>, snapshot: Snapshot) -> Self {
        Self { database, snapshot }
    }
}

/// State for SeqScan executor.
///
/// This type is public because it's used in the `Executor` enum.
/// External code should not construct or directly manipulate this type.
pub struct SeqScanState {
    /// First page of the heap.
    first_page: PageId,
    /// Column type OIDs for deserialization.
    schema: Vec<i32>,
    /// Output column descriptors.
    output_columns: Vec<ColumnDesc>,
    /// Collected visible tuples (fetched on open).
    tuples: Vec<(TupleId, TupleHeader, Record)>,
    /// Current position in tuples.
    position: usize,
    /// Whether the executor has been opened.
    opened: bool,
}

/// Volcano-style iterator for query execution (enum-based).
///
/// Each variant represents a different type of executor operator.
/// The enum approach avoids the need for `async_trait` and makes the
/// type parameters explicit.
pub enum Executor<S: Storage, R: Replacer> {
    /// Sequential scan of a heap table.
    SeqScan {
        state: SeqScanState,
        ctx: ExecutionContext<S, R>,
    },

    /// Filter operator (WHERE clause).
    Filter {
        input: Box<Executor<S, R>>,
        predicate: BoundExpr,
    },

    /// Projection operator (SELECT list).
    Projection {
        input: Box<Executor<S, R>>,
        exprs: Vec<BoundExpr>,
        output_columns: Vec<ColumnDesc>,
    },
}

impl<S: Storage, R: Replacer> Executor<S, R> {
    /// Creates an executor from a plan.
    pub fn from_plan(plan: Plan, ctx: ExecutionContext<S, R>) -> Self {
        match plan {
            Plan::SeqScan {
                table_name: _,
                table_id: _,
                first_page,
                schema,
                output_columns,
            } => Executor::SeqScan {
                state: SeqScanState {
                    first_page,
                    schema,
                    output_columns,
                    tuples: Vec::new(),
                    position: 0,
                    opened: false,
                },
                ctx,
            },
            Plan::Filter { input, predicate } => Executor::Filter {
                input: Box::new(Executor::from_plan(*input, ctx)),
                predicate,
            },
            Plan::Projection {
                input,
                exprs,
                output_columns,
            } => Executor::Projection {
                input: Box::new(Executor::from_plan(*input, ctx)),
                exprs,
                output_columns,
            },
        }
    }

    /// Opens the executor, initializing state.
    ///
    /// This must be called before `next()`. For SeqScan, this fetches all
    /// visible tuples from the heap pages into memory.
    pub fn open(
        &mut self,
    ) -> Pin<Box<dyn Future<Output = Result<(), ExecutorError>> + Send + '_>> {
        Box::pin(async move {
            match self {
                Executor::SeqScan { state, ctx } => {
                    if state.opened {
                        return Ok(());
                    }

                    // Scan the heap page and collect visible tuples
                    // NOTE: Multi-page support will be added in Step 15 (FSM).
                    // Currently, each table uses a single page.
                    let guard = ctx
                        .database
                        .pool()
                        .fetch_page(state.first_page)
                        .await
                        .map_err(|e| ExecutorError::Internal {
                            message: format!("failed to fetch page: {}", e),
                        })?;

                    let heap_page = HeapPage::new(guard.data());

                    // Scan tuples on this page
                    for (slot_id, header, record) in heap_page.scan(&state.schema) {
                        // Check MVCC visibility
                        if ctx
                            .snapshot
                            .is_tuple_visible(&header, ctx.database.tx_manager())
                        {
                            let tid = TupleId::new(state.first_page, slot_id);
                            state.tuples.push((tid, header, record));
                        }
                    }

                    state.opened = true;
                    Ok(())
                }
                Executor::Filter { input, .. } => input.open().await,
                Executor::Projection { input, .. } => input.open().await,
            }
        })
    }

    /// Returns the next tuple, or None if exhausted.
    ///
    /// Must call `open()` first.
    pub fn next_tuple(
        &mut self,
    ) -> Pin<Box<dyn Future<Output = Result<Option<Tuple>, ExecutorError>> + Send + '_>> {
        Box::pin(async move {
            match self {
                Executor::SeqScan { state, .. } => {
                    if !state.opened {
                        return Err(ExecutorError::Internal {
                            message: "executor not opened".to_string(),
                        });
                    }

                    if state.position >= state.tuples.len() {
                        return Ok(None);
                    }

                    let (tid, header, record) = state.tuples[state.position].clone();
                    state.position += 1;

                    Ok(Some(Tuple::from_heap(tid, header, record)))
                }

                Executor::Filter { input, predicate } => {
                    // Keep fetching from input until we find a matching tuple
                    while let Some(tuple) = input.next_tuple().await? {
                        if predicate.is_truthy(&tuple.record)? {
                            return Ok(Some(tuple));
                        }
                    }
                    Ok(None)
                }

                Executor::Projection {
                    input,
                    exprs,
                    output_columns: _,
                } => {
                    if let Some(tuple) = input.next_tuple().await? {
                        // Evaluate each projection expression
                        let values: Vec<_> = exprs
                            .iter()
                            .map(|e| e.evaluate(&tuple.record))
                            .collect::<Result<Vec<_>, _>>()?;

                        Ok(Some(Tuple::computed(Record::new(values))))
                    } else {
                        Ok(None)
                    }
                }
            }
        })
    }

    /// Closes the executor, releasing resources.
    ///
    /// Call this when done iterating.
    pub fn close(
        &mut self,
    ) -> Pin<Box<dyn Future<Output = Result<(), ExecutorError>> + Send + '_>> {
        Box::pin(async move {
            match self {
                Executor::SeqScan { state, .. } => {
                    state.tuples.clear();
                    state.position = 0;
                    state.opened = false;
                    Ok(())
                }
                Executor::Filter { input, .. } => input.close().await,
                Executor::Projection { input, .. } => input.close().await,
            }
        })
    }

    /// Returns output column descriptors.
    pub fn output_columns(&self) -> &[ColumnDesc] {
        match self {
            Executor::SeqScan { state, .. } => &state.output_columns,
            Executor::Filter { input, .. } => input.output_columns(),
            Executor::Projection { output_columns, .. } => output_columns,
        }
    }

    /// Collects all tuples into a vector.
    ///
    /// This is a convenience method that opens, iterates, and closes the executor.
    pub async fn collect(mut self) -> Result<Vec<Tuple>, ExecutorError> {
        self.open().await?;

        let mut results = Vec::new();
        while let Some(tuple) = self.next_tuple().await? {
            results.push(tuple);
        }

        self.close().await?;
        Ok(results)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::heap::Value;
    use crate::protocol::type_oid;
    use crate::storage::MemoryStorage;
    use crate::tx::CommandId;

    async fn create_test_db() -> Arc<Database<Arc<MemoryStorage>, crate::storage::LruReplacer>> {
        let storage = Arc::new(MemoryStorage::new());
        Arc::new(Database::open(storage, 100).await.unwrap())
    }

    #[tokio::test]
    async fn test_seqscan_empty_table() {
        let db = create_test_db().await;

        // Create a table
        let mut session = crate::db::Session::new(db.clone());
        session
            .execute_query("CREATE TABLE test (id INT, name TEXT)")
            .await
            .unwrap();

        // Create snapshot and execution context
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);

        // Get table info
        let table_info = db
            .catalog()
            .get_table(&snapshot, "test")
            .await
            .unwrap()
            .unwrap();

        let ctx = ExecutionContext::new(db.clone(), snapshot);

        // Create and execute SeqScan
        let plan = Plan::SeqScan {
            table_name: "test".to_string(),
            table_id: table_info.table_id,
            first_page: table_info.first_page,
            schema: vec![type_oid::INT4, type_oid::TEXT],
            output_columns: vec![
                ColumnDesc::new("id", type_oid::INT4),
                ColumnDesc::new("name", type_oid::TEXT),
            ],
        };

        let executor = Executor::from_plan(plan, ctx);
        let results = executor.collect().await.unwrap();

        assert!(results.is_empty());
    }

    #[tokio::test]
    async fn test_seqscan_catalog_table() {
        // Test scanning a catalog table (sys_tables) which has data after bootstrap
        let db = create_test_db().await;

        // Create snapshot and execution context
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);

        // Get sys_tables info
        let table_info = db
            .catalog()
            .get_table(&snapshot, "sys_tables")
            .await
            .unwrap()
            .unwrap();

        let ctx = ExecutionContext::new(db.clone(), snapshot);

        // sys_tables schema: table_id (INT4), table_name (TEXT), first_page (INT8)
        let plan = Plan::SeqScan {
            table_name: "sys_tables".to_string(),
            table_id: table_info.table_id,
            first_page: table_info.first_page,
            schema: vec![type_oid::INT4, type_oid::TEXT, type_oid::INT8],
            output_columns: vec![
                ColumnDesc::new("table_id", type_oid::INT4),
                ColumnDesc::new("table_name", type_oid::TEXT),
                ColumnDesc::new("first_page", type_oid::INT8),
            ],
        };

        let executor = Executor::from_plan(plan, ctx);
        let results = executor.collect().await.unwrap();

        // sys_tables should contain at least 3 entries (sys_tables, sys_columns, sys_sequences)
        assert!(results.len() >= 3);

        // Verify the first entry is sys_tables
        assert_eq!(results[0].record.values[0], Value::Int32(1)); // table_id = 1
        assert_eq!(
            results[0].record.values[1],
            Value::Text("sys_tables".to_string())
        );
    }

    #[tokio::test]
    async fn test_filter() {
        // Test filtering on sys_tables catalog table
        let db = create_test_db().await;

        // Create snapshot and execution context
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);

        // Get sys_tables info
        let table_info = db
            .catalog()
            .get_table(&snapshot, "sys_tables")
            .await
            .unwrap()
            .unwrap();

        let ctx = ExecutionContext::new(db.clone(), snapshot);

        // Create plan: SELECT * FROM sys_tables WHERE table_id > 1
        // sys_tables schema: table_id (INT4), table_name (TEXT), first_page (INT8)
        let scan = Plan::SeqScan {
            table_name: "sys_tables".to_string(),
            table_id: table_info.table_id,
            first_page: table_info.first_page,
            schema: vec![type_oid::INT4, type_oid::TEXT, type_oid::INT8],
            output_columns: vec![
                ColumnDesc::new("table_id", type_oid::INT4),
                ColumnDesc::new("table_name", type_oid::TEXT),
                ColumnDesc::new("first_page", type_oid::INT8),
            ],
        };

        let filter = Plan::Filter {
            input: Box::new(scan),
            predicate: BoundExpr::BinaryOp {
                left: Box::new(BoundExpr::Column(0)),
                op: crate::sql::BinaryOperator::Gt,
                right: Box::new(BoundExpr::Integer(1)),
            },
        };

        let executor = Executor::from_plan(filter, ctx);
        let results = executor.collect().await.unwrap();

        // Should have sys_columns (table_id=2) and sys_sequences (table_id=3)
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].record.values[0], Value::Int32(2));
        assert_eq!(results[1].record.values[0], Value::Int32(3));
    }

    #[tokio::test]
    async fn test_projection() {
        // Test projection on sys_tables catalog table
        let db = create_test_db().await;

        // Create snapshot and execution context
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);

        // Get sys_tables info
        let table_info = db
            .catalog()
            .get_table(&snapshot, "sys_tables")
            .await
            .unwrap()
            .unwrap();

        let ctx = ExecutionContext::new(db.clone(), snapshot);

        // Create plan: SELECT table_name FROM sys_tables
        // sys_tables schema: table_id (INT4), table_name (TEXT), first_page (INT8)
        let scan = Plan::SeqScan {
            table_name: "sys_tables".to_string(),
            table_id: table_info.table_id,
            first_page: table_info.first_page,
            schema: vec![type_oid::INT4, type_oid::TEXT, type_oid::INT8],
            output_columns: vec![
                ColumnDesc::new("table_id", type_oid::INT4),
                ColumnDesc::new("table_name", type_oid::TEXT),
                ColumnDesc::new("first_page", type_oid::INT8),
            ],
        };

        let projection = Plan::Projection {
            input: Box::new(scan),
            exprs: vec![BoundExpr::Column(1)], // Select only 'table_name'
            output_columns: vec![ColumnDesc::new("table_name", type_oid::TEXT)],
        };

        let executor = Executor::from_plan(projection, ctx);
        let results = executor.collect().await.unwrap();

        // Should have 3 rows (sys_tables, sys_columns, sys_sequences)
        assert_eq!(results.len(), 3);
        assert_eq!(results[0].record.values.len(), 1);
        assert_eq!(
            results[0].record.values[0],
            Value::Text("sys_tables".to_string())
        );
        assert_eq!(
            results[1].record.values[0],
            Value::Text("sys_columns".to_string())
        );
        assert_eq!(
            results[2].record.values[0],
            Value::Text("sys_sequences".to_string())
        );

        // Projected tuples should not have TID (they're computed)
        assert!(results[0].tid.is_none());
    }
}
