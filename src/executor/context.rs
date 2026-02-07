//! Execution context for executor nodes.
//!
//! The [`ExecContext`] trait abstracts storage operations needed by executor
//! nodes, keeping them decoupled from concrete `Storage`/`Replacer` types.

use std::future::Future;
use std::sync::Arc;

use crate::datum::Type;
use crate::heap::{HeapPage, Tuple, TupleId};
use crate::storage::{BufferPool, PageId, Replacer, Storage};
use crate::tx::{Snapshot, TransactionManager};

use super::error::ExecutorError;

/// Execution context providing stateless storage operations to executor nodes.
///
/// Implementations are `Clone` so each node can own its own copy.
/// Methods take `&self` because all mutable state (scan position, buffer) is
/// managed by the nodes themselves.
pub trait ExecContext: Send + Clone {
    /// Scans a single heap page and returns all visible tuples.
    ///
    /// Visibility is determined by the snapshot embedded in the context.
    /// The caller provides the column schema for record deserialization.
    fn scan_heap_page(
        &self,
        page_id: PageId,
        schema: &[Type],
    ) -> impl Future<Output = Result<Vec<Tuple>, ExecutorError>> + Send;
}

/// Concrete [`ExecContext`] backed by a [`BufferPool`] and [`TransactionManager`].
///
/// Owns `Arc` references to the buffer pool and transaction manager, plus a
/// cloned [`Snapshot`] for visibility checks. Cloning is lightweight.
pub struct ExecContextImpl<S: Storage, R: Replacer> {
    pool: Arc<BufferPool<S, R>>,
    tx_manager: Arc<TransactionManager>,
    snapshot: Snapshot,
}

// Manual Clone impl to avoid requiring S: Clone + R: Clone
// (only Arc and Snapshot are cloned).
impl<S: Storage, R: Replacer> Clone for ExecContextImpl<S, R> {
    fn clone(&self) -> Self {
        Self {
            pool: Arc::clone(&self.pool),
            tx_manager: Arc::clone(&self.tx_manager),
            snapshot: self.snapshot.clone(),
        }
    }
}

impl<S: Storage, R: Replacer> ExecContextImpl<S, R> {
    /// Creates a new execution context.
    pub fn new(
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
        snapshot: Snapshot,
    ) -> Self {
        Self {
            pool,
            tx_manager,
            snapshot,
        }
    }
}

impl<S: Storage, R: Replacer> ExecContext for ExecContextImpl<S, R> {
    async fn scan_heap_page(
        &self,
        page_id: PageId,
        schema: &[Type],
    ) -> Result<Vec<Tuple>, ExecutorError> {
        let page = HeapPage::new(self.pool.fetch_page(page_id).await?);

        let mut tuples = Vec::new();
        for (slot_id, header, record) in page.scan(schema) {
            if !self.snapshot.is_tuple_visible(&header, &self.tx_manager) {
                continue;
            }
            let tid = TupleId { page_id, slot_id };
            tuples.push(Tuple::from_heap(tid, record));
        }

        Ok(tuples)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::catalog::{SystemCatalogTable, TableInfo};
    use crate::datum::Value;
    use crate::db::Database;
    use crate::storage::MemoryStorage;
    use crate::tx::CommandId;

    #[tokio::test]
    async fn test_exec_context_impl_scan_catalog() {
        // Bootstrap a database to get catalog tables with data
        let storage = MemoryStorage::new();
        let db = Database::open(storage, 100).await.unwrap();

        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);

        // Scan the first page of sys_tables (page 2 after superblock and catalog pages)
        // We don't know the exact page ID, so we rely on the catalog to tell us.
        // For this test, we just verify the context is functional by scanning page 2
        // (which is the sys_tables heap page in a freshly bootstrapped database).
        let table_info = db
            .catalog()
            .get_table(&snapshot, "sys_tables")
            .await
            .unwrap()
            .unwrap();

        let ctx =
            ExecContextImpl::new(Arc::clone(db.pool()), Arc::clone(db.tx_manager()), snapshot);

        let tuples = ctx
            .scan_heap_page(table_info.first_page, &TableInfo::SCHEMA)
            .await
            .unwrap();

        // Should find at least 3 catalog tables (sys_tables, sys_columns, sys_sequences)
        assert!(
            tuples.len() >= 3,
            "expected at least 3 catalog tables, got {}",
            tuples.len()
        );

        // Verify first tuple is sys_tables itself
        assert_eq!(tuples[0].record.values[1], Value::Text("sys_tables".into()));
        // All tuples should have TupleId set
        for tuple in &tuples {
            assert!(tuple.tid.is_some());
        }
    }
}
