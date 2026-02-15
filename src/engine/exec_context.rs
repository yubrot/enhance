//! Concrete execution context backed by engine components.
//!
//! [`ExecContextImpl`] implements the [`ExecContext`](crate::executor::ExecContext)
//! trait, providing storage operations to executor nodes.

use std::sync::Arc;

use crate::catalog::CatalogStore;
use crate::executor::{ExecContext, ExecutorError};
use crate::heap::{Record, TupleId, delete, insert, scan_visible_page, update};
use crate::storage::{BufferPool, PageId, Replacer, Storage};
use crate::tx::{Snapshot, TransactionManager};

/// Concrete [`ExecContext`] backed by a [`BufferPool`], [`TransactionManager`], and [`CatalogStore`].
///
/// Owns `Arc` references to shared components plus a cloned [`Snapshot`]
/// for visibility checks. Cloning is lightweight.
pub struct ExecContextImpl<S: Storage, R: Replacer> {
    pool: Arc<BufferPool<S, R>>,
    tx_manager: Arc<TransactionManager>,
    // NOTE: The `CatalogStore` dependency in `ExecContextImpl` exists solely for `nextval`.
    // A future refactor could extract sequence access into a dedicated trait, removing
    // the `CatalogStore` dependency from the execution context.
    catalog_store: CatalogStore<S, R>,
    snapshot: Snapshot,
}

impl<S: Storage, R: Replacer> Clone for ExecContextImpl<S, R> {
    fn clone(&self) -> Self {
        Self {
            pool: Arc::clone(&self.pool),
            tx_manager: Arc::clone(&self.tx_manager),
            catalog_store: self.catalog_store.clone(),
            snapshot: self.snapshot.clone(),
        }
    }
}

impl<S: Storage, R: Replacer> ExecContextImpl<S, R> {
    /// Creates a new execution context.
    pub fn new(
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
        catalog_store: CatalogStore<S, R>,
        snapshot: Snapshot,
    ) -> Self {
        Self {
            pool,
            tx_manager,
            catalog_store,
            snapshot,
        }
    }
}

impl<S: Storage, R: Replacer> ExecContext for ExecContextImpl<S, R> {
    async fn scan_heap_page(
        &self,
        page_id: PageId,
        schema: &[crate::datum::Type],
    ) -> Result<(Vec<(TupleId, Record)>, Option<PageId>), ExecutorError> {
        Ok(scan_visible_page(
            &self.pool,
            page_id,
            schema,
            &self.snapshot,
            &self.tx_manager,
        )
        .await?)
    }

    async fn insert_tuple(
        &self,
        first_page: PageId,
        record: &Record,
    ) -> Result<TupleId, ExecutorError> {
        Ok(insert(
            &self.pool,
            first_page,
            record,
            self.snapshot.current_txid,
            self.snapshot.current_cid,
        )
        .await?)
    }

    async fn delete_tuple(&self, tid: TupleId) -> Result<(), ExecutorError> {
        Ok(delete(
            &self.pool,
            tid,
            self.snapshot.current_txid,
            self.snapshot.current_cid,
        )
        .await?)
    }

    async fn update_tuple(
        &self,
        first_page: PageId,
        old_tid: TupleId,
        new_record: &Record,
    ) -> Result<TupleId, ExecutorError> {
        Ok(update(
            &self.pool,
            first_page,
            old_tid,
            new_record,
            self.snapshot.current_txid,
            self.snapshot.current_cid,
        )
        .await?)
    }

    async fn nextval(&self, seq_id: u32) -> Result<i64, ExecutorError> {
        Ok(self.catalog_store.nextval(seq_id).await?)
    }
}
