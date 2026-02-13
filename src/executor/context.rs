//! Execution context for executor nodes.
//!
//! The [`ExecContext`] trait abstracts storage operations needed by executor
//! nodes, keeping them decoupled from concrete `Storage`/`Replacer` types.

use std::future::Future;
use std::sync::Arc;

use crate::catalog::CatalogStore;
use crate::datum::Type;
use crate::heap::{Record, TupleId, delete, insert, scan_visible_page, update};
use crate::storage::{BufferPool, PageId, Replacer, Storage};
use crate::tx::{Snapshot, TransactionManager};

use super::error::ExecutorError;

/// Result of scanning a single heap page: visible tuples and the next page link.
type ScanPageResult = Result<(Vec<(TupleId, Record)>, Option<PageId>), ExecutorError>;

/// Execution context providing storage operations to executor nodes.
///
/// Implementations are `Clone` so each node can own its own copy.
/// Methods take `&self` because all mutable state (scan position, buffer) is
/// managed by the nodes themselves.
pub trait ExecContext: Send + Clone {
    /// Scans a single heap page and returns all visible tuples.
    ///
    /// Returns `(TupleId, Record)` pairs for each MVCC-visible tuple on the
    /// page, plus the next page ID in the chain (if any) so that the caller
    /// can continue scanning multi-page tables.
    ///
    /// Visibility is determined by the snapshot embedded in the context.
    /// The caller provides the column schema for record deserialization.
    fn scan_heap_page(
        &self,
        page_id: PageId,
        schema: &[Type],
    ) -> impl Future<Output = ScanPageResult> + Send;

    /// Inserts a tuple into the heap table starting at `first_page`.
    ///
    /// Walks the page chain to find free space; allocates new pages when full.
    /// Sets xmin to the current transaction, cid to the current command.
    fn insert_tuple(
        &self,
        first_page: PageId,
        record: &Record,
    ) -> impl Future<Output = Result<TupleId, ExecutorError>> + Send;

    /// Deletes a tuple by setting its xmax to the current transaction.
    ///
    /// The tuple remains physically on the page but becomes invisible to
    /// subsequent snapshots.
    fn delete_tuple(&self, tid: TupleId) -> impl Future<Output = Result<(), ExecutorError>> + Send;

    /// Updates a tuple (delete old version + insert new version).
    ///
    /// Attempts same-page insertion first to avoid unnecessary page chain
    /// traversal. Falls back to `insert_tuple` on the table's first page
    /// if the same page is full.
    fn update_tuple(
        &self,
        first_page: PageId,
        old_tid: TupleId,
        new_record: &Record,
    ) -> impl Future<Output = Result<TupleId, ExecutorError>> + Send;

    /// Gets the next value from a sequence.
    ///
    /// Sequences are NOT rolled back on transaction abort (following PostgreSQL behavior).
    fn nextval(&self, seq_id: u32) -> impl Future<Output = Result<i64, ExecutorError>> + Send;
}

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
    catalog: CatalogStore<S, R>,
    snapshot: Snapshot,
}

impl<S: Storage, R: Replacer> Clone for ExecContextImpl<S, R> {
    fn clone(&self) -> Self {
        Self {
            pool: Arc::clone(&self.pool),
            tx_manager: Arc::clone(&self.tx_manager),
            catalog: self.catalog.clone(),
            snapshot: self.snapshot.clone(),
        }
    }
}

impl<S: Storage, R: Replacer> ExecContextImpl<S, R> {
    /// Creates a new execution context.
    pub fn new(
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
        catalog: CatalogStore<S, R>,
        snapshot: Snapshot,
    ) -> Self {
        Self {
            pool,
            tx_manager,
            catalog,
            snapshot,
        }
    }
}

impl<S: Storage, R: Replacer> ExecContext for ExecContextImpl<S, R> {
    async fn scan_heap_page(&self, page_id: PageId, schema: &[Type]) -> ScanPageResult {
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
        Ok(self.catalog.nextval(seq_id).await?)
    }
}
