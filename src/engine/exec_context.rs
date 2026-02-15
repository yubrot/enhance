//! Concrete execution context backed by engine components.
//!
//! [`ExecContextImpl`] implements the [`ExecContext`](crate::executor::ExecContext)
//! trait, providing storage operations to executor nodes.

use std::sync::Arc;

use parking_lot::RwLock;

use crate::catalog::{CatalogError, SequenceInfo, Superblock, SystemCatalogTable};
use crate::executor::{ExecContext, ExecutorError};
use crate::heap::{HeapPage, Record, TupleId, delete, insert, scan_visible_page, update};
use crate::storage::{BufferPool, PageId, Replacer, Storage};
use crate::tx::{Snapshot, TransactionManager};

/// Concrete [`ExecContext`] backed by a [`BufferPool`], [`TransactionManager`], and [`Superblock`].
///
/// Owns `Arc` references to shared components plus a cloned [`Snapshot`]
/// for visibility checks. Cloning is lightweight.
pub struct ExecContextImpl<S: Storage, R: Replacer> {
    pool: Arc<BufferPool<S, R>>,
    tx_manager: Arc<TransactionManager>,
    superblock: Arc<RwLock<Superblock>>,
    snapshot: Snapshot,
}

impl<S: Storage, R: Replacer> Clone for ExecContextImpl<S, R> {
    fn clone(&self) -> Self {
        Self {
            pool: Arc::clone(&self.pool),
            tx_manager: Arc::clone(&self.tx_manager),
            superblock: Arc::clone(&self.superblock),
            snapshot: self.snapshot.clone(),
        }
    }
}

impl<S: Storage, R: Replacer> ExecContextImpl<S, R> {
    /// Creates a new execution context.
    pub fn new(
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
        superblock: Arc<RwLock<Superblock>>,
        snapshot: Snapshot,
    ) -> Self {
        Self {
            pool,
            tx_manager,
            superblock,
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
        Ok(nextval_impl(&self.pool, &self.superblock, seq_id).await?)
    }
}

/// Shared nextval implementation used by both [`Engine::nextval`](super::core::Engine::nextval)
/// and [`ExecContextImpl::nextval`].
///
/// Sequences are NOT rolled back on transaction abort (following PostgreSQL's behavior).
/// Each call increments the sequence permanently, independent of transaction state.
pub(super) async fn nextval_impl<S: Storage, R: Replacer>(
    pool: &BufferPool<S, R>,
    superblock: &RwLock<Superblock>,
    seq_id: u32,
) -> Result<i64, CatalogError> {
    // The page latch is held during the entire operation to ensure atomicity.
    let sys_sequences_page = superblock.read().sys_sequences_page;
    let mut page = HeapPage::new(pool.fetch_page_mut(sys_sequences_page, true).await?);

    // Find the sequence
    let (slot_id, mut seq) = page
        .scan(SequenceInfo::SCHEMA)
        .find_map(|(slot_id, _header, record)| {
            let seq = SequenceInfo::from_record(&record)?;
            (seq.seq_id == seq_id).then_some((slot_id, seq))
        })
        .ok_or(CatalogError::SequenceNotFound { seq_id })?;

    let current_val = seq.next_val;
    seq.next_val += 1;

    // Update record in-place, bypassing MVCC
    // The record size is unchanged (same seq_name, only next_val differs)
    page.update_record_in_place(slot_id, &seq.to_record())?;

    Ok(current_val)
}
