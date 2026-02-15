//! Concrete execution context backed by an [`Engine`] reference.

use std::sync::Arc;

use super::Engine;
use crate::executor::{ExecContext, ExecutorError};
use crate::heap::{Record, TupleId, delete, insert, scan_visible_page, update};
use crate::storage::{PageId, Replacer, Storage};
use crate::tx::Snapshot;

/// Concrete [`ExecContext`] backed by an [`Engine`] and a [`Snapshot`].
pub struct ExecutionPoint<S: Storage, R: Replacer> {
    engine: Arc<Engine<S, R>>,
    snapshot: Snapshot,
}

impl<S: Storage, R: Replacer> Clone for ExecutionPoint<S, R> {
    fn clone(&self) -> Self {
        Self {
            engine: Arc::clone(&self.engine),
            snapshot: self.snapshot.clone(),
        }
    }
}

impl<S: Storage, R: Replacer> ExecutionPoint<S, R> {
    /// Creates a new execution point.
    pub fn new(engine: Arc<Engine<S, R>>, snapshot: Snapshot) -> Self {
        Self { engine, snapshot }
    }
}

impl<S: Storage, R: Replacer> ExecContext for ExecutionPoint<S, R> {
    async fn scan_heap_page(
        &self,
        page_id: PageId,
        schema: &[crate::datum::Type],
    ) -> Result<(Vec<(TupleId, Record)>, Option<PageId>), ExecutorError> {
        Ok(scan_visible_page(
            self.engine.pool(),
            page_id,
            schema,
            &self.snapshot,
            self.engine.tx_manager(),
        )
        .await?)
    }

    async fn insert_tuple(
        &self,
        first_page: PageId,
        record: &Record,
    ) -> Result<TupleId, ExecutorError> {
        Ok(insert(
            self.engine.pool(),
            first_page,
            record,
            self.snapshot.current_txid,
            self.snapshot.current_cid,
        )
        .await?)
    }

    async fn delete_tuple(&self, tid: TupleId) -> Result<(), ExecutorError> {
        Ok(delete(
            self.engine.pool(),
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
            self.engine.pool(),
            first_page,
            old_tid,
            new_record,
            self.snapshot.current_txid,
            self.snapshot.current_cid,
        )
        .await?)
    }

    async fn nextval(&self, seq_id: u32) -> Result<i64, ExecutorError> {
        self.engine.nextval(seq_id).await
    }
}
