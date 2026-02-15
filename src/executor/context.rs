//! Execution context for executor nodes.
//!
//! The [`ExecContext`] trait abstracts storage operations needed by executor
//! nodes, keeping them decoupled from concrete `Storage`/`Replacer` types.

use std::future::Future;

use crate::datum::Type;
use crate::heap::{Record, TupleId};
use crate::storage::PageId;

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
