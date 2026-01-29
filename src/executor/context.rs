//! Execution context for query processing.
//!
//! The execution context provides access to the snapshot, catalog, buffer pool,
//! and transaction manager needed during query execution.

use std::sync::Arc;

use crate::catalog::Catalog;
use crate::storage::{BufferPool, Replacer, Storage};
use crate::tx::{Snapshot, TransactionManager};

/// Context for query execution.
///
/// This struct holds references to all the infrastructure needed to execute
/// queries, including MVCC snapshot, catalog access, and buffer pool.
pub struct ExecutionContext<'a, S: Storage, R: Replacer> {
    /// MVCC snapshot for visibility determination.
    snapshot: Snapshot,
    /// Catalog for table/column metadata.
    catalog: &'a Catalog<S, R>,
    /// Buffer pool for page access.
    pool: &'a Arc<BufferPool<S, R>>,
    /// Transaction manager for visibility checks.
    tx_manager: &'a Arc<TransactionManager>,
}

impl<'a, S: Storage, R: Replacer> ExecutionContext<'a, S, R> {
    /// Creates a new execution context.
    pub fn new(
        snapshot: Snapshot,
        catalog: &'a Catalog<S, R>,
        pool: &'a Arc<BufferPool<S, R>>,
        tx_manager: &'a Arc<TransactionManager>,
    ) -> Self {
        Self {
            snapshot,
            catalog,
            pool,
            tx_manager,
        }
    }

    /// Returns the MVCC snapshot.
    pub fn snapshot(&self) -> &Snapshot {
        &self.snapshot
    }

    /// Returns the catalog.
    pub fn catalog(&self) -> &'a Catalog<S, R> {
        self.catalog
    }

    /// Returns the buffer pool.
    pub fn pool(&self) -> &'a Arc<BufferPool<S, R>> {
        self.pool
    }

    /// Returns the transaction manager.
    pub fn tx_manager(&self) -> &'a Arc<TransactionManager> {
        self.tx_manager
    }
}
