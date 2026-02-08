//! Database orchestrator for buffer pool, transaction manager, and catalog.

use std::sync::Arc;

use super::error::DatabaseError;
use crate::catalog::Catalog;
use crate::executor::ExecContextImpl;
use crate::storage::{BufferPool, LruReplacer, Replacer, Storage};
use crate::tx::{Snapshot, TransactionManager};

/// Database orchestrates the core components: BufferPool, TransactionManager, and Catalog.
///
/// This is the main entry point for database operations. It initializes or opens
/// an existing database and provides access to its components.
pub struct Database<S: Storage, R: Replacer> {
    pool: Arc<BufferPool<S, R>>,
    tx_manager: Arc<TransactionManager>,
    catalog: Catalog<S, R>,
}

impl<S: Storage> Database<S, LruReplacer> {
    /// Opens or initializes a database with LRU replacement policy.
    ///
    /// If the storage is empty (page_count == 0), bootstraps a new database.
    /// Otherwise, opens the existing database and validates the superblock.
    ///
    /// # Arguments
    ///
    /// * `storage` - Storage backend (MemoryStorage or FileStorage)
    /// * `pool_size` - Number of buffer pool frames
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Storage I/O fails
    /// - Superblock validation fails (invalid magic or version)
    pub async fn open(storage: S, pool_size: usize) -> Result<Self, DatabaseError> {
        let replacer = LruReplacer::new(pool_size);
        Self::open_with_replacer(storage, replacer, pool_size).await
    }
}

impl<S: Storage, R: Replacer> Database<S, R> {
    /// Opens or initializes a database with a custom replacement policy.
    ///
    /// If the storage is empty (page_count == 0), bootstraps a new database.
    /// Otherwise, opens the existing database and validates the superblock.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Storage I/O fails
    /// - Superblock validation fails (invalid magic or version)
    pub async fn open_with_replacer(
        storage: S,
        replacer: R,
        pool_size: usize,
    ) -> Result<Self, DatabaseError> {
        let pool = Arc::new(BufferPool::new(storage, replacer, pool_size));
        let tx_manager = Arc::new(TransactionManager::new());

        // Check if this is a fresh database
        let catalog = match pool.page_count().await {
            0 => Catalog::bootstrap(pool.clone(), tx_manager.clone()).await?,
            _ => Catalog::open(pool.clone(), tx_manager.clone()).await?,
        };

        Ok(Self {
            pool,
            tx_manager,
            catalog,
        })
    }

    /// Returns a reference to the buffer pool.
    pub fn pool(&self) -> &Arc<BufferPool<S, R>> {
        &self.pool
    }

    /// Returns a reference to the transaction manager.
    pub fn tx_manager(&self) -> &Arc<TransactionManager> {
        &self.tx_manager
    }

    /// Returns a reference to the catalog.
    pub fn catalog(&self) -> &Catalog<S, R> {
        &self.catalog
    }

    /// Creates an [`ExecContextImpl`] for query execution with the given snapshot.
    pub fn exec_context(&self, snapshot: Snapshot) -> ExecContextImpl<S, R> {
        ExecContextImpl::new(
            Arc::clone(&self.pool),
            Arc::clone(&self.tx_manager),
            snapshot,
        )
    }

    /// Flushes all dirty pages to storage.
    ///
    /// This ensures all changes are persisted to disk.
    pub async fn flush(&self) -> Result<(), DatabaseError> {
        self.pool.flush_all().await?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::catalog::LAST_RESERVED_TABLE_ID;
    use crate::storage::MemoryStorage;

    #[tokio::test]
    async fn test_database_open() {
        let storage = Arc::new(MemoryStorage::new());
        // First open: should bootstrap a new database
        {
            let db = Database::open(Arc::clone(&storage), 100).await.unwrap();

            // Verify catalog is initialized
            let sb = db.catalog().superblock();
            assert_eq!(sb.next_table_id, LAST_RESERVED_TABLE_ID + 1);
            assert!(db.pool().page_count().await > 0);
        };

        // Second open: should open existing database (not bootstrap)
        {
            let db = Database::open(storage, 100).await.unwrap();

            // Verify catalog was opened (not re-bootstrapped)
            let sb = db.catalog().superblock();
            assert_eq!(sb.next_table_id, LAST_RESERVED_TABLE_ID + 1);
        }
    }
}
