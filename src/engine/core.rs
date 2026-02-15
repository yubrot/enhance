//! Engine orchestrator for buffer pool, transaction manager, and catalog.

use std::sync::Arc;

use super::error::EngineError;
use crate::catalog::{Catalog, CatalogCache, CatalogError, CatalogStore};
use crate::executor::ExecContextImpl;
use crate::storage::{BufferPool, LruReplacer, Replacer, Storage};
use crate::tx::{Snapshot, TransactionManager};

/// Engine orchestrates the core components: BufferPool, TransactionManager, and CatalogStore.
///
/// This is the main entry point for database operations. It initializes or opens
/// an existing database and provides access to its components.
pub struct Engine<S: Storage, R: Replacer> {
    pool: Arc<BufferPool<S, R>>,
    tx_manager: Arc<TransactionManager>,
    catalog_store: CatalogStore<S, R>,
    catalog_cache: CatalogCache,
}

impl<S: Storage> Engine<S, LruReplacer> {
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
    pub async fn open(storage: S, pool_size: usize) -> Result<Self, EngineError> {
        let replacer = LruReplacer::new(pool_size);
        Self::open_with_replacer(storage, replacer, pool_size).await
    }
}

impl<S: Storage, R: Replacer> Engine<S, R> {
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
    ) -> Result<Self, EngineError> {
        let pool = Arc::new(BufferPool::new(storage, replacer, pool_size));
        let tx_manager = Arc::new(TransactionManager::new());

        // Check if this is a fresh database
        let catalog_store = match pool.page_count().await {
            0 => CatalogStore::bootstrap(pool.clone(), tx_manager.clone()).await?,
            _ => CatalogStore::open(pool.clone(), tx_manager.clone()).await?,
        };

        Ok(Self {
            pool,
            tx_manager,
            catalog_store,
            catalog_cache: CatalogCache::new(),
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

    /// Returns a reference to the catalog store.
    pub fn catalog_store(&self) -> &CatalogStore<S, R> {
        &self.catalog_store
    }

    /// Returns a reference to the catalog cache.
    pub fn catalog_cache(&self) -> &CatalogCache {
        &self.catalog_cache
    }

    /// Returns a cached [`Catalog`] for the given MVCC snapshot.
    ///
    /// Delegates to [`CatalogCache::get_or_load`], which avoids redundant
    /// heap scans when no DDL has been committed since the last load.
    pub async fn catalog_snapshot(
        &self,
        snapshot: &Snapshot,
    ) -> Result<Arc<Catalog>, CatalogError> {
        self.catalog_cache
            .get_or_load(&self.catalog_store, snapshot, &self.tx_manager)
            .await
    }

    /// Creates an [`ExecContextImpl`] for query execution with the given snapshot.
    pub fn exec_context(&self, snapshot: Snapshot) -> ExecContextImpl<S, R> {
        ExecContextImpl::new(
            Arc::clone(&self.pool),
            Arc::clone(&self.tx_manager),
            self.catalog_store.clone(),
            snapshot,
        )
    }

    /// Flushes all dirty pages to storage.
    ///
    /// This ensures all changes are persisted to disk.
    pub async fn flush(&self) -> Result<(), EngineError> {
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
    async fn test_engine_open() {
        let storage = Arc::new(MemoryStorage::new());
        // First open: should bootstrap a new database
        {
            let engine = Engine::open(Arc::clone(&storage), 100).await.unwrap();

            // Verify catalog is initialized
            let sb = engine.catalog_store().superblock();
            assert_eq!(sb.next_table_id, LAST_RESERVED_TABLE_ID + 1);
            assert!(engine.pool().page_count().await > 0);
        };

        // Second open: should open existing database (not bootstrap)
        {
            let engine = Engine::open(storage, 100).await.unwrap();

            // Verify catalog was opened (not re-bootstrapped)
            let sb = engine.catalog_store().superblock();
            assert_eq!(sb.next_table_id, LAST_RESERVED_TABLE_ID + 1);
        }
    }
}
