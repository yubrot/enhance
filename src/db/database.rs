//! Database orchestrator for buffer pool, transaction manager, and catalog.

use std::sync::Arc;

use super::error::DatabaseError;
use crate::catalog::Catalog;
use crate::storage::{BufferPool, LruReplacer, Replacer, Storage};
use crate::tx::TransactionManager;

/// Database orchestrates the core components: BufferPool, TransactionManager, and Catalog.
///
/// This is the main entry point for database operations. It initializes or opens
/// an existing database and provides access to its components.
///
/// # Example
///
/// ```no_run
/// use enhance::db::Database;
/// use enhance::storage::FileStorage;
///
/// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let storage = FileStorage::open("enhance.db").await?;
/// let db = Database::open(storage, 1000).await?;
///
/// // Access components
/// let pool = db.pool();
/// let tx_manager = db.tx_manager();
/// let catalog = db.catalog();
/// # Ok(())
/// # }
/// ```
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
    /// # Arguments
    ///
    /// * `storage` - Storage backend (MemoryStorage or FileStorage)
    /// * `replacer` - Page replacement policy
    /// * `pool_size` - Number of buffer pool frames
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
        let page_count = pool.page_count().await;
        let catalog = if page_count == 0 {
            // Bootstrap new database
            println!("Initializing new database...");
            Catalog::bootstrap(pool.clone(), tx_manager.clone()).await?
        } else {
            // Open existing database
            println!("Opening existing database ({} pages)...", page_count);
            Catalog::open(pool.clone(), tx_manager.clone()).await?
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
    use crate::catalog::table_id;
    use crate::sql::{ColumnDef, CreateTableStmt, DataType};
    use crate::storage::MemoryStorage;
    use crate::tx::CommandId;

    #[tokio::test]
    async fn test_database_bootstrap() {
        let storage = MemoryStorage::new();
        let db = Database::open(storage, 100).await.unwrap();

        // Verify catalog is initialized
        let sb = db.catalog().superblock();
        assert_eq!(sb.next_table_id, table_id::FIRST_USER_TABLE);
    }

    #[tokio::test]
    async fn test_database_create_table() {
        let storage = MemoryStorage::new();
        let db = Database::open(storage, 100).await.unwrap();

        // Create a table
        let txid = db.tx_manager().begin();
        let cid = CommandId::FIRST;

        let stmt = CreateTableStmt {
            name: "test_table".to_string(),
            columns: vec![
                ColumnDef {
                    name: "id".to_string(),
                    data_type: DataType::Integer,
                    constraints: vec![],
                },
                ColumnDef {
                    name: "name".to_string(),
                    data_type: DataType::Text,
                    constraints: vec![],
                },
            ],
            constraints: vec![],
            if_not_exists: false,
        };

        let table_id = db.catalog().create_table(txid, cid, &stmt).await.unwrap();
        assert_eq!(table_id, table_id::FIRST_USER_TABLE);

        db.tx_manager().commit(txid).unwrap();

        // Verify table exists
        let txid2 = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid2, CommandId::FIRST);

        let table = db
            .catalog()
            .get_table(&snapshot, "test_table")
            .await
            .unwrap();
        assert!(table.is_some());
        assert_eq!(table.unwrap().table_id, table_id::FIRST_USER_TABLE);

        db.tx_manager().commit(txid2).unwrap();
    }

    #[tokio::test]
    async fn test_database_catalog_lookup() {
        let storage = MemoryStorage::new();
        let db = Database::open(storage, 100).await.unwrap();

        // Verify catalog tables are accessible
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);

        let table = db
            .catalog()
            .get_table(&snapshot, "sys_tables")
            .await
            .unwrap();
        assert!(table.is_some());

        db.tx_manager().commit(txid).unwrap();
    }
}
