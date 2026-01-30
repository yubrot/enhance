//! Catalog wrapper with in-memory caching.
//!
//! This module provides the main `Catalog` type that wraps `CatalogInner`
//! with direct HashMap-based caching for fast metadata lookups.

use std::collections::HashMap;
use std::sync::Arc;

use parking_lot::RwLock;

use super::core::Catalog as CatalogInner;
use super::error::CatalogError;
use super::schema::{ColumnInfo, TableInfo};
use super::superblock::Superblock;
use crate::sql::CreateTableStmt;
use crate::storage::{BufferPool, Replacer, Storage};
use crate::tx::{CommandId, Snapshot, TransactionManager, TxId};

/// System catalog with in-memory caching.
///
/// The catalog wraps `CatalogInner` and provides fast cached access to
/// table and column metadata. Cache is invalidated on DDL operations.
///
/// # Architecture
///
/// ```text
/// Database -> Catalog (HashMaps) -> CatalogInner (pure heap scan)
/// ```
pub struct Catalog<S: Storage, R: Replacer> {
    /// Inner catalog store for direct metadata access.
    inner: CatalogInner<S, R>,
    /// Cache: table_name -> TableInfo
    tables_by_name: RwLock<HashMap<String, TableInfo>>,
    /// Cache: table_id -> Vec<ColumnInfo>
    columns_by_table: RwLock<HashMap<u32, Vec<ColumnInfo>>>,
}

impl<S: Storage, R: Replacer> Catalog<S, R> {
    /// Returns the superblock page IDs.
    pub fn superblock(&self) -> Superblock {
        self.inner.superblock()
    }

    /// Creates a new table from a CREATE TABLE statement.
    ///
    /// This method delegates to the inner store and invalidates the cache.
    ///
    /// # Errors
    ///
    /// Returns `CatalogError::TableAlreadyExists` if the table exists.
    pub async fn create_table(
        &self,
        txid: TxId,
        cid: CommandId,
        stmt: &CreateTableStmt,
    ) -> Result<u32, CatalogError> {
        // Delegate to inner store
        let table_id = self.inner.create_table(txid, cid, stmt).await?;

        // Invalidate cache
        self.invalidate_cache(table_id, &stmt.name);

        Ok(table_id)
    }

    /// Looks up a table by name.
    ///
    /// Uses the cache when available, falls back to scanning sys_tables.
    pub async fn get_table(
        &self,
        snapshot: &Snapshot,
        name: &str,
    ) -> Result<Option<TableInfo>, CatalogError> {
        // Check cache first
        if let Some(info) = self.tables_by_name.read().get(name).cloned() {
            return Ok(Some(info));
        }

        // Cache miss - delegate to inner store
        let info = self.inner.get_table(snapshot, name).await?;

        // Cache the result if found
        if let Some(ref table_info) = info {
            self.tables_by_name
                .write()
                .insert(table_info.table_name.clone(), table_info.clone());
        }

        Ok(info)
    }

    /// Gets columns for a table.
    ///
    /// Uses the cache when available, falls back to scanning sys_columns.
    pub async fn get_columns(
        &self,
        snapshot: &Snapshot,
        table_id: u32,
    ) -> Result<Vec<ColumnInfo>, CatalogError> {
        // Check cache first
        if let Some(columns) = self.columns_by_table.read().get(&table_id).cloned() {
            return Ok(columns);
        }

        // Cache miss - delegate to inner store
        let columns = self.inner.get_columns(snapshot, table_id).await?;

        // Cache the result
        self.columns_by_table
            .write()
            .insert(table_id, columns.clone());

        Ok(columns)
    }

    /// Gets the next value from a sequence.
    ///
    /// Sequences are NOT rolled back on transaction abort (following PostgreSQL's behavior).
    /// Each call increments the sequence permanently.
    pub async fn nextval(&self, seq_id: u32) -> Result<i64, CatalogError> {
        self.inner.nextval(seq_id).await
    }

    /// Invalidates cache entries for a table.
    ///
    /// Called after DDL operations (CREATE TABLE, DROP TABLE) to ensure
    /// cache consistency.
    fn invalidate_cache(&self, table_id: u32, table_name: &str) {
        self.tables_by_name.write().remove(table_name);
        self.columns_by_table.write().remove(&table_id);
    }

    /// Bootstraps the catalog for a fresh database.
    ///
    /// Delegates to `CatalogInner::bootstrap` and wraps with cache.
    pub(crate) async fn bootstrap(
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
    ) -> Result<Self, CatalogError> {
        let inner = CatalogInner::bootstrap(pool, tx_manager).await?;

        Ok(Self {
            inner,
            tables_by_name: RwLock::new(HashMap::new()),
            columns_by_table: RwLock::new(HashMap::new()),
        })
    }

    /// Opens an existing catalog from storage.
    ///
    /// Delegates to `CatalogInner::open` and wraps with cache.
    pub(crate) async fn open(
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
    ) -> Result<Self, CatalogError> {
        let inner = CatalogInner::open(pool, tx_manager).await?;

        Ok(Self {
            inner,
            tables_by_name: RwLock::new(HashMap::new()),
            columns_by_table: RwLock::new(HashMap::new()),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::catalog::schema::SystemCatalogTable;
    use crate::sql::{ColumnDef, DataType};
    use crate::storage::{LruReplacer, MemoryStorage};

    struct TestCatalog {
        catalog: Catalog<MemoryStorage, LruReplacer>,
        tx_manager: Arc<TransactionManager>,
    }

    async fn create_test_catalog() -> TestCatalog {
        let storage = MemoryStorage::new();
        let replacer = LruReplacer::new(100);
        let pool = Arc::new(BufferPool::new(storage, replacer, 100));
        let tx_manager = Arc::new(TransactionManager::new());

        let catalog = Catalog::bootstrap(pool, tx_manager.clone()).await.unwrap();

        TestCatalog {
            catalog,
            tx_manager,
        }
    }

    #[tokio::test]
    async fn test_cache_hit() {
        let tc = create_test_catalog().await;
        let txid = tc.tx_manager.begin();
        let snapshot = tc.tx_manager.snapshot(txid, CommandId::FIRST);

        // First call - cache miss, should populate cache
        let table1 = tc.catalog.get_table(&snapshot, "sys_tables").await.unwrap();
        assert!(table1.is_some());

        // Verify cache is populated
        assert!(tc.catalog.tables_by_name.read().contains_key("sys_tables"));

        // Second call - cache hit, should return same result without inner access
        let table2 = tc.catalog.get_table(&snapshot, "sys_tables").await.unwrap();
        assert_eq!(table1, table2);

        tc.tx_manager.commit(txid).unwrap();
    }

    #[tokio::test]
    async fn test_cache_columns() {
        let tc = create_test_catalog().await;
        let txid = tc.tx_manager.begin();
        let snapshot = tc.tx_manager.snapshot(txid, CommandId::FIRST);

        // First call - cache miss
        let cols1 = tc
            .catalog
            .get_columns(&snapshot, TableInfo::TABLE_ID)
            .await
            .unwrap();
        assert_eq!(cols1.len(), 3);

        // Verify cache is populated
        assert!(tc
            .catalog
            .columns_by_table
            .read()
            .contains_key(&TableInfo::TABLE_ID));

        // Second call - cache hit
        let cols2 = tc
            .catalog
            .get_columns(&snapshot, TableInfo::TABLE_ID)
            .await
            .unwrap();
        assert_eq!(cols1, cols2);

        tc.tx_manager.commit(txid).unwrap();
    }

    #[tokio::test]
    async fn test_cache_invalidation_on_create_table() {
        let tc = create_test_catalog().await;
        let txid = tc.tx_manager.begin();
        let cid = CommandId::FIRST;

        let stmt = CreateTableStmt {
            name: "users".to_string(),
            columns: vec![ColumnDef {
                name: "id".to_string(),
                data_type: DataType::Integer,
                constraints: vec![],
            }],
            constraints: vec![],
            if_not_exists: false,
        };

        // Create table and populate cache
        let table_id = tc.catalog.create_table(txid, cid, &stmt).await.unwrap();
        tc.tx_manager.commit(txid).unwrap();

        // Read to populate cache
        let txid2 = tc.tx_manager.begin();
        let snapshot = tc.tx_manager.snapshot(txid2, CommandId::FIRST);
        tc.catalog.get_table(&snapshot, "users").await.unwrap();
        tc.catalog.get_columns(&snapshot, table_id).await.unwrap();

        // Verify cache is populated
        assert!(tc.catalog.tables_by_name.read().contains_key("users"));
        assert!(tc.catalog.columns_by_table.read().contains_key(&table_id));

        // Simulate cache invalidation (in real scenario, this would happen on DDL)
        tc.catalog.invalidate_cache(table_id, "users");

        // Verify cache is cleared
        assert!(!tc.catalog.tables_by_name.read().contains_key("users"));
        assert!(!tc.catalog.columns_by_table.read().contains_key(&table_id));

        tc.tx_manager.commit(txid2).unwrap();
    }
}
