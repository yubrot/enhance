//! In-memory cache for catalog metadata.
//!
//! Provides fast lookups for table and column information by caching
//! catalog data in memory. The cache is invalidated on DDL operations.

use std::collections::HashMap;

use parking_lot::RwLock;

use super::types::{ColumnInfo, TableInfo};

/// In-memory cache for catalog lookups.
///
/// Caches table and column metadata to avoid repeated heap scans
/// for frequently accessed catalog information.
///
/// NOTE: For production, consider adding:
/// - LRU eviction for large catalogs
/// - Cache statistics for monitoring
/// - Bounded cache size
#[derive(Debug)]
pub struct CatalogCache {
    /// table_name -> TableInfo
    tables_by_name: RwLock<HashMap<String, TableInfo>>,
    /// table_id -> Vec<ColumnInfo>
    columns_by_table: RwLock<HashMap<u32, Vec<ColumnInfo>>>,
}

impl CatalogCache {
    /// Creates a new empty cache.
    pub fn new() -> Self {
        Self {
            tables_by_name: RwLock::new(HashMap::new()),
            columns_by_table: RwLock::new(HashMap::new()),
        }
    }

    /// Gets cached table info by name.
    pub fn get_table(&self, name: &str) -> Option<TableInfo> {
        self.tables_by_name.read().get(name).cloned()
    }

    /// Caches table info.
    pub fn put_table(&self, info: TableInfo) {
        self.tables_by_name
            .write()
            .insert(info.table_name.clone(), info);
    }

    /// Gets cached columns for a table.
    pub fn get_columns(&self, table_id: u32) -> Option<Vec<ColumnInfo>> {
        self.columns_by_table.read().get(&table_id).cloned()
    }

    /// Caches columns for a table.
    pub fn put_columns(&self, table_id: u32, columns: Vec<ColumnInfo>) {
        self.columns_by_table.write().insert(table_id, columns);
    }

    /// Invalidates cache entries for a table.
    ///
    /// Called after DDL operations (CREATE TABLE, DROP TABLE) to ensure
    /// cache consistency.
    pub fn invalidate(&self, table_id: u32, table_name: &str) {
        self.tables_by_name.write().remove(table_name);
        self.columns_by_table.write().remove(&table_id);
    }

    /// Clears all cached data.
    ///
    /// Used during testing or after major catalog changes.
    #[allow(dead_code)]
    pub fn clear(&self) {
        self.tables_by_name.write().clear();
        self.columns_by_table.write().clear();
    }
}

impl Default for CatalogCache {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::PageId;

    #[test]
    fn test_cache_table() {
        let cache = CatalogCache::new();

        assert!(cache.get_table("users").is_none());

        let info = TableInfo::new(1, "users".to_string(), PageId::new(10));
        cache.put_table(info.clone());

        assert_eq!(cache.get_table("users"), Some(info));
    }

    #[test]
    fn test_cache_columns() {
        let cache = CatalogCache::new();

        assert!(cache.get_columns(1).is_none());

        let columns = vec![
            ColumnInfo::new(1, 0, "id".to_string(), 23, 1),
            ColumnInfo::new(1, 1, "name".to_string(), 25, 0),
        ];
        cache.put_columns(1, columns.clone());

        assert_eq!(cache.get_columns(1), Some(columns));
    }

    #[test]
    fn test_cache_invalidate() {
        let cache = CatalogCache::new();

        let info = TableInfo::new(1, "users".to_string(), PageId::new(10));
        cache.put_table(info);

        let columns = vec![ColumnInfo::new(1, 0, "id".to_string(), 23, 1)];
        cache.put_columns(1, columns);

        assert!(cache.get_table("users").is_some());
        assert!(cache.get_columns(1).is_some());

        cache.invalidate(1, "users");

        assert!(cache.get_table("users").is_none());
        assert!(cache.get_columns(1).is_none());
    }

    #[test]
    fn test_cache_clear() {
        let cache = CatalogCache::new();

        cache.put_table(TableInfo::new(1, "t1".to_string(), PageId::new(10)));
        cache.put_table(TableInfo::new(2, "t2".to_string(), PageId::new(20)));
        cache.put_columns(1, vec![]);
        cache.put_columns(2, vec![]);

        cache.clear();

        assert!(cache.get_table("t1").is_none());
        assert!(cache.get_table("t2").is_none());
        assert!(cache.get_columns(1).is_none());
        assert!(cache.get_columns(2).is_none());
    }
}
