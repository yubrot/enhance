//! System catalog for table and column metadata.
//!
//! This module manages metadata about tables, columns, and sequences.
//! Schema types ([`TableInfo`], [`ColumnInfo`], [`SequenceInfo`]) describe
//! catalog rows, [`CatalogCache`] provides MVCC-aware caching, and
//! [`Catalog`] is the in-memory snapshot used by the planner and executor.
//!
//! ## Catalog Tables
//!
//! | Table Name      | Rust Type        | Description                     |
//! |-----------------|------------------|---------------------------------|
//! | `sys_tables`    | [`TableInfo`]    | Table metadata (id, name, page) |
//! | `sys_columns`   | [`ColumnInfo`]   | Column metadata per table       |
//! | `sys_sequences` | [`SequenceInfo`] | SERIAL column sequences         |
//!
//! ## Usage
//!
//! The catalog is accessed through the [`Engine`](crate::engine::Engine) type,
//! which orchestrates the buffer pool, transaction manager, and catalog.

mod cache;
mod schema;

pub use cache::CatalogCache;
pub use schema::{ColumnInfo, LAST_RESERVED_TABLE_ID, SequenceInfo, SystemCatalogTable, TableInfo};

use std::collections::HashMap;

/// A table with its pre-grouped, pre-sorted columns.
pub struct TableEntry {
    /// Table metadata.
    pub info: TableInfo,
    /// Columns sorted by `column_num`.
    pub columns: Vec<ColumnInfo>,
}

/// An in-memory, MVCC-consistent view of the system catalog.
///
/// Built by [`Engine::load_catalog`](crate::engine::Engine), this type holds
/// all table and column metadata visible at a given MVCC snapshot. All lookups
/// are synchronous and carry no generic storage parameters.
pub struct Catalog {
    /// Name → table_id index for O(1) name lookups.
    table_ids: HashMap<String, u32>,
    /// table_id → table entry (info + pre-sorted columns).
    tables: HashMap<u32, TableEntry>,
}

impl Catalog {
    /// Creates a new `Catalog` from preloaded table and column data.
    pub(crate) fn new(tables: Vec<TableInfo>, columns: Vec<ColumnInfo>) -> Self {
        let mut table_ids = HashMap::with_capacity(tables.len());
        let mut table_entries = HashMap::with_capacity(tables.len());

        for info in tables {
            let columns = Vec::new();
            table_ids.insert(info.table_name.clone(), info.table_id);
            table_entries.insert(info.table_id, TableEntry { info, columns });
        }
        for col in columns {
            if let Some(table_entry) = table_entries.get_mut(&col.table_id) {
                table_entry.columns.push(col);
            }
            // NOTE: Orphaned columns whose table_id has no matching table are
            // silently dropped. Production systems should log a warning.
        }
        for table_entry in table_entries.values_mut() {
            table_entry.columns.sort_by_key(|c| c.column_num);
        }

        Self {
            table_ids,
            tables: table_entries,
        }
    }

    /// Resolves a table by name, returning its metadata and columns.
    pub fn resolve_table(&self, name: &str) -> Option<&TableEntry> {
        let &table_id = self.table_ids.get(name)?;
        self.tables.get(&table_id)
    }

    /// Resolves a table by ID, returning its metadata and columns.
    pub fn resolve_table_by_id(&self, table_id: u32) -> Option<&TableEntry> {
        self.tables.get(&table_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::datum::Type;
    use crate::storage::PageId;

    fn sample_tables() -> Vec<TableInfo> {
        vec![
            TableInfo::new(1, "sys_tables".to_string(), PageId::new(1)),
            TableInfo::new(100, "users".to_string(), PageId::new(4)),
        ]
    }

    fn sample_columns() -> Vec<ColumnInfo> {
        vec![
            // sys_tables columns
            ColumnInfo::new(1, 0, "table_id".to_string(), Type::Integer, 0),
            ColumnInfo::new(1, 1, "table_name".to_string(), Type::Text, 0),
            ColumnInfo::new(1, 2, "first_page".to_string(), Type::Bigint, 0),
            // users columns (inserted out of order to test sorting)
            ColumnInfo::new(100, 1, "name".to_string(), Type::Text, 0),
            ColumnInfo::new(100, 0, "id".to_string(), Type::Integer, 1),
        ]
    }

    #[test]
    fn test_resolve_table_by_name() {
        let catalog = Catalog::new(sample_tables(), sample_columns());

        let entry = catalog.resolve_table("users").unwrap();
        assert_eq!(entry.info.table_id, 100);
        assert_eq!(entry.info.table_name, "users");
        assert_eq!(entry.columns.len(), 2);
        // Should be sorted by column_num despite being inserted out of order
        assert_eq!(entry.columns[0].column_name, "id");
        assert_eq!(entry.columns[0].column_num, 0);
        assert_eq!(entry.columns[1].column_name, "name");
        assert_eq!(entry.columns[1].column_num, 1);

        let entry = catalog.resolve_table("sys_tables").unwrap();
        assert_eq!(entry.info.table_id, 1);

        assert!(catalog.resolve_table("nonexistent").is_none());
    }

    #[test]
    fn test_resolve_table_by_id() {
        let catalog = Catalog::new(sample_tables(), sample_columns());

        let entry = catalog.resolve_table_by_id(100).unwrap();
        assert_eq!(entry.info.table_name, "users");

        assert!(catalog.resolve_table_by_id(999).is_none());
    }

    #[test]
    fn test_empty_catalog() {
        let catalog = Catalog::new(vec![], vec![]);
        assert!(catalog.resolve_table("anything").is_none());
        assert!(catalog.resolve_table_by_id(1).is_none());
    }

    #[test]
    fn test_table_with_no_columns() {
        let tables = vec![TableInfo::new(100, "empty".to_string(), PageId::new(4))];
        let catalog = Catalog::new(tables, vec![]);

        let entry = catalog.resolve_table("empty").unwrap();
        assert_eq!(entry.info.table_id, 100);
        assert!(entry.columns.is_empty());
    }
}
