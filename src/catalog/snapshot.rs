//! In-memory catalog snapshot for synchronous metadata lookups.

use std::collections::HashMap;

use super::error::CatalogError;
use super::schema::{ColumnInfo, TableInfo};
use super::store::CatalogStore;
use crate::storage::{Replacer, Storage};
use crate::tx::Snapshot;

/// An in-memory, MVCC-consistent view of the system catalog.
///
/// Built by [`CatalogSnapshot::load`], this type holds all table and column
/// metadata visible at a given MVCC snapshot. All lookups are synchronous
/// and carry no generic storage parameters.
pub struct CatalogSnapshot {
    /// Name → table_id index for O(1) name lookups.
    table_ids: HashMap<String, u32>,
    /// table_id → table entry (info + pre-sorted columns).
    tables: HashMap<u32, TableEntry>,
}

/// A table with its pre-grouped, pre-sorted columns.
pub struct TableEntry {
    /// Table metadata.
    pub info: TableInfo,
    /// Columns sorted by `column_num`.
    pub columns: Vec<ColumnInfo>,
}

impl CatalogSnapshot {
    /// Loads all visible catalog data into a new `CatalogSnapshot`.
    ///
    /// Iterates the sys_tables and sys_columns page chains via
    /// [`CatalogStore::scan_tables`] and [`CatalogStore::scan_columns`],
    /// groups columns by table, and returns an immutable in-memory view.
    pub async fn load<S: Storage, R: Replacer>(
        store: &CatalogStore<S, R>,
        snapshot: &Snapshot,
    ) -> Result<Self, CatalogError> {
        let mut tables = Vec::new();
        let mut next_page_id = Some(None);
        while let Some(page_id) = next_page_id {
            let (page_tables, next) = store.scan_tables(snapshot, page_id).await?;
            tables.extend(page_tables);
            next_page_id = next.map(Some);
        }

        let mut columns = Vec::new();
        let mut next_page_id = Some(None);
        while let Some(page_id) = next_page_id {
            let (page_columns, next) = store.scan_columns(snapshot, page_id).await?;
            columns.extend(page_columns);
            next_page_id = next.map(Some);
        }

        Ok(Self::new(tables, columns))
    }

    /// Creates a new `CatalogSnapshot` from preloaded table and column data.
    fn new(tables: Vec<TableInfo>, columns: Vec<ColumnInfo>) -> Self {
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
    use crate::catalog::LAST_RESERVED_TABLE_ID;
    use crate::catalog::schema::{SequenceInfo, SystemCatalogTable};
    use crate::datum::Type;
    use crate::sql::{Parser, Statement};
    use crate::storage::{BufferPool, LruReplacer, MemoryStorage, PageId};
    use crate::tx::{CommandId, TransactionManager};
    use std::sync::Arc;

    /// Bootstraps a `CatalogStore` backed by in-memory storage for testing.
    ///
    /// NOTE: This helper is duplicated in `cache::tests`. Extract into a shared
    /// test utility if catalog test modules continue to grow.
    async fn bootstrap_store() -> (
        CatalogStore<MemoryStorage, LruReplacer>,
        Arc<TransactionManager>,
    ) {
        let storage = MemoryStorage::new();
        let replacer = LruReplacer::new(100);
        let pool = Arc::new(BufferPool::new(storage, replacer, 100));
        let tx_manager = Arc::new(TransactionManager::new());
        let store = CatalogStore::bootstrap(pool, tx_manager.clone())
            .await
            .unwrap();
        (store, tx_manager)
    }

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
        let snap = CatalogSnapshot::new(sample_tables(), sample_columns());

        let entry = snap.resolve_table("users").unwrap();
        assert_eq!(entry.info.table_id, 100);
        assert_eq!(entry.info.table_name, "users");
        assert_eq!(entry.columns.len(), 2);
        // Should be sorted by column_num despite being inserted out of order
        assert_eq!(entry.columns[0].column_name, "id");
        assert_eq!(entry.columns[0].column_num, 0);
        assert_eq!(entry.columns[1].column_name, "name");
        assert_eq!(entry.columns[1].column_num, 1);

        let entry = snap.resolve_table("sys_tables").unwrap();
        assert_eq!(entry.info.table_id, 1);

        assert!(snap.resolve_table("nonexistent").is_none());
    }

    #[test]
    fn test_resolve_table_by_id() {
        let snap = CatalogSnapshot::new(sample_tables(), sample_columns());

        let entry = snap.resolve_table_by_id(100).unwrap();
        assert_eq!(entry.info.table_name, "users");

        assert!(snap.resolve_table_by_id(999).is_none());
    }

    #[test]
    fn test_empty_snapshot() {
        let snap = CatalogSnapshot::new(vec![], vec![]);
        assert!(snap.resolve_table("anything").is_none());
        assert!(snap.resolve_table_by_id(1).is_none());
    }

    #[test]
    fn test_table_with_no_columns() {
        let tables = vec![TableInfo::new(100, "empty".to_string(), PageId::new(4))];
        let snap = CatalogSnapshot::new(tables, vec![]);

        let entry = snap.resolve_table("empty").unwrap();
        assert_eq!(entry.info.table_id, 100);
        assert!(entry.columns.is_empty());
    }

    // --- Integration tests using CatalogStore ---

    #[tokio::test]
    async fn test_load_system_tables() {
        let (store, tx_manager) = bootstrap_store().await;
        let txid = tx_manager.begin();
        let snapshot = tx_manager.snapshot(txid, CommandId::FIRST);

        let snap = CatalogSnapshot::load(&store, &snapshot).await.unwrap();

        // Should contain the 3 system catalog tables
        assert_eq!(
            snap.resolve_table("sys_tables").unwrap().info.table_id,
            TableInfo::TABLE_ID
        );
        assert_eq!(
            snap.resolve_table("sys_columns").unwrap().info.table_id,
            ColumnInfo::TABLE_ID
        );
        assert_eq!(
            snap.resolve_table("sys_sequences").unwrap().info.table_id,
            SequenceInfo::TABLE_ID
        );

        // sys_tables should have 3 columns
        let entry = snap.resolve_table_by_id(TableInfo::TABLE_ID).unwrap();
        assert_eq!(entry.columns.len(), 3);
        assert_eq!(entry.columns[0].column_name, "table_id");
        assert_eq!(entry.columns[1].column_name, "table_name");
        assert_eq!(entry.columns[2].column_name, "first_page");
    }

    #[tokio::test]
    async fn test_load_with_user_table() {
        let (store, tx_manager) = bootstrap_store().await;
        let txid = tx_manager.begin();
        let cid = CommandId::FIRST;

        let Ok(Some(Statement::CreateTable(stmt))) =
            Parser::new("CREATE TABLE users (id SERIAL, name TEXT)").parse()
        else {
            panic!("expected CreateTable");
        };

        store.create_table(txid, cid, &stmt).await.unwrap();
        tx_manager.commit(txid).unwrap();

        // Load snapshot with a new transaction
        let txid2 = tx_manager.begin();
        let snapshot = tx_manager.snapshot(txid2, CommandId::FIRST);
        let snap = CatalogSnapshot::load(&store, &snapshot).await.unwrap();

        let entry = snap.resolve_table("users").unwrap();
        assert_eq!(entry.info.table_id, LAST_RESERVED_TABLE_ID + 1);
        assert_eq!(entry.columns.len(), 2);
        assert_eq!(entry.columns[0].column_name, "id");
        assert!(entry.columns[0].is_serial());
        assert_eq!(entry.columns[1].column_name, "name");
        assert!(!entry.columns[1].is_serial());
    }

    #[tokio::test]
    async fn test_load_uncommitted_not_visible() {
        let (store, tx_manager) = bootstrap_store().await;
        let txid = tx_manager.begin();
        let cid = CommandId::FIRST;

        let Ok(Some(Statement::CreateTable(stmt))) =
            Parser::new("CREATE TABLE invisible (id INTEGER)").parse()
        else {
            panic!("expected CreateTable");
        };

        store.create_table(txid, cid, &stmt).await.unwrap();
        // Do NOT commit

        // Another transaction should not see the uncommitted table
        let txid2 = tx_manager.begin();
        let snapshot = tx_manager.snapshot(txid2, CommandId::FIRST);
        let snap = CatalogSnapshot::load(&store, &snapshot).await.unwrap();

        assert!(snap.resolve_table("invisible").is_none());
    }
}
