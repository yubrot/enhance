//! Main catalog implementation for table and column metadata management.

use std::sync::Arc;

use parking_lot::Mutex;

use super::cache::CatalogCache;
use super::error::CatalogError;
use super::schema::{ColumnInfo, SequenceInfo, TableInfo, LAST_RESERVED_TABLE_ID};
use super::superblock::{Superblock, SUPERBLOCK_MAGIC, SUPERBLOCK_VERSION};
use crate::heap::{HeapPage, SlotId};
use crate::sql::{CreateTableStmt, DataType};
use crate::storage::{BufferPool, PageId, Replacer, Storage};
use crate::tx::{CommandId, Snapshot, TransactionManager, TxId};

/// System catalog for managing table and column metadata.
///
/// The catalog stores metadata about tables, columns, and sequences in
/// self-hosted heap tables (sys_tables, sys_columns, sys_sequences).
///
/// Each catalog table uses a single page for simplicity. Multi-page
/// support will be added in Step 15 with FSM.
pub struct Catalog<S: Storage, R: Replacer> {
    /// Buffer pool for page access.
    pool: Arc<BufferPool<S, R>>,
    /// Transaction manager for MVCC.
    tx_manager: Arc<TransactionManager>,
    /// Superblock with catalog metadata (protected for updates).
    superblock: Mutex<Superblock>,
    /// In-memory cache for fast lookups.
    cache: CatalogCache,
}

impl<S: Storage, R: Replacer> Catalog<S, R> {
    /// Creates a new catalog with the given components.
    ///
    /// This is an internal constructor; use `Database::open()` to initialize
    /// the catalog properly.
    pub(crate) fn new(
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
        superblock: Superblock,
    ) -> Self {
        Self {
            pool,
            tx_manager,
            superblock: Mutex::new(superblock),
            cache: CatalogCache::new(),
        }
    }

    /// Returns the superblock page IDs.
    pub fn superblock(&self) -> Superblock {
        *self.superblock.lock()
    }

    /// Creates a new table from a CREATE TABLE statement.
    ///
    /// This method:
    /// 1. Checks if table already exists
    /// 2. Allocates a table ID
    /// 3. Creates sequences for SERIAL columns
    /// 4. Allocates a heap page for the table
    /// 5. Inserts metadata into sys_tables and sys_columns
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
        // Check if table already exists
        let snapshot = self.tx_manager.snapshot(txid, cid);
        if self.get_table(&snapshot, &stmt.name).await?.is_some() {
            if stmt.if_not_exists {
                // Return 0 to indicate no new table was created
                return Ok(0);
            }
            return Err(CatalogError::TableAlreadyExists {
                name: stmt.name.clone(),
            });
        }

        // Allocate table ID (lock released before await)
        let table_id = {
            let mut sb = self.superblock.lock();
            sb.allocate_table_id()
        };

        // Allocate a new page for the table data
        let first_page = {
            let mut page_guard = self.pool.new_page().await?;
            let page_id = page_guard.page_id();
            HeapPage::new(page_guard.data_mut()).init();
            page_id
        };

        // Process columns and create sequences for SERIAL columns
        let mut columns = Vec::with_capacity(stmt.columns.len());
        for (col_num, col_def) in stmt.columns.iter().enumerate() {
            let type_oid = col_def.data_type.to_oid();

            let seq_id = if col_def.data_type == DataType::Serial {
                // Create sequence for SERIAL column
                let seq_name = format!("{}_{}_seq", stmt.name, col_def.name);
                self.create_sequence(txid, cid, &seq_name).await?
            } else {
                0 // No sequence
            };

            columns.push(ColumnInfo::new(
                table_id,
                col_num as u32,
                col_def.name.clone(),
                type_oid,
                seq_id,
            ));
        }

        // Insert into sys_tables
        self.insert_table(txid, cid, table_id, &stmt.name, first_page)
            .await?;

        // Insert into sys_columns
        for col in &columns {
            self.insert_column(txid, cid, col).await?;
        }

        // Persist superblock
        self.flush_superblock().await?;

        // Invalidate cache (new table, so nothing to invalidate, but good practice)
        self.cache.invalidate(table_id, &stmt.name);

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
        if let Some(info) = self.cache.get_table(name) {
            return Ok(Some(info));
        }

        // Scan sys_tables
        let sys_tables_page = { self.superblock.lock().sys_tables_page };

        let guard = self.pool.fetch_page(sys_tables_page).await?;
        let page = HeapPage::new(guard.data());

        for (_slot_id, header, record) in page.scan(&TableInfo::SCHEMA) {
            if !snapshot.is_tuple_visible(&header, &self.tx_manager) {
                continue;
            }

            let Some(info) = TableInfo::from_record(&record) else {
                continue;
            };

            if info.table_name == name {
                self.cache.put_table(info.clone());
                return Ok(Some(info));
            }
        }

        Ok(None)
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
        if let Some(columns) = self.cache.get_columns(table_id) {
            return Ok(columns);
        }

        // Scan sys_columns
        let sys_columns_page = { self.superblock.lock().sys_columns_page };

        let guard = self.pool.fetch_page(sys_columns_page).await?;
        let page = HeapPage::new(guard.data());

        let mut columns = Vec::new();
        for (_slot_id, header, record) in page.scan(&ColumnInfo::SCHEMA) {
            if !snapshot.is_tuple_visible(&header, &self.tx_manager) {
                continue;
            }

            let Some(col) = ColumnInfo::from_record(&record) else {
                continue;
            };

            if col.table_id != table_id {
                continue;
            }

            columns.push(col);
        }

        // Sort by column_num
        columns.sort_by_key(|c| c.column_num);

        self.cache.put_columns(table_id, columns.clone());
        Ok(columns)
    }

    /// Gets the next value from a sequence.
    ///
    /// Sequences are NOT rolled back on transaction abort (following PostgreSQL's behavior).
    /// Each call increments the sequence permanently.
    pub async fn nextval(&self, seq_id: u32) -> Result<i64, CatalogError> {
        let sys_sequences_page = { self.superblock.lock().sys_sequences_page };

        let mut guard = self.pool.fetch_page_mut(sys_sequences_page).await?;
        let mut page = HeapPage::new(guard.data_mut());

        // Find and update the sequence
        for (slot_id, header, record) in page.scan(&SequenceInfo::SCHEMA).collect::<Vec<_>>() {
            let Some(seq) = SequenceInfo::from_record(&record) else {
                continue;
            };

            if seq.seq_id != seq_id {
                continue;
            }

            let current_val = seq.next_val;

            // Create updated record with incremented value
            let updated_seq = SequenceInfo::new(seq.seq_id, seq.seq_name, current_val + 1);

            // Mark old tuple as deleted and insert new one
            // For now, we just update the header's xmax and insert a new tuple
            // This is a simplified approach - full MVCC update would be more complex
            let mut new_header = header;
            new_header.xmax = TxId::new(1); // Mark as deleted by a dummy transaction
            new_header.cmax = CommandId::FIRST;
            page.update_header(slot_id, new_header)?;

            // Insert new tuple
            page.insert(&updated_seq.to_record(), TxId::new(1), CommandId::FIRST)?;

            return Ok(current_val);
        }

        Err(CatalogError::SequenceNotFound { seq_id })
    }

    /// Creates a new sequence.
    async fn create_sequence(
        &self,
        txid: TxId,
        cid: CommandId,
        name: &str,
    ) -> Result<u32, CatalogError> {
        let seq_id = {
            let mut sb = self.superblock.lock();
            sb.allocate_seq_id()
        };

        let sys_sequences_page = { self.superblock.lock().sys_sequences_page };

        let seq = SequenceInfo::new(seq_id, name.to_string(), 1); // Start at 1

        let mut guard = self.pool.fetch_page_mut(sys_sequences_page).await?;
        let mut page = HeapPage::new(guard.data_mut());
        page.insert(&seq.to_record(), txid, cid)
            .map_err(|_| CatalogError::PageFull)?;

        Ok(seq_id)
    }

    /// Inserts a table record into sys_tables.
    async fn insert_table(
        &self,
        txid: TxId,
        cid: CommandId,
        table_id: u32,
        name: &str,
        first_page: PageId,
    ) -> Result<SlotId, CatalogError> {
        let sys_tables_page = { self.superblock.lock().sys_tables_page };

        let table = TableInfo::new(table_id, name.to_string(), first_page);

        let mut guard = self.pool.fetch_page_mut(sys_tables_page).await?;
        let mut page = HeapPage::new(guard.data_mut());
        let slot_id = page
            .insert(&table.to_record(), txid, cid)
            .map_err(|_| CatalogError::PageFull)?;

        Ok(slot_id)
    }

    /// Inserts a column record into sys_columns.
    async fn insert_column(
        &self,
        txid: TxId,
        cid: CommandId,
        col: &ColumnInfo,
    ) -> Result<SlotId, CatalogError> {
        let sys_columns_page = { self.superblock.lock().sys_columns_page };

        let mut guard = self.pool.fetch_page_mut(sys_columns_page).await?;
        let mut page = HeapPage::new(guard.data_mut());
        let slot_id = page
            .insert(&col.to_record(), txid, cid)
            .map_err(|_| CatalogError::PageFull)?;

        Ok(slot_id)
    }

    /// Flushes the superblock to page 0.
    async fn flush_superblock(&self) -> Result<(), CatalogError> {
        let sb = { *self.superblock.lock() };
        let mut guard = self.pool.fetch_page_mut(PageId::new(0)).await?;
        sb.write(guard.data_mut());
        Ok(())
    }

    /// Bootstraps the catalog for a fresh database.
    ///
    /// This creates the initial catalog pages and inserts metadata
    /// for the catalog tables themselves.
    pub(crate) async fn bootstrap(
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
    ) -> Result<Self, CatalogError> {
        // Allocate superblock page (page 0)
        let mut sb_guard = pool.new_page().await?;
        assert_eq!(sb_guard.page_id(), PageId::new(0), "First page must be 0");
        sb_guard.data_mut().fill(0);
        drop(sb_guard);

        // Allocate catalog pages
        let mut sys_tables_guard = pool.new_page().await?;
        let sys_tables_page = sys_tables_guard.page_id();
        HeapPage::new(sys_tables_guard.data_mut()).init();
        drop(sys_tables_guard);

        let mut sys_columns_guard = pool.new_page().await?;
        let sys_columns_page = sys_columns_guard.page_id();
        HeapPage::new(sys_columns_guard.data_mut()).init();
        drop(sys_columns_guard);

        let mut sys_sequences_guard = pool.new_page().await?;
        let sys_sequences_page = sys_sequences_guard.page_id();
        HeapPage::new(sys_sequences_guard.data_mut()).init();
        drop(sys_sequences_guard);

        // Initialize superblock
        let mut superblock = Superblock::new();
        superblock.sys_tables_page = sys_tables_page;
        superblock.sys_columns_page = sys_columns_page;
        superblock.sys_sequences_page = sys_sequences_page;
        superblock.next_table_id = LAST_RESERVED_TABLE_ID + 1;
        superblock.next_seq_id = 1;

        // Write superblock
        let mut sb_guard = pool.fetch_page_mut(PageId::new(0)).await?;
        superblock.write(sb_guard.data_mut());
        drop(sb_guard);

        // Begin bootstrap transaction
        let txid = tx_manager.begin();
        let cid = CommandId::FIRST;

        // Insert catalog table metadata into sys_tables
        {
            let mut guard = pool.fetch_page_mut(sys_tables_page).await?;
            let mut page = HeapPage::new(guard.data_mut());

            // sys_tables entry
            let sys_tables_info = TableInfo::new(
                TableInfo::TABLE_ID,
                "sys_tables".to_string(),
                sys_tables_page,
            );
            page.insert(&sys_tables_info.to_record(), txid, cid)?;

            // sys_columns entry
            let sys_columns_info = TableInfo::new(
                ColumnInfo::TABLE_ID,
                "sys_columns".to_string(),
                sys_columns_page,
            );
            page.insert(&sys_columns_info.to_record(), txid, cid)?;

            // sys_sequences entry
            let sys_sequences_info = TableInfo::new(
                SequenceInfo::TABLE_ID,
                "sys_sequences".to_string(),
                sys_sequences_page,
            );
            page.insert(&sys_sequences_info.to_record(), txid, cid)?;
        }

        // Insert column metadata into sys_columns
        {
            use crate::protocol::type_oid;

            let mut guard = pool.fetch_page_mut(sys_columns_page).await?;
            let mut page = HeapPage::new(guard.data_mut());

            // sys_tables columns (3 columns)
            let sys_tables_cols = [
                ("table_id", type_oid::INT4),
                ("table_name", type_oid::TEXT),
                ("first_page", type_oid::INT8),
            ];
            for (i, (name, oid)) in sys_tables_cols.iter().enumerate() {
                let col =
                    ColumnInfo::new(TableInfo::TABLE_ID, i as u32, name.to_string(), *oid, 0);
                page.insert(&col.to_record(), txid, cid)?;
            }

            // sys_columns columns (5 columns)
            let sys_columns_cols = [
                ("table_id", type_oid::INT4),
                ("column_num", type_oid::INT4),
                ("column_name", type_oid::TEXT),
                ("type_oid", type_oid::INT4),
                ("seq_id", type_oid::INT4),
            ];
            for (i, (name, oid)) in sys_columns_cols.iter().enumerate() {
                let col =
                    ColumnInfo::new(ColumnInfo::TABLE_ID, i as u32, name.to_string(), *oid, 0);
                page.insert(&col.to_record(), txid, cid)?;
            }

            // sys_sequences columns (3 columns)
            let sys_sequences_cols = [
                ("seq_id", type_oid::INT4),
                ("seq_name", type_oid::TEXT),
                ("next_val", type_oid::INT8),
            ];
            for (i, (name, oid)) in sys_sequences_cols.iter().enumerate() {
                let col = ColumnInfo::new(
                    SequenceInfo::TABLE_ID,
                    i as u32,
                    name.to_string(),
                    *oid,
                    0,
                );
                page.insert(&col.to_record(), txid, cid)?;
            }
        }

        // Commit bootstrap transaction
        tx_manager.commit(txid).expect("bootstrap commit failed");

        // Flush all pages
        pool.flush_all().await?;

        Ok(Self::new(pool, tx_manager, superblock))
    }

    /// Opens an existing catalog from storage.
    pub(crate) async fn open(
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
    ) -> Result<Self, CatalogError> {
        // Read superblock from page 0
        let guard = pool.fetch_page(PageId::new(0)).await?;
        let superblock = Superblock::read(guard.data());
        drop(guard);

        // Validate superblock
        if superblock.magic != SUPERBLOCK_MAGIC {
            return Err(CatalogError::InvalidMagic {
                expected: SUPERBLOCK_MAGIC,
                found: superblock.magic,
            });
        }
        if superblock.version != SUPERBLOCK_VERSION {
            return Err(CatalogError::UnsupportedVersion {
                expected: SUPERBLOCK_VERSION,
                found: superblock.version,
            });
        }

        Ok(Self::new(pool, tx_manager, superblock))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sql::{ColumnDef, DataType};
    use crate::storage::{LruReplacer, MemoryStorage};

    async fn create_test_catalog() -> Catalog<MemoryStorage, LruReplacer> {
        let storage = MemoryStorage::new();
        let replacer = LruReplacer::new(100);
        let pool = Arc::new(BufferPool::new(storage, replacer, 100));
        let tx_manager = Arc::new(TransactionManager::new());

        Catalog::bootstrap(pool, tx_manager).await.unwrap()
    }

    #[tokio::test]
    async fn test_bootstrap_creates_catalog() {
        let catalog = create_test_catalog().await;
        let sb = catalog.superblock();

        assert_eq!(sb.magic, SUPERBLOCK_MAGIC);
        assert_eq!(sb.version, SUPERBLOCK_VERSION);
        assert_eq!(sb.sys_tables_page, PageId::new(1));
        assert_eq!(sb.sys_columns_page, PageId::new(2));
        assert_eq!(sb.sys_sequences_page, PageId::new(3));
        assert_eq!(sb.next_table_id, LAST_RESERVED_TABLE_ID + 1);
    }

    #[tokio::test]
    async fn test_get_catalog_tables() {
        let catalog = create_test_catalog().await;
        let txid = catalog.tx_manager.begin();
        let snapshot = catalog.tx_manager.snapshot(txid, CommandId::FIRST);

        // Should find sys_tables
        let table = catalog.get_table(&snapshot, "sys_tables").await.unwrap();
        assert!(table.is_some());
        let table = table.unwrap();
        assert_eq!(table.table_id, TableInfo::TABLE_ID);
        assert_eq!(table.table_name, "sys_tables");

        // Should find sys_columns
        let table = catalog.get_table(&snapshot, "sys_columns").await.unwrap();
        assert!(table.is_some());

        // Should not find non-existent table
        let table = catalog.get_table(&snapshot, "nonexistent").await.unwrap();
        assert!(table.is_none());

        catalog.tx_manager.commit(txid).unwrap();
    }

    #[tokio::test]
    async fn test_get_columns() {
        let catalog = create_test_catalog().await;
        let txid = catalog.tx_manager.begin();
        let snapshot = catalog.tx_manager.snapshot(txid, CommandId::FIRST);

        // Get sys_tables columns
        let columns = catalog
            .get_columns(&snapshot, TableInfo::TABLE_ID)
            .await
            .unwrap();

        assert_eq!(columns.len(), 3);
        assert_eq!(columns[0].column_name, "table_id");
        assert_eq!(columns[1].column_name, "table_name");
        assert_eq!(columns[2].column_name, "first_page");

        catalog.tx_manager.commit(txid).unwrap();
    }

    #[tokio::test]
    async fn test_create_table() {
        let catalog = create_test_catalog().await;
        let txid = catalog.tx_manager.begin();
        let cid = CommandId::FIRST;

        let stmt = CreateTableStmt {
            name: "users".to_string(),
            columns: vec![
                ColumnDef {
                    name: "id".to_string(),
                    data_type: DataType::Serial,
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

        let table_id = catalog.create_table(txid, cid, &stmt).await.unwrap();
        assert_eq!(table_id, LAST_RESERVED_TABLE_ID + 1);

        catalog.tx_manager.commit(txid).unwrap();

        // Verify table exists
        let txid2 = catalog.tx_manager.begin();
        let snapshot = catalog.tx_manager.snapshot(txid2, CommandId::FIRST);

        let table = catalog.get_table(&snapshot, "users").await.unwrap();
        assert!(table.is_some());
        let table = table.unwrap();
        assert_eq!(table.table_id, LAST_RESERVED_TABLE_ID + 1);

        // Verify columns
        let columns = catalog.get_columns(&snapshot, table.table_id).await.unwrap();
        assert_eq!(columns.len(), 2);
        assert_eq!(columns[0].column_name, "id");
        assert!(columns[0].is_serial());
        assert_eq!(columns[1].column_name, "name");
        assert!(!columns[1].is_serial());

        catalog.tx_manager.commit(txid2).unwrap();
    }

    #[tokio::test]
    async fn test_create_table_already_exists() {
        let catalog = create_test_catalog().await;
        let txid = catalog.tx_manager.begin();
        let cid = CommandId::FIRST;

        let stmt = CreateTableStmt {
            name: "test".to_string(),
            columns: vec![ColumnDef {
                name: "id".to_string(),
                data_type: DataType::Integer,
                constraints: vec![],
            }],
            constraints: vec![],
            if_not_exists: false,
        };

        catalog.create_table(txid, cid, &stmt).await.unwrap();
        catalog.tx_manager.commit(txid).unwrap();

        // Try to create again
        let txid2 = catalog.tx_manager.begin();
        let result = catalog.create_table(txid2, cid, &stmt).await;
        assert!(matches!(result, Err(CatalogError::TableAlreadyExists { .. })));
        catalog.tx_manager.abort(txid2).unwrap();
    }

    #[tokio::test]
    async fn test_create_table_if_not_exists() {
        let catalog = create_test_catalog().await;
        let txid = catalog.tx_manager.begin();
        let cid = CommandId::FIRST;

        let stmt = CreateTableStmt {
            name: "test".to_string(),
            columns: vec![ColumnDef {
                name: "id".to_string(),
                data_type: DataType::Integer,
                constraints: vec![],
            }],
            constraints: vec![],
            if_not_exists: true,
        };

        let table_id = catalog.create_table(txid, cid, &stmt).await.unwrap();
        assert!(table_id > 0);
        catalog.tx_manager.commit(txid).unwrap();

        // Try to create again with IF NOT EXISTS
        let txid2 = catalog.tx_manager.begin();
        let table_id2 = catalog.create_table(txid2, cid, &stmt).await.unwrap();
        assert_eq!(table_id2, 0); // Returns 0 when table already exists
        catalog.tx_manager.commit(txid2).unwrap();
    }
}
