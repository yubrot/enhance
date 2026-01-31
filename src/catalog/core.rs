//! Catalog for table and column metadata management.
//!
//! This module provides pure metadata accessor without caching.
//! For cached access, use the `Catalog` wrapper in `cached.rs`.

use std::sync::Arc;

use parking_lot::Mutex;

use super::error::CatalogError;
use super::schema::{ColumnInfo, SequenceInfo, SystemCatalogTable, TableInfo};
use super::superblock::Superblock;
use crate::heap::HeapPage;
use crate::sql::{CreateTableStmt, DataType};
use crate::storage::{BufferPool, PageId, Replacer, Storage};
use crate::tx::{CommandId, Snapshot, TransactionManager, TxId};

/// Catalog for managing table and column metadata.
///
/// The catalog provides direct access to metadata stored in self-hosted
/// heap tables (sys_tables, sys_columns, sys_sequences).
///
/// This is a low-level store without caching. Use `catalog::cached::Catalog`
/// wrapper for efficient access.
///
/// Each catalog table uses a single page for simplicity. Multi-page
/// support will be added in Step 15 with FSM.
pub(super) struct Catalog<S: Storage, R: Replacer> {
    /// Buffer pool for page access.
    pool: Arc<BufferPool<S, R>>,
    /// Transaction manager for MVCC.
    tx_manager: Arc<TransactionManager>,
    /// Superblock with catalog metadata (protected for updates).
    superblock: Mutex<Superblock>,
}

impl<S: Storage, R: Replacer> Catalog<S, R> {
    /// Creates a new catalog with the given components.
    ///
    /// This is an internal constructor; use `Catalog::bootstrap()` or
    /// `Catalog::open()` to initialize the catalog properly.
    fn new(
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
        superblock: Superblock,
    ) -> Self {
        Self {
            pool,
            tx_manager,
            superblock: Mutex::new(superblock),
        }
    }

    /// Bootstraps the catalog for a fresh database.
    ///
    /// This creates the initial catalog pages and inserts metadata
    /// for the catalog tables themselves.
    ///
    /// NOTE: Without WAL (Step 13), crash during bootstrap leaves the
    /// database in an inconsistent state that cannot be recovered.
    pub(super) async fn bootstrap(
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
    ) -> Result<Self, CatalogError> {
        let mut sb_guard = pool.new_page().await?;
        // NOTE: Using assert_eq! here panics instead of returning an error.
        // Production code should return CatalogError::InvalidSuperblock or similar.
        assert_eq!(sb_guard.page_id(), PageId::new(0), "First page must be 0");
        sb_guard.data_mut().fill(0);
        drop(sb_guard);

        let sys_tables_guard = pool.new_page().await?;
        let sys_tables_page = sys_tables_guard.page_id();
        HeapPage::new(sys_tables_guard).init();

        let sys_columns_guard = pool.new_page().await?;
        let sys_columns_page = sys_columns_guard.page_id();
        HeapPage::new(sys_columns_guard).init();

        let sys_sequences_guard = pool.new_page().await?;
        let sys_sequences_page = sys_sequences_guard.page_id();
        HeapPage::new(sys_sequences_guard).init();

        let mut superblock = Superblock::new();
        superblock.sys_tables_page = sys_tables_page;
        superblock.sys_columns_page = sys_columns_page;
        superblock.sys_sequences_page = sys_sequences_page;
        superblock.next_table_id = super::schema::LAST_RESERVED_TABLE_ID + 1;
        superblock.next_seq_id = 1;

        let mut sb_guard = pool.fetch_page_mut(PageId::new(0)).await?;
        superblock.write(sb_guard.data_mut());
        drop(sb_guard);

        // Begin bootstrap transaction
        let txid = tx_manager.begin();
        let cid = CommandId::FIRST;

        // Insert catalog table metadata into sys_tables
        {
            let mut page = HeapPage::new(pool.fetch_page_mut(sys_tables_page).await?);

            // sys_tables entry
            let table_info = TableInfo::table_info(sys_tables_page);
            page.insert(&table_info.to_record(), txid, cid)?;

            // sys_columns entry
            let table_info = ColumnInfo::table_info(sys_columns_page);
            page.insert(&table_info.to_record(), txid, cid)?;

            // sys_sequences entry
            let table_info = SequenceInfo::table_info(sys_sequences_page);
            page.insert(&table_info.to_record(), txid, cid)?;
        }

        // Insert column metadata into sys_columns
        {
            let mut page = HeapPage::new(pool.fetch_page_mut(sys_columns_page).await?);

            for (i, (name, oid)) in TableInfo::columns().into_iter().enumerate() {
                let col = ColumnInfo::new(TableInfo::TABLE_ID, i as u32, name.to_string(), oid, 0);
                page.insert(&col.to_record(), txid, cid)?;
            }

            for (i, (name, oid)) in ColumnInfo::columns().into_iter().enumerate() {
                let col = ColumnInfo::new(ColumnInfo::TABLE_ID, i as u32, name.to_string(), oid, 0);
                page.insert(&col.to_record(), txid, cid)?;
            }

            for (i, (name, oid)) in SequenceInfo::columns().into_iter().enumerate() {
                let col =
                    ColumnInfo::new(SequenceInfo::TABLE_ID, i as u32, name.to_string(), oid, 0);
                page.insert(&col.to_record(), txid, cid)?;
            }
        }

        pool.flush_all().await?;

        // NOTE: Using expect() here panics if commit fails. Production code should
        // return an error. However, bootstrap commit should never fail in practice
        // since there are no conflicts and no integrity constraints to violate.
        tx_manager.commit(txid).expect("bootstrap commit failed");

        Ok(Self::new(pool, tx_manager, superblock))
    }

    /// Opens an existing catalog from storage.
    pub(super) async fn open(
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
    ) -> Result<Self, CatalogError> {
        // Read superblock from page 0
        let guard = pool.fetch_page(PageId::new(0)).await?;
        let superblock = Superblock::read(guard.data());
        drop(guard);

        // Validate superblock
        superblock.validate()?;

        // Create catalog store
        Ok(Self::new(pool, tx_manager, superblock))
    }

    /// Returns the superblock.
    pub(super) fn superblock(&self) -> Superblock {
        *self.superblock.lock()
    }

    /// Flushes the superblock to persistent storage with immediate fsync.
    ///
    /// The superblock is outside the WAL system (it contains WAL metadata itself),
    /// so we must ensure durability through immediate fsync.
    async fn flush_superblock(&self) -> Result<(), CatalogError> {
        let sb = *self.superblock.lock();
        let mut guard = self.pool.fetch_page_mut(PageId::new(0)).await?;
        sb.write(guard.data_mut());
        drop(guard);

        // Flush and fsync the superblock page
        self.pool.flush_page(PageId::new(0)).await?;
        self.pool.storage().sync_all().await?;

        Ok(())
    }

    /// Looks up a table by name.
    ///
    /// Scans sys_tables to find the table metadata.
    pub(super) async fn get_table(
        &self,
        snapshot: &Snapshot,
        name: &str,
    ) -> Result<Option<TableInfo>, CatalogError> {
        let sys_tables_page = self.superblock.lock().sys_tables_page;
        let page = HeapPage::new(self.pool.fetch_page(sys_tables_page).await?);

        for (_slot_id, header, record) in page.scan(TableInfo::SCHEMA) {
            if !snapshot.is_tuple_visible(&header, &self.tx_manager) {
                continue;
            }

            let Some(info) = TableInfo::from_record(&record) else {
                // NOTE: from_record() returns None when deserialization fails, indicating
                // possible data corruption. For learning purposes, we silently skip.
                // Production systems should either:
                // - Log corruption warnings and attempt recovery
                // - Return CatalogError::CorruptedMetadata to fail fast
                // - Use checksums (Step 13) to detect corruption earlier
                continue;
            };

            if info.table_name == name {
                return Ok(Some(info));
            }
        }

        Ok(None)
    }

    /// Gets columns for a table.
    ///
    /// Scans sys_columns to find the column metadata.
    pub(super) async fn get_columns(
        &self,
        snapshot: &Snapshot,
        table_id: u32,
    ) -> Result<Vec<ColumnInfo>, CatalogError> {
        let sys_columns_page = self.superblock.lock().sys_columns_page;
        let page = HeapPage::new(self.pool.fetch_page(sys_columns_page).await?);

        let mut columns = Vec::new();
        for (_slot_id, header, record) in page.scan(ColumnInfo::SCHEMA) {
            if !snapshot.is_tuple_visible(&header, &self.tx_manager) {
                continue;
            }

            let Some(col) = ColumnInfo::from_record(&record) else {
                // NOTE: Silently skipping corrupted records. See get_table() for details.
                continue;
            };

            if col.table_id != table_id {
                continue;
            }

            columns.push(col);
        }

        // Sort by column_num
        columns.sort_by_key(|c| c.column_num);

        Ok(columns)
    }

    /// Inserts a table record into sys_tables.
    async fn insert_table(
        &self,
        txid: TxId,
        cid: CommandId,
        table_id: u32,
        name: &str,
        first_page: PageId,
    ) -> Result<(), CatalogError> {
        let sys_tables_page = self.superblock.lock().sys_tables_page;
        HeapPage::new(self.pool.fetch_page_mut(sys_tables_page).await?).insert(
            &TableInfo::new(table_id, name.to_string(), first_page).to_record(),
            txid,
            cid,
        )?;
        Ok(())
    }

    /// Inserts a column record into sys_columns.
    async fn insert_column(
        &self,
        txid: TxId,
        cid: CommandId,
        col: &ColumnInfo,
    ) -> Result<(), CatalogError> {
        let sys_columns_page = self.superblock.lock().sys_columns_page;
        HeapPage::new(self.pool.fetch_page_mut(sys_columns_page).await?).insert(
            &col.to_record(),
            txid,
            cid,
        )?;
        Ok(())
    }

    /// Creates a new table from a CREATE TABLE statement.
    ///
    /// This method:
    /// 1. Checks if table already exists
    /// 2. Allocates a table ID and immediately persists the superblock
    /// 3. Creates sequences for SERIAL columns
    /// 4. Allocates a heap page for the table
    /// 5. Inserts metadata into sys_tables and sys_columns
    ///
    /// # Errors
    ///
    /// Returns `CatalogError::TableAlreadyExists` if the table exists.
    ///
    /// NOTE: Table IDs are allocated eagerly and persisted immediately (step 2)
    /// to ensure uniqueness even across transaction aborts. If the transaction
    /// aborts after ID allocation, the ID is permanently consumed by design.
    /// This matches PostgreSQL's behavior for OID allocation.
    pub(super) async fn create_table(
        &self,
        txid: TxId,
        cid: CommandId,
        stmt: &CreateTableStmt,
    ) -> Result<u32, CatalogError> {
        // Check if table already exists
        // NOTE: This check-then-insert pattern is not atomic without proper locking
        // or unique constraints.
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

        // Allocate table ID and persist immediately to ensure uniqueness
        // even if the transaction aborts or crashes occur later.
        let table_id = {
            let mut sb = self.superblock.lock();
            sb.allocate_table_id()
        };
        self.flush_superblock().await?;

        let first_page = {
            let page_guard = self.pool.new_page().await?;
            let page_id = page_guard.page_id();
            HeapPage::new(page_guard).init();
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

        Ok(table_id)
    }

    /// Gets the next value from a sequence.
    ///
    /// Sequences are NOT rolled back on transaction abort (following PostgreSQL's behavior).
    /// Each call increments the sequence permanently, independent of transaction state.
    ///
    /// NOTE: Uses TxId::FROZEN for sequence updates to ensure:
    /// - Updates are immediately visible to all transactions (no MVCC isolation)
    /// - Updates are never rolled back (sequence guarantees monotonic increment)
    ///
    /// This matches PostgreSQL's sequence behavior where nextval() is transactional
    /// in terms of returning unique values, but the increment itself is permanent.
    ///
    /// Production systems typically use:
    /// - In-place updates bypassing MVCC entirely
    /// - Separate sequence storage outside heap tables
    /// - Sequence caching and lock-free algorithms for high concurrency
    pub(super) async fn nextval(&self, seq_id: u32) -> Result<i64, CatalogError> {
        let sys_sequences_page = self.superblock.lock().sys_sequences_page;
        let mut page = HeapPage::new(self.pool.fetch_page_mut(sys_sequences_page).await?);

        // Find and update the sequence
        for (slot_id, header, record) in page.scan(SequenceInfo::SCHEMA).collect::<Vec<_>>() {
            let Some(seq) = SequenceInfo::from_record(&record) else {
                continue;
            };

            if seq.seq_id != seq_id {
                continue;
            }

            let current_val = seq.next_val;

            // Create updated record with incremented value
            let updated_seq = SequenceInfo::new(seq.seq_id, seq.seq_name, current_val + 1);

            // Mark old tuple as deleted and insert new one using FROZEN transaction
            // This ensures the update is immediately visible and never rolled back
            let mut new_header = header;
            new_header.xmax = TxId::FROZEN;
            new_header.cmax = CommandId::FIRST;
            page.update_header(slot_id, new_header)?;

            // Insert new tuple with FROZEN so it's visible to all transactions
            page.insert(&updated_seq.to_record(), TxId::FROZEN, CommandId::FIRST)?;

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
        // Allocate sequence ID and persist immediately to ensure uniqueness
        let seq_id = self.superblock.lock().allocate_seq_id();
        self.flush_superblock().await?;

        let sys_sequences_page = self.superblock.lock().sys_sequences_page;

        let seq = SequenceInfo::new(seq_id, name.to_string(), 1); // Start at 1

        let mut page = HeapPage::new(self.pool.fetch_page_mut(sys_sequences_page).await?);
        page.insert(&seq.to_record(), txid, cid)?;

        Ok(seq_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::catalog::LAST_RESERVED_TABLE_ID;
    use crate::catalog::schema::SystemCatalogTable;
    use crate::sql::{ColumnDef, DataType};
    use crate::storage::{LruReplacer, MemoryStorage, PageId};

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
    async fn test_bootstrap_creates_catalog() {
        let tc = create_test_catalog().await;
        let sb = tc.catalog.superblock();

        assert!(sb.validate().is_ok());
        assert_eq!(sb.sys_tables_page, PageId::new(1));
        assert_eq!(sb.sys_columns_page, PageId::new(2));
        assert_eq!(sb.sys_sequences_page, PageId::new(3));
        assert_eq!(sb.next_table_id, LAST_RESERVED_TABLE_ID + 1);
    }

    #[tokio::test]
    async fn test_get_catalog_tables() {
        let tc = create_test_catalog().await;
        let txid = tc.tx_manager.begin();
        let snapshot = tc.tx_manager.snapshot(txid, CommandId::FIRST);

        // Should find sys_tables
        let table = tc.catalog.get_table(&snapshot, "sys_tables").await.unwrap();
        assert!(table.is_some());
        let table = table.unwrap();
        assert_eq!(table.table_id, TableInfo::TABLE_ID);
        assert_eq!(table.table_name, "sys_tables");

        // Should find sys_columns
        let table = tc
            .catalog
            .get_table(&snapshot, "sys_columns")
            .await
            .unwrap();
        assert!(table.is_some());

        // Should not find non-existent table
        let table = tc
            .catalog
            .get_table(&snapshot, "nonexistent")
            .await
            .unwrap();
        assert!(table.is_none());

        tc.tx_manager.commit(txid).unwrap();
    }

    #[tokio::test]
    async fn test_get_columns() {
        let tc = create_test_catalog().await;
        let txid = tc.tx_manager.begin();
        let snapshot = tc.tx_manager.snapshot(txid, CommandId::FIRST);

        // Get sys_tables columns
        let columns = tc
            .catalog
            .get_columns(&snapshot, TableInfo::TABLE_ID)
            .await
            .unwrap();

        assert_eq!(columns.len(), 3);
        assert_eq!(columns[0].column_name, "table_id");
        assert_eq!(columns[1].column_name, "table_name");
        assert_eq!(columns[2].column_name, "first_page");

        tc.tx_manager.commit(txid).unwrap();
    }

    #[tokio::test]
    async fn test_create_table() {
        let tc = create_test_catalog().await;
        let txid = tc.tx_manager.begin();
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

        let table_id = tc.catalog.create_table(txid, cid, &stmt).await.unwrap();
        assert_eq!(table_id, LAST_RESERVED_TABLE_ID + 1);

        tc.tx_manager.commit(txid).unwrap();

        // Verify table exists
        let txid2 = tc.tx_manager.begin();
        let snapshot = tc.tx_manager.snapshot(txid2, CommandId::FIRST);

        let table = tc.catalog.get_table(&snapshot, "users").await.unwrap();
        assert!(table.is_some());
        let table = table.unwrap();
        assert_eq!(table.table_id, LAST_RESERVED_TABLE_ID + 1);

        // Verify columns
        let columns = tc
            .catalog
            .get_columns(&snapshot, table.table_id)
            .await
            .unwrap();
        assert_eq!(columns.len(), 2);
        assert_eq!(columns[0].column_name, "id");
        assert!(columns[0].is_serial());
        assert_eq!(columns[1].column_name, "name");
        assert!(!columns[1].is_serial());

        tc.tx_manager.commit(txid2).unwrap();
    }

    #[tokio::test]
    async fn test_create_table_already_exists() {
        let tc = create_test_catalog().await;
        let txid = tc.tx_manager.begin();
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

        tc.catalog.create_table(txid, cid, &stmt).await.unwrap();
        tc.tx_manager.commit(txid).unwrap();

        // Try to create again
        let txid2 = tc.tx_manager.begin();
        let result = tc.catalog.create_table(txid2, cid, &stmt).await;
        assert!(matches!(
            result,
            Err(CatalogError::TableAlreadyExists { .. })
        ));
        tc.tx_manager.abort(txid2).unwrap();
    }

    #[tokio::test]
    async fn test_create_table_if_not_exists() {
        let tc = create_test_catalog().await;
        let txid = tc.tx_manager.begin();
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

        let table_id = tc.catalog.create_table(txid, cid, &stmt).await.unwrap();
        assert!(table_id > 0);
        tc.tx_manager.commit(txid).unwrap();

        // Try to create again with IF NOT EXISTS
        let txid2 = tc.tx_manager.begin();
        let table_id2 = tc.catalog.create_table(txid2, cid, &stmt).await.unwrap();
        assert_eq!(table_id2, 0); // Returns 0 when table already exists
        tc.tx_manager.commit(txid2).unwrap();
    }
}
