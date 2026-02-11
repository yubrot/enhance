//! Catalog for table and column metadata management.
//!
//! This module provides pure metadata accessor without caching.
//! For cached access, use the `Catalog` wrapper in `cached.rs`.

use std::sync::Arc;

use parking_lot::RwLock;

use super::error::CatalogError;
use super::schema::{ColumnInfo, SequenceInfo, SystemCatalogTable, TableInfo};
use super::superblock::Superblock;
use crate::heap::{HeapPage, insert, scan_visible_page};
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
pub struct Catalog<S: Storage, R: Replacer> {
    /// Buffer pool for page access.
    pool: Arc<BufferPool<S, R>>,
    /// Transaction manager for MVCC.
    tx_manager: Arc<TransactionManager>,
    /// Superblock with catalog metadata (protected for updates).
    superblock: Arc<RwLock<Superblock>>,
}

// Manual Clone impl: all fields are Arc-based, so cloning is lightweight.
impl<S: Storage, R: Replacer> Clone for Catalog<S, R> {
    fn clone(&self) -> Self {
        Self {
            pool: Arc::clone(&self.pool),
            tx_manager: Arc::clone(&self.tx_manager),
            superblock: Arc::clone(&self.superblock),
        }
    }
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
            superblock: Arc::new(RwLock::new(superblock)),
        }
    }

    /// Bootstraps the catalog for a fresh database.
    ///
    /// This creates the initial catalog pages and inserts metadata
    /// for the catalog tables themselves.
    ///
    /// NOTE: Without WAL (Step 13), crash during bootstrap leaves the
    /// database in an inconsistent state that cannot be recovered.
    pub async fn bootstrap(
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
    ) -> Result<Self, CatalogError> {
        let mut sb_guard = pool.new_page().await?;
        // NOTE: Using assert_eq! here panics instead of returning an error.
        // Production code should return CatalogError::InvalidSuperblock or similar.
        assert_eq!(sb_guard.page_id(), PageId::new(0), "First page must be 0");

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

        superblock.write(sb_guard.data_mut());
        drop(sb_guard);

        // Bootstrap uses TxId::FROZEN so tuples are immediately visible without
        // requiring a transaction commit. This is safe because bootstrap runs
        // exclusively at database initialization time.
        let txid = TxId::FROZEN;
        let cid = CommandId::FIRST;

        // Insert catalog table metadata into sys_tables
        for table_info in [
            TableInfo::table_info(sys_tables_page),
            ColumnInfo::table_info(sys_columns_page),
            SequenceInfo::table_info(sys_sequences_page),
        ] {
            insert(&pool, sys_tables_page, &table_info.to_record(), txid, cid).await?;
        }

        // Insert column metadata into sys_columns
        for col in TableInfo::columns()
            .into_iter()
            .chain(ColumnInfo::columns())
            .chain(SequenceInfo::columns())
        {
            insert(&pool, sys_columns_page, &col.to_record(), txid, cid).await?;
        }

        pool.flush_all().await?;

        Ok(Self::new(pool, tx_manager, superblock))
    }

    /// Opens an existing catalog from storage.
    pub async fn open(
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
    pub fn superblock(&self) -> Superblock {
        *self.superblock.read()
    }

    /// Flushes the superblock to persistent storage with immediate fsync.
    ///
    /// The superblock is outside the WAL system (it contains WAL metadata itself),
    /// so we must ensure durability through immediate fsync.
    async fn flush_superblock(&self) -> Result<(), CatalogError> {
        let sb = self.superblock();
        let mut guard = self.pool.fetch_page_mut(PageId::new(0), true).await?;
        sb.write(guard.data_mut());
        drop(guard);

        // Flush and fsync the superblock page
        self.pool.flush_page(PageId::new(0)).await?;
        self.pool.storage().sync_all().await?;

        Ok(())
    }

    /// Looks up a table by name.
    ///
    /// Scans the full sys_tables page chain to find the table metadata.
    pub async fn get_table(
        &self,
        snapshot: &Snapshot,
        name: &str,
    ) -> Result<Option<TableInfo>, CatalogError> {
        let sys_tables_page = self.superblock.read().sys_tables_page;
        let mut current_page = Some(sys_tables_page);

        while let Some(page_id) = current_page {
            let (tuples, next_page) = scan_visible_page(
                &self.pool,
                page_id,
                TableInfo::SCHEMA,
                snapshot,
                &self.tx_manager,
            )
            .await?;
            current_page = next_page;

            for (_tid, record) in tuples {
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
        }

        Ok(None)
    }

    /// Gets columns for a table.
    ///
    /// Scans the full sys_columns page chain to find the column metadata.
    pub async fn get_columns(
        &self,
        snapshot: &Snapshot,
        table_id: u32,
    ) -> Result<Vec<ColumnInfo>, CatalogError> {
        let sys_columns_page = self.superblock.read().sys_columns_page;
        let mut current_page = Some(sys_columns_page);

        let mut columns = Vec::new();
        while let Some(page_id) = current_page {
            let (tuples, next_page) = scan_visible_page(
                &self.pool,
                page_id,
                ColumnInfo::SCHEMA,
                snapshot,
                &self.tx_manager,
            )
            .await?;
            current_page = next_page;

            for (_tid, record) in tuples {
                let Some(col) = ColumnInfo::from_record(&record) else {
                    // NOTE: Silently skipping corrupted records. See get_table() for details.
                    continue;
                };

                if col.table_id != table_id {
                    continue;
                }

                columns.push(col);
            }
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
        let sys_tables_page = self.superblock.read().sys_tables_page;
        insert(
            &self.pool,
            sys_tables_page,
            &TableInfo::new(table_id, name.to_string(), first_page).to_record(),
            txid,
            cid,
        )
        .await?;
        Ok(())
    }

    /// Inserts a column record into sys_columns.
    async fn insert_column(
        &self,
        txid: TxId,
        cid: CommandId,
        col: &ColumnInfo,
    ) -> Result<(), CatalogError> {
        let sys_columns_page = self.superblock.read().sys_columns_page;
        insert(&self.pool, sys_columns_page, &col.to_record(), txid, cid).await?;
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
    pub async fn create_table(
        &self,
        txid: TxId,
        cid: CommandId,
        stmt: &CreateTableStmt,
    ) -> Result<u32, CatalogError> {
        // Check if table already exists
        // NOTE: This check-then-insert pattern is not atomic without proper locking
        // or unique constraints.
        let snapshot = self.tx_manager.snapshot(txid, cid);
        if let Some(table) = self.get_table(&snapshot, &stmt.name).await? {
            if stmt.if_not_exists {
                return Ok(table.table_id);
            }
            return Err(CatalogError::TableAlreadyExists {
                name: stmt.name.clone(),
            });
        }

        // Allocate table ID and persist immediately to ensure uniqueness
        // even if the transaction aborts or crashes occur later.
        let table_id = self.superblock.write().allocate_table_id();
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
            let seq_id = match col_def.data_type {
                DataType::Serial => {
                    let seq_name = format!("{}_{}_seq", stmt.name, col_def.name);
                    self.create_sequence(txid, cid, &seq_name).await?
                }
                _ => 0,
            };

            columns.push(ColumnInfo::new(
                table_id,
                col_num as u32,
                col_def.name.clone(),
                col_def.data_type.to_type(),
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

    /// Creates a new sequence.
    async fn create_sequence(
        &self,
        txid: TxId,
        cid: CommandId,
        name: &str,
    ) -> Result<u32, CatalogError> {
        // Allocate sequence ID and persist immediately to ensure uniqueness
        let seq_id = self.superblock.write().allocate_seq_id();
        self.flush_superblock().await?;

        let seq = SequenceInfo::new(seq_id, name.to_string(), 1); // Start at 1

        let sys_sequences_page = self.superblock.read().sys_sequences_page;
        insert(&self.pool, sys_sequences_page, &seq.to_record(), txid, cid).await?;
        Ok(seq_id)
    }

    /// Gets the next value from a sequence.
    ///
    /// Sequences are NOT rolled back on transaction abort (following PostgreSQL's behavior).
    /// Each call increments the sequence permanently, independent of transaction state.
    pub async fn nextval(&self, seq_id: u32) -> Result<i64, CatalogError> {
        // The page latch is held during the entire operation to ensure atomicity.
        let sys_sequences_page = self.superblock.read().sys_sequences_page;
        let mut page = HeapPage::new(self.pool.fetch_page_mut(sys_sequences_page, true).await?);

        // Find the sequence
        let (slot_id, mut seq) = page
            .scan(SequenceInfo::SCHEMA)
            .find_map(|(slot_id, _header, record)| {
                let seq = SequenceInfo::from_record(&record)?;
                (seq.seq_id == seq_id).then_some((slot_id, seq))
            })
            .ok_or(CatalogError::SequenceNotFound { seq_id })?;

        let current_val = seq.next_val;
        seq.next_val += 1;

        // Update record in-place, bypassing MVCC
        // The record size is unchanged (same seq_name, only next_val differs)
        page.update_record_in_place(slot_id, &seq.to_record())?;

        Ok(current_val)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::catalog::LAST_RESERVED_TABLE_ID;
    use crate::catalog::schema::SystemCatalogTable;
    use crate::sql::{Parser, Statement};
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
    }

    #[tokio::test]
    async fn test_create_table() {
        let tc = create_test_catalog().await;
        let txid = tc.tx_manager.begin();
        let cid = CommandId::FIRST;

        let Ok(Some(Statement::CreateTable(stmt))) =
            Parser::new("CREATE TABLE users (id SERIAL, name TEXT)").parse()
        else {
            panic!("expected CreateTable");
        };

        let table_id = tc.catalog.create_table(txid, cid, &stmt).await.unwrap();
        assert_eq!(table_id, LAST_RESERVED_TABLE_ID + 1);

        tc.tx_manager.commit(txid).unwrap();

        // Verify table exists
        let txid2 = tc.tx_manager.begin();
        let snapshot = tc.tx_manager.snapshot(txid2, CommandId::FIRST);

        let Some(table) = tc.catalog.get_table(&snapshot, "users").await.unwrap() else {
            panic!("expected table exists");
        };
        assert_eq!(table.table_name, "users");
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
    }

    #[tokio::test]
    async fn test_create_table_already_exists() {
        let tc = create_test_catalog().await;
        let txid = tc.tx_manager.begin();
        let cid = CommandId::FIRST;

        let Ok(Some(Statement::CreateTable(stmt))) =
            Parser::new("CREATE TABLE test (id INTEGER)").parse()
        else {
            panic!("expected CreateTable");
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
    }

    #[tokio::test]
    async fn test_create_table_if_not_exists() {
        let tc = create_test_catalog().await;
        let txid = tc.tx_manager.begin();
        let cid = CommandId::FIRST;

        let Ok(Some(Statement::CreateTable(stmt))) =
            Parser::new("CREATE TABLE IF NOT EXISTS test (id INTEGER)").parse()
        else {
            panic!("expected CreateTable");
        };

        let table_id = tc.catalog.create_table(txid, cid, &stmt).await.unwrap();
        assert!(table_id > 0);
        tc.tx_manager.commit(txid).unwrap();

        // Try to create again with IF NOT EXISTS
        let txid2 = tc.tx_manager.begin();
        let table_id2 = tc.catalog.create_table(txid2, cid, &stmt).await.unwrap();
        assert_eq!(table_id2, table_id);
    }
}
