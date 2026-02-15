//! Engine orchestrator for managing buffer pool, transaction manager, and catalog.
//!
//! The [`Engine`] type is the main entry point for database infrastructure.
//! It initializes or opens an existing database and provides access to
//! the core components (buffer pool, transaction manager, catalog operations).
//!
//! # Architecture
//!
//! ```text
//! +------------------------------------------------------------------+
//! |                          Engine                                  |
//! |  (Orchestrates core infrastructure components)                   |
//! |                                                                  |
//! |  +-----------------+  +--------------------+  +---------------+  |
//! |  | Arc<BufferPool> |  | Arc<TxManager>     |  | Superblock    |  |
//! |  | (Page I/O,      |  | (TxId allocation,  |  | (Table/column |  |
//! |  |  LRU eviction)  |  |  commit/abort)     |  |  page IDs)    |  |
//! |  +--------+--------+  +--------------------+  +-------+-------+  |
//! |           |                                           |          |
//! +-----------+-------------------------------------------+----------+
//!             |                                           |
//!             v                                           | uses
//!       +---------------------+                           |
//!       |  storage::Storage   |<--------------------------+
//!       | (Memory / File)     |
//!       +---------------------+
//! ```

mod error;
mod execution_point;
mod superblock;

pub use error::EngineError;
pub use execution_point::ExecutionPoint;
pub use superblock::Superblock;

use std::sync::Arc;

use parking_lot::RwLock;

use crate::catalog::{Catalog, CatalogVC, ColumnInfo, SequenceInfo, SystemCatalogTable, TableInfo};
use crate::executor::ExecutorError;
use crate::heap::{HeapPage, insert, scan_visible_page};
use crate::sql::{CreateTableStmt, DataType};
use crate::storage::{BufferPool, LruReplacer, PageId, Replacer, Storage};
use crate::tx::{CommandId, Snapshot, TransactionManager, TxId};

/// Engine orchestrates the core components: BufferPool, TransactionManager, and catalog.
///
/// This is the main entry point for database operations. It initializes or opens
/// an existing database and provides access to its components.
pub struct Engine<S: Storage, R: Replacer> {
    pool: BufferPool<S, R>,
    tx_manager: TransactionManager,
    superblock: RwLock<Superblock>,
    catalog_vc: CatalogVC,
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
        let pool = BufferPool::new(storage, replacer, pool_size);
        let tx_manager = TransactionManager::new();
        let superblock = Superblock::boot(&pool).await?;

        Ok(Self {
            pool,
            tx_manager,
            superblock: RwLock::new(superblock),
            catalog_vc: CatalogVC::new(),
        })
    }

    /// Returns a reference to the buffer pool.
    pub fn pool(&self) -> &BufferPool<S, R> {
        &self.pool
    }

    /// Returns a reference to the transaction manager.
    pub fn tx_manager(&self) -> &TransactionManager {
        &self.tx_manager
    }

    /// Creates an [`ExecutionPoint`] for query execution with the given snapshot.
    ///
    /// Requires `&Arc<Self>` so the execution point can hold a lightweight
    /// `Arc` clone of the engine instead of cloning each component separately.
    pub fn execution_point(self: &Arc<Self>, snapshot: Snapshot) -> ExecutionPoint<S, R> {
        ExecutionPoint::new(Arc::clone(self), snapshot)
    }

    /// Returns the superblock.
    pub(crate) fn superblock(&self) -> Superblock {
        *self.superblock.read()
    }

    /// Flushes the superblock to persistent storage with immediate fsync.
    ///
    /// The superblock is outside the WAL system (it contains WAL metadata itself),
    /// so we must ensure durability through immediate fsync.
    async fn flush_superblock(&self) -> Result<(), EngineError> {
        let sb = self.superblock();
        let mut guard = self.pool.fetch_page_mut(PageId::new(0), true).await?;
        sb.write(guard.data_mut());
        drop(guard);

        // Flush and fsync the superblock page
        self.pool.flush_page(PageId::new(0)).await?;
        self.pool.storage().sync_all().await?;

        Ok(())
    }

    /// Returns a cached [`Catalog`] for the given MVCC snapshot.
    ///
    /// Avoids redundant heap scans when no DDL has been committed since the
    /// last load. Self-DDL snapshots bypass the cache entirely to see their
    /// own uncommitted schema changes.
    pub async fn catalog(&self, snapshot: &Snapshot) -> Result<Arc<Catalog>, EngineError> {
        if let Some(catalog) = self.catalog_vc.get(snapshot, &self.tx_manager) {
            return Ok(catalog);
        }

        // Cache miss — load from heap.
        // NOTE: Two threads may concurrently miss the cache and both perform a
        // heap load. This is harmless: try_populate re-checks and only one
        // result populates the slot; the other is used directly and discarded.
        let loaded = Arc::new(self.load_catalog(snapshot).await?);
        self.catalog_vc
            .try_populate(snapshot, &self.tx_manager, Arc::clone(&loaded));

        Ok(loaded)
    }

    /// Gets the next value from a sequence.
    ///
    /// Sequences are NOT rolled back on transaction abort (following PostgreSQL's behavior).
    /// Each call increments the sequence permanently, independent of transaction state.
    pub async fn nextval(&self, seq_id: u32) -> Result<i64, ExecutorError> {
        // The page latch is held during the entire operation to ensure atomicity.
        let sys_sequences_page = self.superblock.read().sys_sequences_page;
        let mut page = HeapPage::new(
            self.pool
                .fetch_page_mut(sys_sequences_page, true)
                .await
                .map_err(|e| ExecutorError::Heap(e.into()))?,
        );

        // Find the sequence
        let (slot_id, mut seq) = page
            .scan(SequenceInfo::SCHEMA)
            .find_map(|(slot_id, _header, record)| {
                let seq = SequenceInfo::from_record(&record)?;
                (seq.seq_id == seq_id).then_some((slot_id, seq))
            })
            .ok_or(ExecutorError::SequenceNotFound { seq_id })?;

        let current_val = seq.next_val;
        seq.next_val += 1;

        // Update record in-place, bypassing MVCC
        // The record size is unchanged (same seq_name, only next_val differs)
        page.update_record_in_place(slot_id, &seq.to_record())?;

        Ok(current_val)
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
    /// Returns `EngineError::TableAlreadyExists` if the table exists.
    pub async fn create_table(
        &self,
        txid: TxId,
        cid: CommandId,
        stmt: &CreateTableStmt,
    ) -> Result<u32, EngineError> {
        // Check if table already exists
        // NOTE: This check-then-insert pattern is not atomic without proper locking
        // or unique constraints.
        let snapshot = self.tx_manager.snapshot(txid, cid);
        let catalog = self.catalog(&snapshot).await?;
        if let Some(entry) = catalog.resolve_table(&stmt.name) {
            if stmt.if_not_exists {
                return Ok(entry.info.table_id);
            }
            return Err(EngineError::TableAlreadyExists {
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

        self.catalog_vc.register_ddl(txid, &self.tx_manager);
        Ok(table_id)
    }

    /// Loads all visible catalog data into a new [`Catalog`].
    async fn load_catalog(&self, snapshot: &Snapshot) -> Result<Catalog, EngineError> {
        let mut tables = Vec::new();
        let mut next_page_id: Option<PageId> = Some(self.superblock.read().sys_tables_page);
        while let Some(page_id) = next_page_id {
            let (tuples, next) = scan_visible_page(
                &self.pool,
                page_id,
                TableInfo::SCHEMA,
                snapshot,
                &self.tx_manager,
            )
            .await?;
            let page_tables: Vec<TableInfo> = tuples
                .into_iter()
                .filter_map(|(_tid, record)| TableInfo::from_record(&record))
                .collect();
            tables.extend(page_tables);
            next_page_id = next;
        }

        let mut columns = Vec::new();
        let mut next_page_id: Option<PageId> = Some(self.superblock.read().sys_columns_page);
        while let Some(page_id) = next_page_id {
            let (tuples, next) = scan_visible_page(
                &self.pool,
                page_id,
                ColumnInfo::SCHEMA,
                snapshot,
                &self.tx_manager,
            )
            .await?;
            let page_columns: Vec<ColumnInfo> = tuples
                .into_iter()
                .filter_map(|(_tid, record)| ColumnInfo::from_record(&record))
                .collect();
            columns.extend(page_columns);
            next_page_id = next;
        }

        Ok(Catalog::new(tables, columns))
    }

    /// Inserts a table record into sys_tables.
    async fn insert_table(
        &self,
        txid: TxId,
        cid: CommandId,
        table_id: u32,
        name: &str,
        first_page: PageId,
    ) -> Result<(), EngineError> {
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
    ) -> Result<(), EngineError> {
        let sys_columns_page = self.superblock.read().sys_columns_page;
        insert(&self.pool, sys_columns_page, &col.to_record(), txid, cid).await?;
        Ok(())
    }

    /// Creates a new sequence.
    async fn create_sequence(
        &self,
        txid: TxId,
        cid: CommandId,
        name: &str,
    ) -> Result<u32, EngineError> {
        // Allocate sequence ID and persist immediately to ensure uniqueness
        let seq_id = self.superblock.write().allocate_seq_id();
        self.flush_superblock().await?;

        let seq = SequenceInfo::new(seq_id, name.to_string(), 1); // Start at 1

        let sys_sequences_page = self.superblock.read().sys_sequences_page;
        insert(&self.pool, sys_sequences_page, &seq.to_record(), txid, cid).await?;
        Ok(seq_id)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::catalog::{LAST_RESERVED_TABLE_ID, SequenceInfo, SystemCatalogTable};
    use crate::sql::tests::parse_create_table;
    use crate::storage::MemoryStorage;

    /// Type alias for a test engine backed by in-memory storage.
    pub type TestEngine = Engine<MemoryStorage, LruReplacer>;

    /// Opens a test engine with in-memory storage and 100-frame buffer pool.
    pub async fn open_test_engine() -> Arc<TestEngine> {
        Arc::new(Engine::open(MemoryStorage::new(), 100).await.unwrap())
    }

    impl TestEngine {
        /// Creates a table using the given DDL and commits it in its own transaction.
        ///
        /// Parses the DDL string as a `CREATE TABLE` statement, executes it within
        /// a new transaction, and commits immediately.
        pub async fn create_test_table(&self, ddl: &str) {
            let txid = self.tx_manager().begin();
            let stmt = parse_create_table(ddl);
            self.create_table(txid, CommandId::FIRST, &stmt)
                .await
                .unwrap();
            self.tx_manager().commit(txid).unwrap();
        }
    }

    #[tokio::test]
    async fn test_engine_open() {
        let storage = Arc::new(MemoryStorage::new());
        // First open: should bootstrap a new database
        {
            let engine = Engine::open(Arc::clone(&storage), 100).await.unwrap();

            // Verify catalog is initialized
            let sb = engine.superblock();
            assert_eq!(sb.next_table_id, LAST_RESERVED_TABLE_ID + 1);
            assert!(engine.pool().page_count().await > 0);
        };

        // Second open: should open existing database (not bootstrap)
        {
            let engine = Engine::open(storage, 100).await.unwrap();

            // Verify catalog was opened (not re-bootstrapped)
            let sb = engine.superblock();
            assert_eq!(sb.next_table_id, LAST_RESERVED_TABLE_ID + 1);
        }
    }

    #[tokio::test]
    async fn test_catalog_resolve_table() {
        let engine = Engine::open(MemoryStorage::new(), 100).await.unwrap();
        let txid = engine.tx_manager().begin();
        let snapshot = engine.tx_manager().snapshot(txid, CommandId::FIRST);
        let catalog = engine.catalog(&snapshot).await.unwrap();

        // Should find sys_tables
        let entry = catalog.resolve_table("sys_tables").unwrap();
        assert_eq!(entry.info.table_id, TableInfo::TABLE_ID);
        assert_eq!(entry.info.table_name, "sys_tables");

        // Should find sys_columns
        assert!(catalog.resolve_table("sys_columns").is_some());

        // Should not find non-existent table
        assert!(catalog.resolve_table("nonexistent").is_none());
    }

    #[tokio::test]
    async fn test_create_table() {
        let engine = Engine::open(MemoryStorage::new(), 100).await.unwrap();
        let txid = engine.tx_manager().begin();
        let cid = CommandId::FIRST;

        let stmt = parse_create_table("CREATE TABLE users (id SERIAL, name TEXT)");

        let table_id = engine.create_table(txid, cid, &stmt).await.unwrap();
        assert_eq!(table_id, LAST_RESERVED_TABLE_ID + 1);

        engine.tx_manager().commit(txid).unwrap();

        // Verify table exists
        let txid2 = engine.tx_manager().begin();
        let snapshot = engine.tx_manager().snapshot(txid2, CommandId::FIRST);
        let catalog = engine.catalog(&snapshot).await.unwrap();

        let Some(entry) = catalog.resolve_table("users") else {
            panic!("expected table exists");
        };
        assert_eq!(entry.info.table_name, "users");
        assert_eq!(entry.info.table_id, LAST_RESERVED_TABLE_ID + 1);
    }

    #[tokio::test]
    async fn test_create_table_already_exists() {
        let engine = Engine::open(MemoryStorage::new(), 100).await.unwrap();
        let txid = engine.tx_manager().begin();
        let cid = CommandId::FIRST;

        let stmt = parse_create_table("CREATE TABLE test (id INTEGER)");

        engine.create_table(txid, cid, &stmt).await.unwrap();
        engine.tx_manager().commit(txid).unwrap();

        // Try to create again
        let txid2 = engine.tx_manager().begin();
        let result = engine.create_table(txid2, cid, &stmt).await;
        assert!(matches!(
            result,
            Err(EngineError::TableAlreadyExists { .. })
        ));
    }

    #[tokio::test]
    async fn test_create_table_if_not_exists() {
        let engine = Engine::open(MemoryStorage::new(), 100).await.unwrap();
        let txid = engine.tx_manager().begin();
        let cid = CommandId::FIRST;

        let stmt = parse_create_table("CREATE TABLE IF NOT EXISTS test (id INTEGER)");

        let table_id = engine.create_table(txid, cid, &stmt).await.unwrap();
        assert!(table_id > 0);
        engine.tx_manager().commit(txid).unwrap();

        // Try to create again with IF NOT EXISTS
        let txid2 = engine.tx_manager().begin();
        let table_id2 = engine.create_table(txid2, cid, &stmt).await.unwrap();
        assert_eq!(table_id2, table_id);
    }

    #[tokio::test]
    async fn test_committed_table_is_queryable() {
        let engine = Engine::open(MemoryStorage::new(), 100).await.unwrap();

        // Create a user table and commit
        let txid = engine.tx_manager().begin();
        let cid = CommandId::FIRST;
        let stmt = parse_create_table("CREATE TABLE users (id INTEGER, name TEXT)");
        engine.create_table(txid, cid, &stmt).await.unwrap();
        engine.tx_manager().commit(txid).unwrap();

        // Verify the table is visible in a new transaction
        let txid2 = engine.tx_manager().begin();
        let snapshot = engine.tx_manager().snapshot(txid2, CommandId::FIRST);
        let catalog = engine.catalog(&snapshot).await.unwrap();

        let Some(entry) = catalog.resolve_table("users") else {
            panic!("expected 'users' table to exist after commit");
        };
        assert_eq!(entry.info.table_name, "users");
    }

    // --- Integration tests for load_catalog (moved from catalog/snapshot.rs) ---

    #[tokio::test]
    async fn test_load_system_tables() {
        let engine = Engine::open(MemoryStorage::new(), 100).await.unwrap();
        let txid = engine.tx_manager().begin();
        let snapshot = engine.tx_manager().snapshot(txid, CommandId::FIRST);

        let catalog = engine.load_catalog(&snapshot).await.unwrap();

        // Should contain the 3 system catalog tables
        assert_eq!(
            catalog.resolve_table("sys_tables").unwrap().info.table_id,
            TableInfo::TABLE_ID
        );
        assert_eq!(
            catalog.resolve_table("sys_columns").unwrap().info.table_id,
            ColumnInfo::TABLE_ID
        );
        assert_eq!(
            catalog
                .resolve_table("sys_sequences")
                .unwrap()
                .info
                .table_id,
            SequenceInfo::TABLE_ID
        );

        // sys_tables should have 3 columns
        let entry = catalog.resolve_table_by_id(TableInfo::TABLE_ID).unwrap();
        assert_eq!(entry.columns.len(), 3);
        assert_eq!(entry.columns[0].column_name, "table_id");
        assert_eq!(entry.columns[1].column_name, "table_name");
        assert_eq!(entry.columns[2].column_name, "first_page");
    }

    #[tokio::test]
    async fn test_load_with_user_table() {
        let engine = Engine::open(MemoryStorage::new(), 100).await.unwrap();
        let txid = engine.tx_manager().begin();
        let cid = CommandId::FIRST;

        let stmt = parse_create_table("CREATE TABLE users (id SERIAL, name TEXT)");

        engine.create_table(txid, cid, &stmt).await.unwrap();
        engine.tx_manager().commit(txid).unwrap();

        // Load catalog with a new transaction
        let txid2 = engine.tx_manager().begin();
        let snapshot = engine.tx_manager().snapshot(txid2, CommandId::FIRST);
        let catalog = engine.load_catalog(&snapshot).await.unwrap();

        let entry = catalog.resolve_table("users").unwrap();
        assert_eq!(entry.info.table_id, LAST_RESERVED_TABLE_ID + 1);
        assert_eq!(entry.columns.len(), 2);
        assert_eq!(entry.columns[0].column_name, "id");
        assert!(entry.columns[0].is_serial());
        assert_eq!(entry.columns[1].column_name, "name");
        assert!(!entry.columns[1].is_serial());
    }

    #[tokio::test]
    async fn test_load_uncommitted_not_visible() {
        let engine = Engine::open(MemoryStorage::new(), 100).await.unwrap();
        let txid = engine.tx_manager().begin();
        let cid = CommandId::FIRST;

        let stmt = parse_create_table("CREATE TABLE invisible (id INTEGER)");

        engine.create_table(txid, cid, &stmt).await.unwrap();
        // Do NOT commit

        // Another transaction should not see the uncommitted table
        let txid2 = engine.tx_manager().begin();
        let snapshot = engine.tx_manager().snapshot(txid2, CommandId::FIRST);
        let catalog = engine.load_catalog(&snapshot).await.unwrap();

        assert!(catalog.resolve_table("invisible").is_none());
    }
}
