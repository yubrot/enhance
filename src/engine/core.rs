//! Engine orchestrator for buffer pool, transaction manager, and catalog.

use std::collections::VecDeque;
use std::sync::Arc;

use parking_lot::RwLock;

use super::error::EngineError;
use super::exec_context::ExecContextImpl;
use super::superblock::Superblock;
use crate::catalog::{Catalog, ColumnInfo, SequenceInfo, SystemCatalogTable, TableInfo};
use crate::heap::{HeapPage, insert, scan_visible_page};
use crate::sql::{CreateTableStmt, DataType};
use crate::storage::{BufferPool, LruReplacer, PageId, Replacer, Storage};
use crate::tx::{CommandId, Snapshot, TransactionManager, TxId, TxState};

/// Engine orchestrates the core components: BufferPool, TransactionManager, and catalog.
///
/// This is the main entry point for database operations. It initializes or opens
/// an existing database and provides access to its components.
pub struct Engine<S: Storage, R: Replacer> {
    pool: Arc<BufferPool<S, R>>,
    tx_manager: Arc<TransactionManager>,
    superblock: Arc<RwLock<Superblock>>,
    /// MVCC-aware catalog cache.
    ///
    /// A small queue of `(TxId, Option<Arc<Catalog>>)` entries ordered from oldest
    /// to newest. Each entry represents a DDL epoch. `TxId::FROZEN` serves as the
    /// universal fallback (always visible to every snapshot).
    catalog_cache: RwLock<VecDeque<(TxId, Option<Arc<Catalog>>)>>,
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
        let superblock = match pool.page_count().await {
            0 => Self::bootstrap(&pool).await?,
            _ => Self::open_superblock(&pool).await?,
        };

        Ok(Self {
            pool,
            tx_manager,
            superblock: Arc::new(RwLock::new(superblock)),
            catalog_cache: {
                let mut deque = VecDeque::with_capacity(2);
                deque.push_back((TxId::FROZEN, None));
                RwLock::new(deque)
            },
        })
    }

    /// Bootstraps the catalog for a fresh database.
    ///
    /// Creates the initial catalog pages and inserts metadata for the
    /// catalog tables themselves.
    ///
    /// NOTE: Without WAL (Step 13), crash during bootstrap leaves the
    /// database in an inconsistent state that cannot be recovered.
    async fn bootstrap(pool: &Arc<BufferPool<S, R>>) -> Result<Superblock, EngineError> {
        let mut sb_guard = pool.new_page().await?;
        // NOTE: Using assert_eq! here panics instead of returning an error.
        // Production code should return an appropriate error.
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
        superblock.next_table_id = crate::catalog::LAST_RESERVED_TABLE_ID + 1;
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
            insert(pool, sys_tables_page, &table_info.to_record(), txid, cid).await?;
        }

        // Insert column metadata into sys_columns
        for col in TableInfo::columns()
            .into_iter()
            .chain(ColumnInfo::columns())
            .chain(SequenceInfo::columns())
        {
            insert(pool, sys_columns_page, &col.to_record(), txid, cid).await?;
        }

        pool.flush_all().await?;

        Ok(superblock)
    }

    /// Opens an existing database by reading the superblock from page 0.
    async fn open_superblock(pool: &Arc<BufferPool<S, R>>) -> Result<Superblock, EngineError> {
        let guard = pool.fetch_page(PageId::new(0)).await?;
        let superblock = Superblock::read(guard.data());
        drop(guard);
        superblock.validate()?;
        Ok(superblock)
    }

    /// Returns a reference to the buffer pool.
    pub fn pool(&self) -> &Arc<BufferPool<S, R>> {
        &self.pool
    }

    /// Returns a reference to the transaction manager.
    pub fn tx_manager(&self) -> &Arc<TransactionManager> {
        &self.tx_manager
    }

    /// Returns a cached [`Catalog`] for the given MVCC snapshot.
    ///
    /// Avoids redundant heap scans when no DDL has been committed since the
    /// last load. Self-DDL snapshots bypass the cache entirely to see their
    /// own uncommitted schema changes.
    pub async fn catalog_snapshot(&self, snapshot: &Snapshot) -> Result<Arc<Catalog>, EngineError> {
        // Phase 1: Write lock — find the visible entry (with aborted cleanup).
        {
            let mut cache = self.catalog_cache.write();
            if let Some(Some(catalog)) = find_visible_entry(&mut cache, snapshot, &self.tx_manager)
            {
                return Ok(Arc::clone(catalog));
            }
        }

        // Phase 2: No lock — load from heap.
        // NOTE: Two threads may concurrently miss the cache and both perform a
        // heap load. This is harmless: Phase 3 re-checks and only one result
        // populates the slot; the other is used directly and discarded.
        let loaded = Arc::new(
            Self::load_catalog_static(
                Arc::clone(&self.pool),
                Arc::clone(&self.tx_manager),
                Arc::clone(&self.superblock),
                snapshot.clone(),
            )
            .await?,
        );

        // Phase 3: Write lock — re-find and populate if still empty.
        {
            let mut cache = self.catalog_cache.write();
            if let Some(slot @ None) = find_visible_entry(&mut cache, snapshot, &self.tx_manager) {
                *slot = Some(Arc::clone(&loaded));
            }
        }

        Ok(loaded)
    }

    /// Creates an [`ExecContextImpl`] for query execution with the given snapshot.
    pub fn exec_context(&self, snapshot: Snapshot) -> ExecContextImpl<S, R> {
        ExecContextImpl::new(
            Arc::clone(&self.pool),
            Arc::clone(&self.tx_manager),
            Arc::clone(&self.superblock),
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

    /// Registers an in-progress DDL transaction in the catalog cache.
    ///
    /// Called after DDL succeeds but **before** commit, so that concurrent
    /// readers can detect the pending schema change.
    pub(crate) fn register_ddl(&self, txid: TxId) {
        let mut cache = self.catalog_cache.write();

        deny_concurrent_ddl(&mut cache, &self.tx_manager);
        clean_up_latest_aborted_entry(&mut cache, &self.tx_manager);

        cache.push_back((txid, None));

        // Keep at most 2 entries: one committed fallback + the new DDL entry.
        while cache.len() > 2 {
            cache.pop_front();
        }
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
        if let Some(table) = self.get_table(&snapshot, &stmt.name).await? {
            if stmt.if_not_exists {
                return Ok(table.table_id);
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

        Ok(table_id)
    }

    /// Gets the next value from a sequence.
    ///
    /// Sequences are NOT rolled back on transaction abort (following PostgreSQL's behavior).
    /// Each call increments the sequence permanently, independent of transaction state.
    pub async fn nextval(&self, seq_id: u32) -> Result<i64, EngineError> {
        super::exec_context::nextval_impl(&self.pool, &self.superblock, seq_id).await
    }

    /// Loads all visible catalog data into a new [`Catalog`].
    ///
    /// Scans sys_tables and sys_columns page chains, then calls [`Catalog::new`]
    /// to build the in-memory view.
    #[cfg(test)]
    pub(crate) async fn load_catalog(&self, snapshot: &Snapshot) -> Result<Catalog, EngineError> {
        Self::load_catalog_static(
            Arc::clone(&self.pool),
            Arc::clone(&self.tx_manager),
            Arc::clone(&self.superblock),
            snapshot.clone(),
        )
        .await
    }

    /// Static version of `load_catalog` that takes owned Arcs.
    ///
    /// Used by `catalog_snapshot` to create a `'static` loader future for the
    /// catalog cache.
    async fn load_catalog_static(
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
        superblock: Arc<RwLock<Superblock>>,
        snapshot: Snapshot,
    ) -> Result<Catalog, EngineError> {
        let mut tables = Vec::new();
        let mut next_page_id: Option<PageId> = Some(superblock.read().sys_tables_page);
        while let Some(page_id) = next_page_id {
            let (tuples, next) =
                scan_visible_page(&pool, page_id, TableInfo::SCHEMA, &snapshot, &tx_manager)
                    .await?;
            let page_tables: Vec<TableInfo> = tuples
                .into_iter()
                .filter_map(|(_tid, record)| TableInfo::from_record(&record))
                .collect();
            tables.extend(page_tables);
            next_page_id = next;
        }

        let mut columns = Vec::new();
        let mut next_page_id: Option<PageId> = Some(superblock.read().sys_columns_page);
        while let Some(page_id) = next_page_id {
            let (tuples, next) =
                scan_visible_page(&pool, page_id, ColumnInfo::SCHEMA, &snapshot, &tx_manager)
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

    /// Looks up a table by name.
    ///
    /// Iterates the sys_tables page chain and returns the first match.
    async fn get_table(
        &self,
        snapshot: &Snapshot,
        name: &str,
    ) -> Result<Option<TableInfo>, EngineError> {
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
            let tables: Vec<TableInfo> = tuples
                .into_iter()
                .filter_map(|(_tid, record)| TableInfo::from_record(&record))
                .collect();
            for info in tables {
                if info.table_name == name {
                    return Ok(Some(info));
                }
            }
            next_page_id = next;
        }
        Ok(None)
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

/// Panics if the most recent DDL entry is still in progress, enforcing
/// the serial DDL assumption.
///
/// NOTE: This panic will be replaced by a DDL lock in a future step,
/// which prevents concurrent DDL at a higher level.
fn deny_concurrent_ddl(
    entries: &mut VecDeque<(TxId, Option<Arc<Catalog>>)>,
    tx_manager: &TransactionManager,
) {
    if let Some(&(txid, _)) = entries.back()
        && tx_manager.state(txid) == TxState::InProgress
    {
        panic!(
            "Concurrent DDL: cannot register DDL while {} is still in progress",
            txid
        );
    }
}

/// Clean up the tail entry if it was aborted. Only the tail is removed
/// here; non-tail aborted entries are skipped during the scan below and
/// naturally evicted by register_ddl's size limit.
fn clean_up_latest_aborted_entry(
    entries: &mut VecDeque<(TxId, Option<Arc<Catalog>>)>,
    tx_manager: &TransactionManager,
) {
    if entries.len() > 1
        && let Some(&(txid, _)) = entries.back()
        && tx_manager.state(txid) == TxState::Aborted
    {
        entries.pop_back();
    }
}

/// Finds the most recent cache entry visible to the given MVCC snapshot.
///
/// Returns `Some(slot)` for the best visible committed entry (which may
/// or may not contain a cached catalog), or `None` for self-DDL and
/// stale-read scenarios where the cache must be bypassed.
fn find_visible_entry<'a>(
    entries: &'a mut VecDeque<(TxId, Option<Arc<Catalog>>)>,
    snapshot: &Snapshot,
    tx_manager: &TransactionManager,
) -> Option<&'a mut Option<Arc<Catalog>>> {
    clean_up_latest_aborted_entry(entries, tx_manager);

    for (txid, slot) in entries.iter_mut().rev() {
        // Self-DDL: must bypass cache (uncommitted schema change).
        if *txid == snapshot.current_txid {
            return None;
        }
        // Accept only committed DDLs visible to this snapshot.
        // Aborted and in-progress entries are skipped.
        if snapshot.is_txid_visible(*txid) && tx_manager.state(*txid) == TxState::Committed {
            return Some(slot);
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::catalog::{LAST_RESERVED_TABLE_ID, SequenceInfo, SystemCatalogTable};
    use crate::sql::tests::parse_create_table;
    use crate::storage::MemoryStorage;
    use crate::storage::tests::test_pool;

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
    async fn test_bootstrap_creates_catalog() {
        let pool = test_pool();

        let sb = Engine::bootstrap(&pool).await.unwrap();

        assert!(sb.validate().is_ok());
        assert_eq!(sb.sys_tables_page, PageId::new(1));
        assert_eq!(sb.sys_columns_page, PageId::new(2));
        assert_eq!(sb.sys_sequences_page, PageId::new(3));
        assert_eq!(sb.next_table_id, LAST_RESERVED_TABLE_ID + 1);
    }

    #[tokio::test]
    async fn test_get_table() {
        let engine = Engine::open(MemoryStorage::new(), 100).await.unwrap();
        let txid = engine.tx_manager().begin();
        let snapshot = engine.tx_manager().snapshot(txid, CommandId::FIRST);

        // Should find sys_tables
        let table = engine.get_table(&snapshot, "sys_tables").await.unwrap();
        assert!(table.is_some());
        let table = table.unwrap();
        assert_eq!(table.table_id, TableInfo::TABLE_ID);
        assert_eq!(table.table_name, "sys_tables");

        // Should find sys_columns
        let table = engine.get_table(&snapshot, "sys_columns").await.unwrap();
        assert!(table.is_some());

        // Should not find non-existent table
        let table = engine.get_table(&snapshot, "nonexistent").await.unwrap();
        assert!(table.is_none());
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

        let Some(table) = engine.get_table(&snapshot, "users").await.unwrap() else {
            panic!("expected table exists");
        };
        assert_eq!(table.table_name, "users");
        assert_eq!(table.table_id, LAST_RESERVED_TABLE_ID + 1);
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
    async fn test_open_reads_superblock() {
        let pool = test_pool();

        // Bootstrap first
        let sb = Engine::bootstrap(&pool).await.unwrap();

        // Open superblock from the same pool
        let sb2 = Engine::open_superblock(&pool).await.unwrap();

        assert_eq!(sb2.sys_tables_page, sb.sys_tables_page);
        assert_eq!(sb2.sys_columns_page, sb.sys_columns_page);
        assert_eq!(sb2.sys_sequences_page, sb.sys_sequences_page);
        assert_eq!(sb2.next_table_id, sb.next_table_id);
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

        let Some(table) = engine.get_table(&snapshot, "users").await.unwrap() else {
            panic!("expected 'users' table to exist after commit");
        };
        assert_eq!(table.table_name, "users");
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

    // --- Catalog cache tests (moved from catalog/cache.rs) ---

    #[tokio::test]
    async fn test_catalog_cache_hit() {
        let engine = Engine::open(MemoryStorage::new(), 100).await.unwrap();
        let txid = engine.tx_manager().begin();
        let snapshot = engine.tx_manager().snapshot(txid, CommandId::FIRST);

        // First call: cache miss, loads from heap.
        let snap1 = engine.catalog_snapshot(&snapshot).await.unwrap();
        assert!(snap1.resolve_table("sys_tables").is_some());

        // Second call: cache hit, returns same Arc.
        let snap2 = engine.catalog_snapshot(&snapshot).await.unwrap();
        assert!(Arc::ptr_eq(&snap1, &snap2));
    }

    #[tokio::test]
    async fn test_catalog_cache_ddl_invalidation() {
        let engine = Engine::open(MemoryStorage::new(), 100).await.unwrap();

        // Populate cache.
        let tx1 = engine.tx_manager().begin();
        let snap1 = engine.tx_manager().snapshot(tx1, CommandId::FIRST);
        let initial = engine.catalog_snapshot(&snap1).await.unwrap();
        assert!(initial.resolve_table("test_tbl").is_none());
        let _ = engine.tx_manager().abort(tx1);

        // DDL: create table.
        let ddl_txid = engine.tx_manager().begin();
        let cid = CommandId::FIRST;
        let stmt = parse_create_table("CREATE TABLE test_tbl (id INTEGER)");
        engine.create_table(ddl_txid, cid, &stmt).await.unwrap();

        // Register DDL before commit.
        engine.register_ddl(ddl_txid);
        engine.tx_manager().commit(ddl_txid).unwrap();

        // New snapshot should see the DDL.
        let tx2 = engine.tx_manager().begin();
        let snap2 = engine.tx_manager().snapshot(tx2, CommandId::FIRST);
        let refreshed = engine.catalog_snapshot(&snap2).await.unwrap();

        // Should NOT be the same Arc (cache was invalidated).
        assert!(!Arc::ptr_eq(&initial, &refreshed));
        assert!(refreshed.resolve_table("test_tbl").is_some());
    }

    #[tokio::test]
    async fn test_catalog_cache_ddl_abort() {
        let engine = Engine::open(MemoryStorage::new(), 100).await.unwrap();

        // Populate cache.
        let tx1 = engine.tx_manager().begin();
        let snap1 = engine.tx_manager().snapshot(tx1, CommandId::FIRST);
        let cached = engine.catalog_snapshot(&snap1).await.unwrap();
        let _ = engine.tx_manager().abort(tx1);

        // DDL that gets aborted.
        let ddl_txid = engine.tx_manager().begin();
        let cid = CommandId::FIRST;
        let stmt = parse_create_table("CREATE TABLE vanish (id INTEGER)");
        engine.create_table(ddl_txid, cid, &stmt).await.unwrap();
        engine.register_ddl(ddl_txid);
        let _ = engine.tx_manager().abort(ddl_txid);

        // After abort, the aborted entry is cleaned up and the original
        // cached catalog is returned (no redundant heap scan).
        let tx2 = engine.tx_manager().begin();
        let snap2 = engine.tx_manager().snapshot(tx2, CommandId::FIRST);
        let after = engine.catalog_snapshot(&snap2).await.unwrap();
        assert!(Arc::ptr_eq(&cached, &after));
        assert!(after.resolve_table("vanish").is_none());
    }

    #[tokio::test]
    async fn test_catalog_cache_self_ddl_bypass() {
        let engine = Engine::open(MemoryStorage::new(), 100).await.unwrap();

        // Populate cache.
        let tx0 = engine.tx_manager().begin();
        let snap0 = engine.tx_manager().snapshot(tx0, CommandId::FIRST);
        let _ = engine.catalog_snapshot(&snap0).await.unwrap();
        let _ = engine.tx_manager().abort(tx0);

        // Start a DDL transaction.
        let ddl_txid = engine.tx_manager().begin();
        let cid = CommandId::FIRST;
        let stmt = parse_create_table("CREATE TABLE self_tbl (id INTEGER)");
        engine.create_table(ddl_txid, cid, &stmt).await.unwrap();
        engine.register_ddl(ddl_txid);

        // Self-DDL: the same txid should get a fresh load,
        // NOT the shared cache.
        let self_snapshot = engine.tx_manager().snapshot(ddl_txid, cid.next());
        let self_catalog = engine.catalog_snapshot(&self_snapshot).await.unwrap();
        // The self-DDL result should see the uncommitted table.
        assert!(self_catalog.resolve_table("self_tbl").is_some());

        // But the shared cache should NOT have been updated.
        let tx2 = engine.tx_manager().begin();
        let snap2 = engine.tx_manager().snapshot(tx2, CommandId::FIRST);
        let shared = engine.catalog_snapshot(&snap2).await.unwrap();
        // Other transactions can't see the uncommitted DDL.
        assert!(shared.resolve_table("self_tbl").is_none());
    }
}
