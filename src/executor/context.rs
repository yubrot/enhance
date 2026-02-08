//! Execution context for executor nodes.
//!
//! The [`ExecContext`] trait abstracts storage operations needed by executor
//! nodes, keeping them decoupled from concrete `Storage`/`Replacer` types.

use std::future::Future;
use std::sync::Arc;

use crate::catalog::Catalog;
use crate::datum::Type;
use crate::heap::{HeapPage, Record, TupleId, heap_insert};
use crate::storage::{BufferPool, PageId, Replacer, Storage};
use crate::tx::{Snapshot, TransactionManager};

use super::error::ExecutorError;
use super::row::Row;

/// Execution context providing storage operations to executor nodes.
///
/// Implementations are `Clone` so each node can own its own copy.
/// Methods take `&self` because all mutable state (scan position, buffer) is
/// managed by the nodes themselves.
pub trait ExecContext: Send + Clone {
    /// Scans a single heap page and returns all visible tuples.
    ///
    /// Also returns the next page ID in the chain (if any) so that the
    /// caller can continue scanning multi-page tables.
    ///
    /// Visibility is determined by the snapshot embedded in the context.
    /// The caller provides the column schema for record deserialization.
    ///
    /// NOTE: Page chain traversal is currently pushed to the caller (SeqScan).
    /// A future refactor could wrap this as `scan_table` that uses HeapScanner
    /// internally, keeping chain logic in the context layer.
    fn scan_heap_page(
        &self,
        page_id: PageId,
        schema: &[Type],
    ) -> impl Future<Output = Result<(Vec<Row>, Option<PageId>), ExecutorError>> + Send;

    /// Inserts a tuple into the heap table starting at `first_page`.
    ///
    /// Walks the page chain to find free space; allocates new pages when full.
    /// Sets xmin to the current transaction, cid to the current command.
    fn insert_tuple(
        &self,
        first_page: PageId,
        record: &Record,
    ) -> impl Future<Output = Result<TupleId, ExecutorError>> + Send;

    /// Deletes a tuple by setting its xmax to the current transaction.
    ///
    /// The tuple remains physically on the page but becomes invisible to
    /// subsequent snapshots.
    fn delete_tuple(
        &self,
        tid: TupleId,
    ) -> impl Future<Output = Result<(), ExecutorError>> + Send;

    /// Updates a tuple (delete old version + insert new version).
    ///
    /// Attempts same-page insertion first to avoid unnecessary page chain
    /// traversal. Falls back to `insert_tuple` on the table's first page
    /// if the same page is full.
    fn update_tuple(
        &self,
        first_page: PageId,
        old_tid: TupleId,
        new_record: &Record,
    ) -> impl Future<Output = Result<TupleId, ExecutorError>> + Send;

    /// Gets the next value from a sequence.
    ///
    /// Sequences are NOT rolled back on transaction abort (following PostgreSQL behavior).
    fn nextval(&self, seq_id: u32) -> impl Future<Output = Result<i64, ExecutorError>> + Send;
}

/// Concrete [`ExecContext`] backed by a [`BufferPool`], [`TransactionManager`], and [`Catalog`].
///
/// Owns `Arc` references to shared components plus a cloned [`Snapshot`]
/// for visibility checks. Cloning is lightweight.
pub struct ExecContextImpl<S: Storage, R: Replacer> {
    pool: Arc<BufferPool<S, R>>,
    tx_manager: Arc<TransactionManager>,
    catalog: Catalog<S, R>,
    snapshot: Snapshot,
}

// Manual Clone impl to avoid requiring S: Clone + R: Clone
// (only Arc, Catalog, and Snapshot are cloned).
impl<S: Storage, R: Replacer> Clone for ExecContextImpl<S, R> {
    fn clone(&self) -> Self {
        Self {
            pool: Arc::clone(&self.pool),
            tx_manager: Arc::clone(&self.tx_manager),
            catalog: self.catalog.clone(),
            snapshot: self.snapshot.clone(),
        }
    }
}

impl<S: Storage, R: Replacer> ExecContextImpl<S, R> {
    /// Creates a new execution context.
    pub fn new(
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
        catalog: Catalog<S, R>,
        snapshot: Snapshot,
    ) -> Self {
        Self {
            pool,
            tx_manager,
            catalog,
            snapshot,
        }
    }
}

impl<S: Storage, R: Replacer> ExecContext for ExecContextImpl<S, R> {
    // NOTE: All visible tuples from the page are loaded into a Vec<Row>
    // so that the page latch is released before returning to the caller. This
    // minimizes latch hold time but means memory usage is proportional to tuples
    // per page. For production, consider streaming with explicit latch management,
    // especially once Sort/Aggregate (Step 12) may need to scan large tables.
    async fn scan_heap_page(
        &self,
        page_id: PageId,
        schema: &[Type],
    ) -> Result<(Vec<Row>, Option<PageId>), ExecutorError> {
        let page = HeapPage::new(self.pool.fetch_page(page_id).await?);
        let next_page = page.next_page();

        let mut tuples = Vec::new();
        for (slot_id, header, record) in page.scan(schema) {
            if !self.snapshot.is_tuple_visible(&header, &self.tx_manager) {
                continue;
            }
            let tid = TupleId { page_id, slot_id };
            tuples.push(Row::from_heap(tid, record));
        }

        Ok((tuples, next_page))
    }

    async fn insert_tuple(
        &self,
        first_page: PageId,
        record: &Record,
    ) -> Result<TupleId, ExecutorError> {
        let tid = heap_insert(
            &self.pool,
            first_page,
            record,
            self.snapshot.current_txid,
            self.snapshot.current_cid,
        )
        .await?;
        Ok(tid)
    }

    async fn delete_tuple(&self, tid: TupleId) -> Result<(), ExecutorError> {
        let mut page = HeapPage::new(self.pool.fetch_page_mut(tid.page_id, true).await?);
        let mut header = page
            .get_header(tid.slot_id)
            .ok_or(crate::heap::HeapError::SlotNotFound(tid.slot_id))?;
        // NOTE: No xmax conflict check here. If another transaction has already set
        // xmax, we overwrite it. Row-level locking (Step 20) will add proper
        // write-write conflict detection via wait-for graph.
        header.xmax = self.snapshot.current_txid;
        header.cmax = self.snapshot.current_cid;
        page.update_header(tid.slot_id, header)?;
        Ok(())
    }

    // NOTE: update_tuple is not atomic — if delete succeeds but insert fails
    // (e.g., storage I/O error), the old version has xmax set with no new version.
    // The transaction should be aborted in this case, which makes xmax invisible.
    // WAL (Step 13) will provide proper rollback guarantees.
    async fn update_tuple(
        &self,
        first_page: PageId,
        old_tid: TupleId,
        new_record: &Record,
    ) -> Result<TupleId, ExecutorError> {
        // Delete the old version
        self.delete_tuple(old_tid).await?;

        // Try same-page insert first
        {
            let mut page = HeapPage::new(self.pool.fetch_page_mut(old_tid.page_id, true).await?);
            match page.insert(
                new_record,
                self.snapshot.current_txid,
                self.snapshot.current_cid,
            ) {
                Ok(slot_id) => {
                    return Ok(TupleId {
                        page_id: old_tid.page_id,
                        slot_id,
                    });
                }
                Err(crate::heap::HeapError::PageFull { .. }) => {
                    // Fall through to table-wide insert
                }
                Err(other) => return Err(other.into()),
            }
        }

        // Same page is full; insert via page chain
        let tid = self.insert_tuple(first_page, new_record).await?;
        Ok(tid)
    }

    async fn nextval(&self, seq_id: u32) -> Result<i64, ExecutorError> {
        let val = self.catalog.nextval(seq_id).await?;
        Ok(val)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::catalog::{SystemCatalogTable, TableInfo};
    use crate::datum::Value;
    use crate::db::Database;
    use crate::storage::MemoryStorage;
    use crate::tx::CommandId;

    #[tokio::test]
    async fn test_exec_context_impl_scan_catalog() {
        // Bootstrap a database to get catalog tables with data
        let storage = MemoryStorage::new();
        let db = Database::open(storage, 100).await.unwrap();

        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);

        // Scan the first page of sys_tables (page 2 after superblock and catalog pages)
        // We don't know the exact page ID, so we rely on the catalog to tell us.
        // For this test, we just verify the context is functional by scanning page 2
        // (which is the sys_tables heap page in a freshly bootstrapped database).
        let table_info = db
            .catalog()
            .get_table(&snapshot, "sys_tables")
            .await
            .unwrap()
            .unwrap();

        let ctx = db.exec_context(snapshot);

        let (tuples, next_page) = ctx
            .scan_heap_page(table_info.first_page, &TableInfo::SCHEMA)
            .await
            .unwrap();

        // Single-page catalog: no next page
        assert_eq!(next_page, None);

        // Should find at least 3 catalog tables (sys_tables, sys_columns, sys_sequences)
        assert!(
            tuples.len() >= 3,
            "expected at least 3 catalog tables, got {}",
            tuples.len()
        );

        // Verify first tuple is sys_tables itself
        assert_eq!(tuples[0].record.values[1], Value::Text("sys_tables".into()));
        // All tuples should have TupleId set
        for tuple in &tuples {
            assert!(tuple.tid.is_some());
        }
    }

    #[tokio::test]
    async fn test_insert_tuple_and_scan() {
        let storage = MemoryStorage::new();
        let db = Database::open(storage, 100).await.unwrap();

        // Create a test table
        let txid = db.tx_manager().begin();
        let stmt = crate::sql::Parser::new("CREATE TABLE test (id INTEGER, name TEXT)")
            .parse()
            .unwrap()
            .into_iter()
            .next()
            .unwrap();
        let crate::sql::Statement::CreateTable(create_stmt) = stmt else {
            panic!("expected CreateTable");
        };
        db.catalog()
            .create_table(txid, CommandId::FIRST, &create_stmt)
            .await
            .unwrap();
        db.tx_manager().commit(txid).unwrap();

        // Insert a tuple (CID 0)
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        let table = db.catalog().get_table(&snapshot, "test").await.unwrap().unwrap();
        let ctx = db.exec_context(snapshot);

        let record = Record::new(vec![Value::Integer(42), Value::Text("hello".into())]);
        let tid = ctx.insert_tuple(table.first_page, &record).await.unwrap();
        assert_eq!(tid.page_id, table.first_page);

        // Same-CID scan: tuple inserted at CID 0 is NOT visible to CID 0
        // (MVCC rule: cmin < current_cid required, but 0 < 0 is false)
        let schema = [Type::Integer, Type::Text];
        let (tuples, _) = ctx.scan_heap_page(table.first_page, &schema).await.unwrap();
        assert_eq!(tuples.len(), 0, "same-CID insert should not be visible");

        // Next command's snapshot (CID 1): tuple IS visible (cmin 0 < current_cid 1)
        let snapshot2 = db.tx_manager().snapshot(txid, CommandId::new(1));
        let ctx2 = db.exec_context(snapshot2);
        let schema = [Type::Integer, Type::Text];
        let (tuples, _) = ctx2.scan_heap_page(table.first_page, &schema).await.unwrap();
        assert_eq!(tuples.len(), 1);
        assert_eq!(tuples[0].record.values[0], Value::Integer(42));
        assert_eq!(tuples[0].record.values[1], Value::Text("hello".into()));
        db.tx_manager().commit(txid).unwrap();
    }

    #[tokio::test]
    async fn test_delete_tuple() {
        let storage = MemoryStorage::new();
        let db = Database::open(storage, 100).await.unwrap();

        // Create table
        let txid = db.tx_manager().begin();
        let stmt = crate::sql::Parser::new("CREATE TABLE test (id INTEGER)")
            .parse()
            .unwrap()
            .into_iter()
            .next()
            .unwrap();
        let crate::sql::Statement::CreateTable(create_stmt) = stmt else {
            panic!("expected CreateTable");
        };
        db.catalog()
            .create_table(txid, CommandId::FIRST, &create_stmt)
            .await
            .unwrap();
        db.tx_manager().commit(txid).unwrap();

        // Insert a tuple (CID 0)
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        let table = db.catalog().get_table(&snapshot, "test").await.unwrap().unwrap();
        let ctx = db.exec_context(snapshot);
        let record = Record::new(vec![Value::Integer(1)]);
        let tid = ctx.insert_tuple(table.first_page, &record).await.unwrap();

        // Delete the tuple (still CID 0 — same command can delete what it inserted)
        ctx.delete_tuple(tid).await.unwrap();

        // After delete, a new snapshot at the next CID should not see it
        let snapshot2 = db.tx_manager().snapshot(txid, CommandId::new(1));
        let ctx2 = db.exec_context(snapshot2);
        let (tuples, _) = ctx2
            .scan_heap_page(table.first_page, &[Type::Integer])
            .await
            .unwrap();
        assert_eq!(tuples.len(), 0, "deleted tuple should not be visible");
        db.tx_manager().commit(txid).unwrap();
    }

    #[tokio::test]
    async fn test_update_tuple() {
        let storage = MemoryStorage::new();
        let db = Database::open(storage, 100).await.unwrap();

        // Create table
        let txid = db.tx_manager().begin();
        let stmt = crate::sql::Parser::new("CREATE TABLE test (id INTEGER, val TEXT)")
            .parse()
            .unwrap()
            .into_iter()
            .next()
            .unwrap();
        let crate::sql::Statement::CreateTable(create_stmt) = stmt else {
            panic!("expected CreateTable");
        };
        db.catalog()
            .create_table(txid, CommandId::FIRST, &create_stmt)
            .await
            .unwrap();
        db.tx_manager().commit(txid).unwrap();

        // Insert a tuple (CID 0)
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        let table = db.catalog().get_table(&snapshot, "test").await.unwrap().unwrap();
        let ctx = db.exec_context(snapshot);
        let record = Record::new(vec![Value::Integer(1), Value::Text("old".into())]);
        let tid = ctx.insert_tuple(table.first_page, &record).await.unwrap();

        // Update the tuple (new CID so we see the old version)
        let snapshot2 = db.tx_manager().snapshot(txid, CommandId::new(1));
        let ctx2 = db.exec_context(snapshot2.clone());
        let new_record = Record::new(vec![Value::Integer(1), Value::Text("new".into())]);
        let new_tid = ctx2
            .update_tuple(table.first_page, tid, &new_record)
            .await
            .unwrap();

        // The new tuple should be on the same page (same-page priority)
        assert_eq!(new_tid.page_id, tid.page_id);

        // With a new snapshot, only the new version should be visible
        let snapshot3 = db.tx_manager().snapshot(txid, CommandId::new(2));
        let ctx3 = db.exec_context(snapshot3);
        let schema = [Type::Integer, Type::Text];
        let (tuples, _) = ctx3
            .scan_heap_page(table.first_page, &schema)
            .await
            .unwrap();
        assert_eq!(tuples.len(), 1);
        assert_eq!(tuples[0].record.values[1], Value::Text("new".into()));
        db.tx_manager().commit(txid).unwrap();
    }

    #[tokio::test]
    async fn test_nextval() {
        let storage = MemoryStorage::new();
        let db = Database::open(storage, 100).await.unwrap();

        // Create a table with a SERIAL column to generate a sequence
        let txid = db.tx_manager().begin();
        let stmt = crate::sql::Parser::new("CREATE TABLE test (id SERIAL, name TEXT)")
            .parse()
            .unwrap()
            .into_iter()
            .next()
            .unwrap();
        let crate::sql::Statement::CreateTable(create_stmt) = stmt else {
            panic!("expected CreateTable");
        };
        db.catalog()
            .create_table(txid, CommandId::FIRST, &create_stmt)
            .await
            .unwrap();
        db.tx_manager().commit(txid).unwrap();

        // Find the sequence ID for the SERIAL column
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        let table = db.catalog().get_table(&snapshot, "test").await.unwrap().unwrap();
        let columns = db.catalog().get_columns(&snapshot, table.table_id).await.unwrap();
        let serial_col = columns.iter().find(|c| c.column_name == "id").unwrap();
        let seq_id = serial_col.seq_id;
        assert!(seq_id > 0, "SERIAL column should have a sequence");

        let ctx = db.exec_context(snapshot);

        // nextval should return incrementing values
        let v1 = ctx.nextval(seq_id).await.unwrap();
        let v2 = ctx.nextval(seq_id).await.unwrap();
        let v3 = ctx.nextval(seq_id).await.unwrap();
        assert_eq!(v1, 1);
        assert_eq!(v2, 2);
        assert_eq!(v3, 3);
        db.tx_manager().commit(txid).unwrap();
    }
}
