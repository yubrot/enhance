//! Multi-page heap write operations (insert, delete, update).
//!
//! These functions operate on a heap page chain identified by its first page,
//! handling page traversal and allocation automatically.
//!
//! Implemented as free functions rather than a struct because each operation is
//! stateless — no cursor position or buffered data needs to be maintained.

use crate::storage::{BufferPool, PageId, Replacer, Storage};
use crate::tx::{CommandId, TxId};

use super::TupleId;
use super::error::HeapError;
use super::page::HeapPage;
use super::record::Record;

/// Inserts a tuple into a heap table, extending the page chain if needed.
///
/// Walks pages starting from `first_page`, attempting to insert the record.
/// If all existing pages are full, allocates a new page at the end of the chain.
///
/// Returns the [`TupleId`] of the inserted tuple.
pub async fn insert<S: Storage, R: Replacer>(
    pool: &BufferPool<S, R>,
    first_page: PageId,
    record: &Record,
    txid: TxId,
    cid: CommandId,
) -> Result<TupleId, HeapError> {
    // Walk the page chain looking for a page with free space
    let mut current_page_id = first_page;
    loop {
        let guard = pool.fetch_page_mut(current_page_id, true).await?;
        let mut heap_page = HeapPage::new(guard);

        // Try to insert into this page
        match heap_page.insert(record, txid, cid) {
            Ok(slot_id) => {
                return Ok(TupleId {
                    page_id: current_page_id,
                    slot_id,
                });
            }
            Err(HeapError::PageFull { .. }) => {
                // Check if there's a next page to try
                match heap_page.next_page() {
                    Some(next_id) => {
                        // Drop the guard before fetching the next page
                        drop(heap_page);
                        current_page_id = next_id;
                        continue;
                    }
                    None => {
                        // Allocate a new page and link it.
                        // Latch ordering is safe: new_page() allocates a higher
                        // page ID, so we hold latches in ascending order.
                        let new_guard = pool.new_page().await?;
                        let new_page_id = new_guard.page_id();
                        HeapPage::new(new_guard).init();

                        // Link the current (last) page to the new page
                        heap_page.set_next_page(Some(new_page_id));
                        drop(heap_page);

                        // Insert into the new page
                        let new_guard = pool.fetch_page_mut(new_page_id, true).await?;
                        let mut new_heap_page = HeapPage::new(new_guard);
                        let slot_id = new_heap_page.insert(record, txid, cid)?;

                        return Ok(TupleId {
                            page_id: new_page_id,
                            slot_id,
                        });
                    }
                }
            }
            Err(other) => return Err(other),
        }
    }
}

/// Deletes a tuple by setting its xmax/cmax (MVCC soft delete).
///
/// The tuple remains physically on the page but becomes invisible to
/// subsequent snapshots once the deleting transaction commits.
///
/// NOTE: No xmax conflict check here. If another transaction has already set
/// xmax, we overwrite it. Row-level locking (Step 20) will add proper
/// write-write conflict detection via wait-for graph.
pub async fn delete<S: Storage, R: Replacer>(
    pool: &BufferPool<S, R>,
    tid: TupleId,
    txid: TxId,
    cid: CommandId,
) -> Result<(), HeapError> {
    let mut page = HeapPage::new(pool.fetch_page_mut(tid.page_id, true).await?);
    let mut header = page
        .get_header(tid.slot_id)
        .ok_or(HeapError::SlotNotFound(tid.slot_id))?;
    header.xmax = txid;
    header.cmax = cid;
    page.update_header(tid.slot_id, header)?;
    Ok(())
}

/// Updates a tuple (delete old version + insert new version).
///
/// Attempts same-page insertion first to avoid unnecessary page chain
/// traversal. Falls back to [`insert`] on the table's first page if the
/// same page is full.
///
/// Returns the [`TupleId`] of the newly inserted version.
///
/// NOTE: This operation is not atomic — if delete succeeds but insert fails
/// (e.g., storage I/O error), the old version has xmax set with no new version.
/// The transaction should be aborted in this case, which makes xmax invisible.
/// WAL (Step 13) will provide proper rollback guarantees.
pub async fn update<S: Storage, R: Replacer>(
    pool: &BufferPool<S, R>,
    first_page: PageId,
    old_tid: TupleId,
    new_record: &Record,
    txid: TxId,
    cid: CommandId,
) -> Result<TupleId, HeapError> {
    // Delete the old version and try same-page insert in a single fetch
    {
        let mut page = HeapPage::new(pool.fetch_page_mut(old_tid.page_id, true).await?);

        // Set xmax on the old tuple
        let mut header = page
            .get_header(old_tid.slot_id)
            .ok_or(HeapError::SlotNotFound(old_tid.slot_id))?;
        header.xmax = txid;
        header.cmax = cid;
        page.update_header(old_tid.slot_id, header)?;

        // Try to insert the new version on the same page
        match page.insert(new_record, txid, cid) {
            Ok(slot_id) => {
                return Ok(TupleId {
                    page_id: old_tid.page_id,
                    slot_id,
                });
            }
            Err(HeapError::PageFull { .. }) => {
                // Fall through — release the latch and use page-chain insert
            }
            Err(other) => return Err(other),
        }
    }

    // Same page is full; insert via page chain
    insert(pool, first_page, new_record, txid, cid).await
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::datum::{Type, Value};
    use crate::heap::scan_visible_page;
    use crate::storage::{BufferPool, LruReplacer, MemoryStorage};
    use crate::tx::TransactionManager;
    use std::sync::Arc;

    async fn create_pool() -> Arc<BufferPool<MemoryStorage, LruReplacer>> {
        Arc::new(BufferPool::new(
            MemoryStorage::new(),
            LruReplacer::new(100),
            100,
        ))
    }

    async fn create_heap_table(pool: &BufferPool<MemoryStorage, LruReplacer>) -> PageId {
        let guard = pool.new_page().await.unwrap();
        let page_id = guard.page_id();
        HeapPage::new(guard).init();
        page_id
    }

    /// Collects all visible tuples from a heap page chain using scan_visible_page.
    async fn collect_all_visible(
        pool: &BufferPool<MemoryStorage, LruReplacer>,
        first_page: PageId,
        schema: &[Type],
        snapshot: &crate::tx::Snapshot,
        tx_manager: &TransactionManager,
    ) -> Vec<(super::TupleId, Record)> {
        let mut all = Vec::new();
        let mut current_page = Some(first_page);
        while let Some(page_id) = current_page {
            let (tuples, next_page) =
                scan_visible_page(pool, page_id, schema, snapshot, tx_manager)
                    .await
                    .unwrap();
            all.extend(tuples);
            current_page = next_page;
        }
        all
    }

    #[tokio::test]
    async fn test_insert_cid_visibility() {
        let pool = create_pool().await;
        let tx_manager = TransactionManager::new();
        let first_page = create_heap_table(&pool).await;
        let schema = [Type::Integer, Type::Text];

        let txid = tx_manager.begin();

        // Insert a tuple at CID 0
        let record = Record::new(vec![Value::Integer(42), Value::Text("hello".into())]);
        let tid = insert(&pool, first_page, &record, txid, CommandId::FIRST)
            .await
            .unwrap();
        assert_eq!(tid.page_id, first_page);

        // Same-CID scan: tuple inserted at CID 0 is NOT visible to CID 0
        // (MVCC rule: cmin < current_cid required, but 0 < 0 is false)
        let snapshot0 = tx_manager.snapshot(txid, CommandId::FIRST);
        let tuples = collect_all_visible(&pool, first_page, &schema, &snapshot0, &tx_manager).await;
        assert_eq!(tuples.len(), 0, "same-CID insert should not be visible");

        // Next command's snapshot (CID 1): tuple IS visible (cmin 0 < current_cid 1)
        let snapshot1 = tx_manager.snapshot(txid, CommandId::new(1));
        let tuples = collect_all_visible(&pool, first_page, &schema, &snapshot1, &tx_manager).await;
        assert_eq!(tuples.len(), 1);
        assert_eq!(tuples[0].1.values[0], Value::Integer(42));
        assert_eq!(tuples[0].1.values[1], Value::Text("hello".into()));
    }

    #[tokio::test]
    async fn test_delete_cid_visibility() {
        let pool = create_pool().await;
        let tx_manager = TransactionManager::new();
        let first_page = create_heap_table(&pool).await;
        let schema = [Type::Integer];

        let txid = tx_manager.begin();

        // Insert and delete at CID 0 (same command can delete what it inserted)
        let record = Record::new(vec![Value::Integer(1)]);
        let tid = insert(&pool, first_page, &record, txid, CommandId::FIRST)
            .await
            .unwrap();
        delete(&pool, tid, txid, CommandId::FIRST).await.unwrap();

        // After delete, CID 1 snapshot should not see the tuple
        let snapshot1 = tx_manager.snapshot(txid, CommandId::new(1));
        let tuples = collect_all_visible(&pool, first_page, &schema, &snapshot1, &tx_manager).await;
        assert_eq!(tuples.len(), 0, "deleted tuple should not be visible");
    }

    #[tokio::test]
    async fn test_update_cid_visibility() {
        let pool = create_pool().await;
        let tx_manager = TransactionManager::new();
        let first_page = create_heap_table(&pool).await;
        let schema = [Type::Integer, Type::Text];

        let txid = tx_manager.begin();

        // Insert a tuple at CID 0
        let record = Record::new(vec![Value::Integer(1), Value::Text("old".into())]);
        let old_tid = insert(&pool, first_page, &record, txid, CommandId::FIRST)
            .await
            .unwrap();

        // Update at CID 1 (CID 1 scan sees old version, so update is possible)
        let new_record = Record::new(vec![Value::Integer(1), Value::Text("new".into())]);
        let new_tid = update(
            &pool,
            first_page,
            old_tid,
            &new_record,
            txid,
            CommandId::new(1),
        )
        .await
        .unwrap();

        // New version should be on the same page (same-page priority)
        assert_eq!(new_tid.page_id, old_tid.page_id);

        // CID 2 snapshot: only the new version should be visible
        let snapshot2 = tx_manager.snapshot(txid, CommandId::new(2));
        let tuples = collect_all_visible(&pool, first_page, &schema, &snapshot2, &tx_manager).await;
        assert_eq!(tuples.len(), 1);
        assert_eq!(tuples[0].1.values[1], Value::Text("new".into()));
    }

    #[tokio::test]
    async fn test_insert_into_empty_page() {
        let pool = create_pool().await;
        let tx_manager = TransactionManager::new();
        let first_page = create_heap_table(&pool).await;

        let record = Record::new(vec![Value::Integer(42)]);
        let tid = insert(&pool, first_page, &record, TxId::FROZEN, CommandId::FIRST)
            .await
            .unwrap();

        assert_eq!(tid.page_id, first_page);
        assert_eq!(tid.slot_id, 0);

        // Verify the record is readable
        let txid = tx_manager.begin();
        let snapshot = tx_manager.snapshot(txid, CommandId::FIRST);
        let schema = [Type::Integer];
        let tuples = collect_all_visible(&pool, first_page, &schema, &snapshot, &tx_manager).await;
        assert_eq!(tuples.len(), 1);
        assert_eq!(tuples[0].1.values, vec![Value::Integer(42)]);
    }

    #[tokio::test]
    async fn test_insert_triggers_new_page_allocation() {
        let pool = create_pool().await;
        let tx_manager = TransactionManager::new();
        let first_page = create_heap_table(&pool).await;

        let txid = TxId::FROZEN;
        let cid = CommandId::FIRST;

        // Insert records until the first page is full and a new page is allocated
        // Use a large record to fill pages quickly
        let large_text = "x".repeat(2000);
        let mut tids = Vec::new();
        for i in 0..10 {
            let record = Record::new(vec![Value::Integer(i), Value::Text(large_text.clone())]);
            let tid = insert(&pool, first_page, &record, txid, cid).await.unwrap();
            tids.push(tid);
        }

        // Verify that at least one tuple ended up on a different page
        let has_second_page = tids.iter().any(|t| t.page_id != first_page);
        assert!(
            has_second_page,
            "expected at least one insert to trigger a new page allocation"
        );

        // Verify all records are readable via scan
        let tx = tx_manager.begin();
        let snapshot = tx_manager.snapshot(tx, CommandId::FIRST);
        let schema = [Type::Integer, Type::Text];
        let tuples = collect_all_visible(&pool, first_page, &schema, &snapshot, &tx_manager).await;
        assert_eq!(tuples.len(), 10);
        for (i, tuple) in tuples.iter().enumerate() {
            assert_eq!(tuple.1.values[0], Value::Integer(i as i32));
        }
    }

    #[tokio::test]
    async fn test_page_chain_integrity() {
        let pool = create_pool().await;
        let first_page = create_heap_table(&pool).await;

        let txid = TxId::FROZEN;
        let cid = CommandId::FIRST;

        // Fill enough records to span 3+ pages
        let large_text = "y".repeat(3000);
        for i in 0..10 {
            let record = Record::new(vec![Value::Integer(i), Value::Text(large_text.clone())]);
            insert(&pool, first_page, &record, txid, cid).await.unwrap();
        }

        // Walk the page chain manually and verify linkage
        let mut page_count = 0;
        let mut current = Some(first_page);
        while let Some(pid) = current {
            page_count += 1;
            let guard = pool.fetch_page(pid).await.unwrap();
            let page = HeapPage::new(guard);
            current = page.next_page();
        }

        assert!(
            page_count >= 2,
            "expected at least 2 pages in chain, got {}",
            page_count
        );
    }

    #[tokio::test]
    async fn test_insert_fills_existing_pages_before_allocating() {
        let pool = create_pool().await;
        let first_page = create_heap_table(&pool).await;

        let txid = TxId::FROZEN;
        let cid = CommandId::FIRST;

        // Fill the first page
        let large_text = "z".repeat(2000);
        let mut last_on_first = None;
        for i in 0..20 {
            let record = Record::new(vec![Value::Integer(i), Value::Text(large_text.clone())]);
            let tid = insert(&pool, first_page, &record, txid, cid).await.unwrap();
            if tid.page_id == first_page {
                last_on_first = Some(i);
            }
        }

        // The first few inserts should have gone to the first page
        assert!(
            last_on_first.is_some(),
            "at least one insert should go to the first page"
        );
    }

    #[tokio::test]
    async fn test_delete_marks_tuple_invisible() {
        let pool = create_pool().await;
        let tx_manager = TransactionManager::new();
        let first_page = create_heap_table(&pool).await;

        let txid = TxId::FROZEN;
        let cid = CommandId::FIRST;
        let schema = [Type::Integer];

        // Insert two tuples
        let record1 = Record::new(vec![Value::Integer(1)]);
        let record2 = Record::new(vec![Value::Integer(2)]);
        let tid1 = insert(&pool, first_page, &record1, txid, cid)
            .await
            .unwrap();
        insert(&pool, first_page, &record2, txid, cid)
            .await
            .unwrap();

        // Delete the first tuple using a real transaction
        let del_txid = tx_manager.begin();
        let del_cid = CommandId::FIRST;
        delete(&pool, tid1, del_txid, del_cid).await.unwrap();
        tx_manager.commit(del_txid).unwrap();

        // A new snapshot should see only the second tuple
        let scan_txid = tx_manager.begin();
        let snapshot = tx_manager.snapshot(scan_txid, CommandId::FIRST);
        let tuples = collect_all_visible(&pool, first_page, &schema, &snapshot, &tx_manager).await;
        assert_eq!(tuples.len(), 1);
        assert_eq!(tuples[0].1.values[0], Value::Integer(2));
    }

    #[tokio::test]
    async fn test_delete_nonexistent_slot() {
        let pool = create_pool().await;
        let first_page = create_heap_table(&pool).await;

        let tid = TupleId {
            page_id: first_page,
            slot_id: 99,
        };
        let result = delete(&pool, tid, TxId::FROZEN, CommandId::FIRST).await;
        assert!(
            matches!(result, Err(HeapError::SlotNotFound(99))),
            "expected SlotNotFound, got {:?}",
            result
        );
    }

    #[tokio::test]
    async fn test_update_same_page() {
        let pool = create_pool().await;
        let tx_manager = TransactionManager::new();
        let first_page = create_heap_table(&pool).await;

        let txid = TxId::FROZEN;
        let cid = CommandId::FIRST;
        let schema = [Type::Integer, Type::Text];

        // Insert a tuple
        let record = Record::new(vec![Value::Integer(1), Value::Text("old".into())]);
        let old_tid = insert(&pool, first_page, &record, txid, cid).await.unwrap();

        // Update using a real transaction
        let upd_txid = tx_manager.begin();
        let upd_cid = CommandId::FIRST;
        let new_record = Record::new(vec![Value::Integer(1), Value::Text("new".into())]);
        let new_tid = update(&pool, first_page, old_tid, &new_record, upd_txid, upd_cid)
            .await
            .unwrap();

        // New version should be on the same page
        assert_eq!(new_tid.page_id, old_tid.page_id);

        tx_manager.commit(upd_txid).unwrap();

        // A new snapshot should see only the new version
        let scan_txid = tx_manager.begin();
        let snapshot = tx_manager.snapshot(scan_txid, CommandId::FIRST);
        let tuples = collect_all_visible(&pool, first_page, &schema, &snapshot, &tx_manager).await;
        assert_eq!(tuples.len(), 1);
        assert_eq!(tuples[0].1.values[1], Value::Text("new".into()));
    }

    #[tokio::test]
    async fn test_update_cross_page_fallback() {
        let pool = create_pool().await;
        let tx_manager = TransactionManager::new();
        let first_page = create_heap_table(&pool).await;

        let txid = TxId::FROZEN;
        let cid = CommandId::FIRST;

        // Insert a small tuple first
        let record = Record::new(vec![Value::Integer(1), Value::Text("small".into())]);
        let old_tid = insert(&pool, first_page, &record, txid, cid).await.unwrap();

        // Fill the page with large tuples so there's no room for the updated version
        let large_text = "x".repeat(2000);
        for i in 2..20 {
            let record = Record::new(vec![Value::Integer(i), Value::Text(large_text.clone())]);
            insert(&pool, first_page, &record, txid, cid).await.unwrap();
        }

        // Update the first tuple with a large value — should fall back to another page
        let upd_txid = tx_manager.begin();
        let upd_cid = CommandId::FIRST;
        let new_record = Record::new(vec![Value::Integer(1), Value::Text(large_text.clone())]);
        let new_tid = update(&pool, first_page, old_tid, &new_record, upd_txid, upd_cid)
            .await
            .unwrap();

        // New version should be on a different page (cross-page fallback)
        assert_ne!(
            new_tid.page_id, old_tid.page_id,
            "expected cross-page fallback, but new tuple is on the same page"
        );

        tx_manager.commit(upd_txid).unwrap();

        // Scan should see all tuples: the updated one + the filler tuples
        let scan_txid = tx_manager.begin();
        let snapshot = tx_manager.snapshot(scan_txid, CommandId::FIRST);
        let schema = [Type::Integer, Type::Text];
        let tuples = collect_all_visible(&pool, first_page, &schema, &snapshot, &tx_manager).await;

        // The old version (id=1, "small") should be gone; new version (id=1, large) should be present
        let updated = tuples
            .iter()
            .find(|(_, r)| r.values[0] == Value::Integer(1));
        assert!(updated.is_some(), "updated tuple should be visible");
        assert_eq!(updated.unwrap().1.values[1], Value::Text(large_text));
    }
}
