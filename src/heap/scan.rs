//! MVCC-aware single-page heap scan.
//!
//! [`scan_visible_page`] fetches a single heap page, filters tuples by
//! snapshot visibility, and returns `(TupleId, Record)` pairs along with
//! the next page in the chain.

use crate::datum::Type;
use crate::storage::{BufferPool, PageId, Replacer, Storage};
use crate::tx::{Infomask, Snapshot, TransactionManager};

use super::TupleId;
use super::error::HeapError;
use super::page::{HeapPage, SlotId};
use super::record::Record;

/// Scans a single heap page and returns all MVCC-visible tuples.
///
/// Uses a two-pass approach for lazy hint bit propagation:
/// 1. **Read pass**: Acquires a read latch, scans tuples, computes visibility,
///    and collects pending hint bit updates for tuples whose transaction state
///    has been resolved (committed or aborted) but not yet recorded in infomask.
/// 2. **Write-back pass**: If any hint bit updates are pending, acquires a write
///    latch and applies them. Hint bits are merged via bitwise OR (safe because
///    hint bits are monotonic — once set, never cleared).
///
/// When all hint bits are already set (2nd+ scan of a page), the write-back
/// pass is skipped entirely, avoiding write latch acquisition.
///
/// Also returns the next page ID in the chain (if any) so that the caller
/// can continue scanning multi-page tables via a while-let loop.
///
/// NOTE: Memory usage is proportional to the number of visible tuples per
/// page. For production, consider streaming with explicit latch management,
/// especially once Sort/Aggregate may need to scan large tables.
pub async fn scan_visible_page<S: Storage, R: Replacer>(
    pool: &BufferPool<S, R>,
    page_id: PageId,
    schema: &[Type],
    snapshot: &Snapshot,
    tx_manager: &TransactionManager,
) -> Result<(Vec<(TupleId, Record)>, Option<PageId>), HeapError> {
    // Phase 1: Read pass — scan page with read latch, collect visible tuples
    // and pending hint bit updates
    let (tuples, next_page, hint_updates) = {
        let guard = pool.fetch_page(page_id).await?;
        let heap_page = HeapPage::new(guard);
        let next_page = heap_page.next_page();

        let mut tuples = Vec::new();
        let mut hint_updates: Vec<(SlotId, Infomask)> = Vec::new();

        for (slot_id, header, record) in heap_page.scan(schema) {
            let vis = snapshot.check_visibility(&header, tx_manager);

            if vis.hint_bits != Infomask::empty() {
                hint_updates.push((slot_id, vis.hint_bits));
            }

            if vis.visible {
                let tid = TupleId { page_id, slot_id };
                tuples.push((tid, record));
            }
        }

        (tuples, next_page, hint_updates)
    }; // Read latch released here

    // Phase 2: Write-back pass — apply pending hint bit updates
    if !hint_updates.is_empty() {
        let guard = pool.fetch_page_mut(page_id, true).await?;
        let mut heap_page = HeapPage::new(guard);

        for (slot_id, new_infomask) in hint_updates {
            if let Some(mut current_header) = heap_page.get_header(slot_id) {
                current_header.infomask = current_header.infomask.merge(new_infomask);
                // Hint bit write-back is best-effort; failure does not affect correctness.
                let _ = heap_page.update_header(slot_id, current_header);
            }
        }
    }

    Ok((tuples, next_page))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::datum::Value;
    use crate::heap::page::HeapPage;
    use crate::storage::tests::test_pool;
    use crate::tx::{CommandId, TransactionManager, TxId};

    #[tokio::test]
    async fn test_scan_visible_page_frozen_tuples() {
        let pool = test_pool();
        let tx_manager = TransactionManager::new();

        let page_id = pool
            .new_heap_page(|page| {
                page.insert(
                    &Record::new(vec![Value::Bigint(10)]),
                    TxId::FROZEN,
                    CommandId::FIRST,
                )
                .unwrap();
                page.insert(
                    &Record::new(vec![Value::Bigint(20)]),
                    TxId::FROZEN,
                    CommandId::FIRST,
                )
                .unwrap();
                page.insert(
                    &Record::new(vec![Value::Bigint(30)]),
                    TxId::FROZEN,
                    CommandId::FIRST,
                )
                .unwrap();
            })
            .await;

        let txid = tx_manager.begin();
        let snapshot = tx_manager.snapshot(txid, CommandId::FIRST);
        let schema = [Type::Bigint];

        let (tuples, next_page) =
            scan_visible_page(&pool, page_id, &schema, &snapshot, &tx_manager)
                .await
                .unwrap();

        assert_eq!(tuples.len(), 3);
        assert_eq!(tuples[0].0.page_id, page_id);
        assert_eq!(tuples[0].0.slot_id, 0);
        assert_eq!(tuples[0].1.values, vec![Value::Bigint(10)]);
        assert_eq!(tuples[1].1.values, vec![Value::Bigint(20)]);
        assert_eq!(tuples[2].1.values, vec![Value::Bigint(30)]);
        assert_eq!(next_page, None);
    }

    #[tokio::test]
    async fn test_scan_visible_page_empty() {
        let pool = test_pool();
        let tx_manager = TransactionManager::new();

        let page_id = pool.new_heap_page(|_| {}).await;

        let txid = tx_manager.begin();
        let snapshot = tx_manager.snapshot(txid, CommandId::FIRST);
        let schema = [Type::Bigint];

        let (tuples, next_page) =
            scan_visible_page(&pool, page_id, &schema, &snapshot, &tx_manager)
                .await
                .unwrap();

        assert!(tuples.is_empty());
        assert_eq!(next_page, None);
    }

    #[tokio::test]
    async fn test_scan_sets_xmin_committed_hint_bit() {
        let pool = test_pool();
        let tx_manager = TransactionManager::new();

        let tx1 = tx_manager.begin();
        let page_id = pool
            .new_heap_page(|page| {
                page.insert(&Record::new(vec![Value::Bigint(42)]), tx1, CommandId::FIRST)
                    .unwrap();
            })
            .await;
        tx_manager.commit(tx1).unwrap();

        // Before scan: no hint bits
        {
            let guard = pool.fetch_page(page_id).await.unwrap();
            let page = HeapPage::new(guard);
            let header = page.get_header(0).unwrap();
            assert!(!header.infomask.has_xmin_hint());
        }

        // Scan should set hint bits
        let tx2 = tx_manager.begin();
        let snapshot = tx_manager.snapshot(tx2, CommandId::FIRST);
        let schema = [Type::Bigint];
        let (tuples, _) = scan_visible_page(&pool, page_id, &schema, &snapshot, &tx_manager)
            .await
            .unwrap();
        assert_eq!(tuples.len(), 1);

        // After scan: xmin_committed should be set
        {
            let guard = pool.fetch_page(page_id).await.unwrap();
            let page = HeapPage::new(guard);
            let header = page.get_header(0).unwrap();
            assert!(header.infomask.xmin_committed());
        }
    }

    #[tokio::test]
    async fn test_scan_sets_xmin_aborted_hint_bit() {
        let pool = test_pool();
        let tx_manager = TransactionManager::new();

        let tx1 = tx_manager.begin();
        let page_id = pool
            .new_heap_page(|page| {
                page.insert(&Record::new(vec![Value::Bigint(42)]), tx1, CommandId::FIRST)
                    .unwrap();
            })
            .await;
        tx_manager.abort(tx1).unwrap();

        // Scan (tuple not visible, but hint bits should still be set)
        let tx2 = tx_manager.begin();
        let snapshot = tx_manager.snapshot(tx2, CommandId::FIRST);
        let schema = [Type::Bigint];
        let (tuples, _) = scan_visible_page(&pool, page_id, &schema, &snapshot, &tx_manager)
            .await
            .unwrap();
        assert!(tuples.is_empty());

        // xmin_aborted should be set
        {
            let guard = pool.fetch_page(page_id).await.unwrap();
            let page = HeapPage::new(guard);
            let header = page.get_header(0).unwrap();
            assert!(header.infomask.xmin_aborted());
        }
    }

    #[tokio::test]
    async fn test_scan_sets_xmax_hint_bits() {
        let pool = test_pool();
        let tx_manager = TransactionManager::new();

        // Insert and commit
        let tx1 = tx_manager.begin();
        let page_id = pool
            .new_heap_page(|page| {
                page.insert(&Record::new(vec![Value::Bigint(1)]), tx1, CommandId::FIRST)
                    .unwrap();
            })
            .await;
        tx_manager.commit(tx1).unwrap();

        // Delete and commit
        let tx2 = tx_manager.begin();
        {
            let guard = pool.fetch_page_mut(page_id, true).await.unwrap();
            let mut page = HeapPage::new(guard);
            let mut header = page.get_header(0).unwrap();
            header.xmax = tx2;
            header.cmax = CommandId::FIRST;
            page.update_header(0, header).unwrap();
        }
        tx_manager.commit(tx2).unwrap();

        // Scan — tuple invisible (deleted), but both xmin and xmax hint bits should be set
        let tx3 = tx_manager.begin();
        let snapshot = tx_manager.snapshot(tx3, CommandId::FIRST);
        let schema = [Type::Bigint];
        let (tuples, _) = scan_visible_page(&pool, page_id, &schema, &snapshot, &tx_manager)
            .await
            .unwrap();
        assert!(tuples.is_empty());

        {
            let guard = pool.fetch_page(page_id).await.unwrap();
            let page = HeapPage::new(guard);
            let header = page.get_header(0).unwrap();
            assert!(header.infomask.xmin_committed());
            assert!(header.infomask.xmax_committed());
        }
    }

    #[tokio::test]
    async fn test_scan_skips_write_when_hints_already_set() {
        let pool = test_pool();
        let tx_manager = TransactionManager::new();

        // Insert with FROZEN — no hint bit updates needed
        let page_id = pool
            .new_heap_page(|page| {
                page.insert(
                    &Record::new(vec![Value::Bigint(10)]),
                    TxId::FROZEN,
                    CommandId::FIRST,
                )
                .unwrap();
            })
            .await;

        let tx = tx_manager.begin();
        let snapshot = tx_manager.snapshot(tx, CommandId::FIRST);
        let schema = [Type::Bigint];

        // Multiple scans should all succeed (no write pass triggered for FROZEN)
        for _ in 0..3 {
            let (tuples, _) = scan_visible_page(&pool, page_id, &schema, &snapshot, &tx_manager)
                .await
                .unwrap();
            assert_eq!(tuples.len(), 1);
        }
    }

    #[tokio::test]
    async fn test_scan_visible_page_mvcc_filtering() {
        let pool = test_pool();
        let tx_manager = TransactionManager::new();

        // tx1 inserts a tuple but does NOT commit
        let tx1 = tx_manager.begin();
        let page_id = pool
            .new_heap_page(|page| {
                page.insert(&Record::new(vec![Value::Bigint(42)]), tx1, CommandId::FIRST)
                    .unwrap();
            })
            .await;

        // tx2 takes a snapshot — tx1's uncommitted tuple should not be visible
        let tx2 = tx_manager.begin();
        let snapshot = tx_manager.snapshot(tx2, CommandId::FIRST);
        let schema = [Type::Bigint];

        let (tuples, _) = scan_visible_page(&pool, page_id, &schema, &snapshot, &tx_manager)
            .await
            .unwrap();

        assert!(
            tuples.is_empty(),
            "uncommitted tuple from another transaction should not be visible"
        );

        // After tx1 commits, a new snapshot from tx3 should see it
        tx_manager.commit(tx1).unwrap();
        let tx3 = tx_manager.begin();
        let snapshot3 = tx_manager.snapshot(tx3, CommandId::FIRST);

        let (tuples, _) = scan_visible_page(&pool, page_id, &schema, &snapshot3, &tx_manager)
            .await
            .unwrap();

        assert_eq!(tuples.len(), 1);
        assert_eq!(tuples[0].1.values, vec![Value::Bigint(42)]);
    }
}
