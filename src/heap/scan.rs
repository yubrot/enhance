//! MVCC-aware single-page heap scan.
//!
//! [`scan_visible_page`] fetches a single heap page, filters tuples by
//! snapshot visibility, and returns `(TupleId, Record)` pairs along with
//! the next page in the chain.

use crate::datum::Type;
use crate::storage::{BufferPool, PageId, Replacer, Storage};
use crate::tx::{Snapshot, TransactionManager};

use super::TupleId;
use super::error::HeapError;
use super::page::HeapPage;
use super::record::Record;

/// Scans a single heap page and returns all MVCC-visible tuples.
///
/// Fetches the page via the buffer pool, applies `HeapPage::scan` to
/// enumerate all non-deleted slots, filters by snapshot visibility, and
/// collects the results as `(TupleId, Record)` pairs.
///
/// Also returns the next page ID in the chain (if any) so that the caller
/// can continue scanning multi-page tables via a while-let loop.
///
/// All tuples from the page are collected into a `Vec` before the page
/// latch is released, minimizing latch hold time.
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
    let guard = pool.fetch_page(page_id).await?;
    let heap_page = HeapPage::new(guard);
    let next_page = heap_page.next_page();

    let tuples: Vec<_> = heap_page
        .scan(schema)
        .filter(|(_slot_id, header, _record)| snapshot.is_tuple_visible(header, tx_manager))
        .map(|(slot_id, _header, record)| {
            let tid = TupleId { page_id, slot_id };
            (tid, record)
        })
        .collect();

    Ok((tuples, next_page))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::datum::Value;
    use crate::heap::page::HeapPage;
    use crate::storage::{BufferPool, LruReplacer, MemoryStorage};
    use crate::tx::{CommandId, TransactionManager, TxId};
    use std::sync::Arc;

    async fn create_pool() -> Arc<BufferPool<MemoryStorage, LruReplacer>> {
        Arc::new(BufferPool::new(
            MemoryStorage::new(),
            LruReplacer::new(100),
            100,
        ))
    }

    #[tokio::test]
    async fn test_scan_visible_page_frozen_tuples() {
        let pool = create_pool().await;
        let tx_manager = TransactionManager::new();

        // Create a page with FROZEN tuples (always visible)
        let guard = pool.new_page().await.unwrap();
        let page_id = guard.page_id();
        let mut page = HeapPage::new(guard);
        page.init();

        let record0 = Record::new(vec![Value::Bigint(10)]);
        let record1 = Record::new(vec![Value::Bigint(20)]);
        let record2 = Record::new(vec![Value::Bigint(30)]);
        page.insert(&record0, TxId::FROZEN, CommandId::FIRST)
            .unwrap();
        page.insert(&record1, TxId::FROZEN, CommandId::FIRST)
            .unwrap();
        page.insert(&record2, TxId::FROZEN, CommandId::FIRST)
            .unwrap();
        drop(page);

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
        let pool = create_pool().await;
        let tx_manager = TransactionManager::new();

        let guard = pool.new_page().await.unwrap();
        let page_id = guard.page_id();
        HeapPage::new(guard).init();

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
    async fn test_scan_visible_page_mvcc_filtering() {
        let pool = create_pool().await;
        let tx_manager = TransactionManager::new();

        // tx1 inserts a tuple but does NOT commit
        let tx1 = tx_manager.begin();
        let guard = pool.new_page().await.unwrap();
        let page_id = guard.page_id();
        let mut page = HeapPage::new(guard);
        page.init();
        page.insert(&Record::new(vec![Value::Bigint(42)]), tx1, CommandId::FIRST)
            .unwrap();
        drop(page);

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
