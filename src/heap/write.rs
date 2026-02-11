//! Multi-page heap tuple insertion.
//!
//! [`insert`] walks a heap page chain to find a page with free space,
//! and allocates new pages when needed. Handles page chain linkage automatically.
//!
//! Implemented as a free function rather than a struct because insertion is
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
}
