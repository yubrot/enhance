//! Multi-page heap tuple scanner.
//!
//! [`HeapScanner`] walks a heap page chain (linked via `HeapPage::next_page`)
//! and yields all tuples without MVCC filtering. The caller is responsible for
//! applying visibility checks.

use crate::datum::Type;
use crate::storage::{BufferPool, PageId, Replacer, Storage};
use crate::tx::TupleHeader;

use super::error::HeapError;
use super::page::{HeapPage, SlotId};
use super::record::Record;

/// Async iterator over all tuples in a heap page chain.
///
/// Walks pages via `HeapPage::next_page()` and yields every non-deleted slot
/// as `(PageId, SlotId, TupleHeader, Record)`. No MVCC filtering is applied;
/// the caller must check visibility.
pub struct HeapScanner<'a, S: Storage, R: Replacer> {
    pool: &'a BufferPool<S, R>,
    schema: &'a [Type],
    next_page_id: Option<PageId>,
}

impl<'a, S: Storage, R: Replacer> HeapScanner<'a, S, R> {
    /// Creates a new scanner starting at `first_page`.
    pub fn new(pool: &'a BufferPool<S, R>, schema: &'a [Type], first_page: PageId) -> Self {
        Self {
            pool,
            schema,
            next_page_id: Some(first_page),
        }
    }

    /// Scans the next page and returns all tuples on it.
    ///
    /// Returns `Ok(None)` when the chain is exhausted.
    /// Each call advances to the next page in the chain.
    ///
    /// All tuples from a page are collected into a `Vec` before the page
    /// latch is released, minimizing latch hold time.
    pub async fn next_page(
        &mut self,
    ) -> Result<Option<Vec<(PageId, SlotId, TupleHeader, Record)>>, HeapError> {
        let page_id = match self.next_page_id.take() {
            Some(id) => id,
            None => return Ok(None),
        };

        let guard = self.pool.fetch_page(page_id).await?;
        let heap_page = HeapPage::new(guard);

        // Advance to next page before collecting tuples
        self.next_page_id = heap_page.next_page();

        let tuples: Vec<_> = heap_page
            .scan(self.schema)
            .map(|(slot_id, header, record)| (page_id, slot_id, header, record))
            .collect();

        Ok(Some(tuples))
    }

    /// Collects all tuples from the entire page chain.
    ///
    /// This is a convenience method that drains the scanner. Useful for
    /// catalog scans where the result set is small.
    ///
    /// NOTE: This loads the entire table into memory. For user-table scans,
    /// prefer the page-by-page `next_page()` interface.
    pub async fn collect_all(
        &mut self,
    ) -> Result<Vec<(PageId, SlotId, TupleHeader, Record)>, HeapError> {
        let mut all = Vec::new();
        while let Some(page_tuples) = self.next_page().await? {
            all.extend(page_tuples);
        }
        Ok(all)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::datum::Value;
    use crate::storage::{BufferPool, LruReplacer, MemoryStorage};
    use crate::tx::{CommandId, TxId};
    use std::sync::Arc;

    async fn create_pool() -> Arc<BufferPool<MemoryStorage, LruReplacer>> {
        Arc::new(BufferPool::new(MemoryStorage::new(), LruReplacer::new(100), 100))
    }

    /// Creates a chain of `page_count` heap pages and inserts `records_per_page`
    /// integer records on each. Returns the first page ID.
    async fn setup_page_chain(
        pool: &BufferPool<MemoryStorage, LruReplacer>,
        page_count: usize,
        records_per_page: usize,
    ) -> PageId {
        let txid = TxId::FROZEN;
        let cid = CommandId::FIRST;
        let mut value_counter = 0i64;

        // Create pages
        let mut page_ids = Vec::new();
        for _ in 0..page_count {
            let guard = pool.new_page().await.unwrap();
            let page_id = guard.page_id();
            HeapPage::new(guard).init();
            page_ids.push(page_id);
        }

        // Link pages and insert records
        for (i, &page_id) in page_ids.iter().enumerate() {
            let mut page = HeapPage::new(pool.fetch_page_mut(page_id, true).await.unwrap());
            if i + 1 < page_count {
                page.set_next_page(Some(page_ids[i + 1]));
            }
            for _ in 0..records_per_page {
                let record = Record::new(vec![Value::Bigint(value_counter)]);
                page.insert(&record, txid, cid).unwrap();
                value_counter += 1;
            }
        }

        page_ids[0]
    }

    #[tokio::test]
    async fn test_scan_single_page() {
        let pool = create_pool().await;
        let first_page = setup_page_chain(&pool, 1, 3).await;

        let schema = [Type::Bigint];
        let mut scanner = HeapScanner::new(&pool, &schema, first_page);
        let tuples = scanner.collect_all().await.unwrap();

        assert_eq!(tuples.len(), 3);
        assert_eq!(tuples[0].3.values, vec![Value::Bigint(0)]);
        assert_eq!(tuples[1].3.values, vec![Value::Bigint(1)]);
        assert_eq!(tuples[2].3.values, vec![Value::Bigint(2)]);
    }

    #[tokio::test]
    async fn test_scan_multi_page_chain() {
        let pool = create_pool().await;
        let first_page = setup_page_chain(&pool, 3, 2).await;

        let schema = [Type::Bigint];
        let mut scanner = HeapScanner::new(&pool, &schema, first_page);
        let tuples = scanner.collect_all().await.unwrap();

        // 3 pages * 2 records = 6 tuples
        assert_eq!(tuples.len(), 6);
        for (i, tuple) in tuples.iter().enumerate() {
            assert_eq!(tuple.3.values, vec![Value::Bigint(i as i64)]);
        }
    }

    #[tokio::test]
    async fn test_scan_empty_table() {
        let pool = create_pool().await;
        let first_page = setup_page_chain(&pool, 1, 0).await;

        let schema = [Type::Bigint];
        let mut scanner = HeapScanner::new(&pool, &schema, first_page);
        let tuples = scanner.collect_all().await.unwrap();

        assert!(tuples.is_empty());
    }

    #[tokio::test]
    async fn test_scan_with_empty_intermediate_page() {
        let pool = create_pool().await;
        let txid = TxId::FROZEN;
        let cid = CommandId::FIRST;

        // Create 3 pages manually: page1 has data, page2 is empty, page3 has data
        let p1 = pool.new_page().await.unwrap();
        let p1_id = p1.page_id();
        HeapPage::new(p1).init();

        let p2 = pool.new_page().await.unwrap();
        let p2_id = p2.page_id();
        HeapPage::new(p2).init();

        let p3 = pool.new_page().await.unwrap();
        let p3_id = p3.page_id();
        HeapPage::new(p3).init();

        // Link: p1 -> p2 -> p3
        {
            let mut page1 = HeapPage::new(pool.fetch_page_mut(p1_id, true).await.unwrap());
            page1.set_next_page(Some(p2_id));
            page1
                .insert(&Record::new(vec![Value::Bigint(10)]), txid, cid)
                .unwrap();
        }
        {
            let mut page2 = HeapPage::new(pool.fetch_page_mut(p2_id, true).await.unwrap());
            page2.set_next_page(Some(p3_id));
            // No records on page2
        }
        {
            let mut page3 = HeapPage::new(pool.fetch_page_mut(p3_id, true).await.unwrap());
            page3
                .insert(&Record::new(vec![Value::Bigint(30)]), txid, cid)
                .unwrap();
        }

        let schema = [Type::Bigint];
        let mut scanner = HeapScanner::new(&pool, &schema, p1_id);
        let tuples = scanner.collect_all().await.unwrap();

        assert_eq!(tuples.len(), 2);
        assert_eq!(tuples[0].3.values, vec![Value::Bigint(10)]);
        assert_eq!(tuples[0].0, p1_id);
        assert_eq!(tuples[1].3.values, vec![Value::Bigint(30)]);
        assert_eq!(tuples[1].0, p3_id);
    }

    #[tokio::test]
    async fn test_scan_page_by_page() {
        let pool = create_pool().await;
        let first_page = setup_page_chain(&pool, 2, 2).await;

        let schema = [Type::Bigint];
        let mut scanner = HeapScanner::new(&pool, &schema, first_page);

        // First page
        let page1 = scanner.next_page().await.unwrap().unwrap();
        assert_eq!(page1.len(), 2);
        assert_eq!(page1[0].3.values, vec![Value::Bigint(0)]);
        assert_eq!(page1[1].3.values, vec![Value::Bigint(1)]);

        // Second page
        let page2 = scanner.next_page().await.unwrap().unwrap();
        assert_eq!(page2.len(), 2);
        assert_eq!(page2[0].3.values, vec![Value::Bigint(2)]);
        assert_eq!(page2[1].3.values, vec![Value::Bigint(3)]);

        // Exhausted
        assert!(scanner.next_page().await.unwrap().is_none());
        // Idempotent
        assert!(scanner.next_page().await.unwrap().is_none());
    }
}
