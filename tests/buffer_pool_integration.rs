//! Integration tests for BufferPool.
//!
//! These tests verify the buffer pool behavior with both MemoryStorage
//! and FileStorage backends, including concurrent access patterns.

use std::sync::Arc;

use enhance::storage::{
    BufferPool, BufferPoolError, FileStorage, LruReplacer, MemoryStorage, PAGE_SIZE, PageId,
    Replacer, Storage,
};
use tempfile::tempdir;

/// Generic test runner for buffer pool operations.
async fn test_buffer_pool_basic<S: Storage>(storage: S) {
    let replacer = LruReplacer::new(10);
    let bpm = BufferPool::new(storage, replacer, 10);

    // Test new_page
    let page_id;
    {
        let mut guard = bpm.new_page().await.unwrap();
        page_id = guard.page_id();
        assert_eq!(guard.data().len(), PAGE_SIZE);

        // Write some data
        guard.data_mut()[0] = 0xDE;
        guard.data_mut()[1] = 0xAD;
        guard.data_mut()[2] = 0xBE;
        guard.data_mut()[3] = 0xEF;
        guard.mark_dirty();
    }

    // Flush to storage
    bpm.flush_page(page_id).await.unwrap();

    // Fetch and verify
    {
        let guard = bpm.fetch_page(page_id).await.unwrap();
        assert_eq!(guard.data()[0], 0xDE);
        assert_eq!(guard.data()[1], 0xAD);
        assert_eq!(guard.data()[2], 0xBE);
        assert_eq!(guard.data()[3], 0xEF);
    }
}

#[tokio::test]
async fn test_buffer_pool_with_memory_storage() {
    let storage = MemoryStorage::new();
    test_buffer_pool_basic(storage).await;
}

#[tokio::test]
async fn test_buffer_pool_with_file_storage() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.db");
    let storage = FileStorage::open(&path).await.unwrap();
    test_buffer_pool_basic(storage).await;
}

/// Test that eviction works correctly and dirty pages are written back.
async fn test_eviction_writes_back<S: Storage>(storage: S) {
    let replacer = LruReplacer::new(2); // Small pool to force eviction
    let bpm = BufferPool::new(storage, replacer, 2);

    // Create and modify page 0
    let page0;
    {
        let mut guard = bpm.new_page().await.unwrap();
        page0 = guard.page_id();
        guard.data_mut()[0] = 100;
        guard.mark_dirty();
    }

    // Create page 1
    let page1;
    {
        let mut guard = bpm.new_page().await.unwrap();
        page1 = guard.page_id();
        guard.data_mut()[0] = 101;
        guard.mark_dirty();
    }

    // Create page 2 - this should evict page 0 (LRU)
    let page2;
    {
        let mut guard = bpm.new_page().await.unwrap();
        page2 = guard.page_id();
        guard.data_mut()[0] = 102;
        guard.mark_dirty();
    }

    // Fetch page 0 back - should have been written to storage during eviction
    {
        let guard = bpm.fetch_page(page0).await.unwrap();
        assert_eq!(guard.data()[0], 100);
    }

    // Verify other pages still accessible
    {
        let guard = bpm.fetch_page(page1).await.unwrap();
        assert_eq!(guard.data()[0], 101);
    }
    {
        let guard = bpm.fetch_page(page2).await.unwrap();
        assert_eq!(guard.data()[0], 102);
    }
}

#[tokio::test]
async fn test_eviction_with_memory_storage() {
    let storage = MemoryStorage::new();
    test_eviction_writes_back(storage).await;
}

#[tokio::test]
async fn test_eviction_with_file_storage() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.db");
    let storage = FileStorage::open(&path).await.unwrap();
    test_eviction_writes_back(storage).await;
}

/// Test concurrent read access to the same page.
#[tokio::test]
async fn test_concurrent_read_access() {
    let storage = MemoryStorage::new();
    let page_id = storage.allocate_page().await.unwrap();

    // Write initial data
    let mut buf = vec![0u8; PAGE_SIZE];
    buf[0] = 42;
    storage.write_page(page_id, &buf).await.unwrap();

    let replacer = LruReplacer::new(10);
    let bpm = Arc::new(BufferPool::new(storage, replacer, 10));

    // Spawn multiple readers
    let mut handles = vec![];
    for _ in 0..10 {
        let bpm_clone = Arc::clone(&bpm);
        handles.push(tokio::spawn(async move {
            for _ in 0..100 {
                let guard = bpm_clone.fetch_page(page_id).await.unwrap();
                assert_eq!(guard.data()[0], 42);
            }
        }));
    }

    for handle in handles {
        handle.await.unwrap();
    }
}

/// Test concurrent access to different pages.
#[tokio::test]
async fn test_concurrent_different_pages() {
    let storage = MemoryStorage::new();

    // Pre-allocate pages
    for i in 0..10 {
        let page_id = storage.allocate_page().await.unwrap();
        let mut buf = vec![0u8; PAGE_SIZE];
        buf[0] = i as u8;
        storage.write_page(page_id, &buf).await.unwrap();
    }

    let replacer = LruReplacer::new(10);
    let bpm = Arc::new(BufferPool::new(storage, replacer, 10));

    // Spawn tasks accessing different pages
    let mut handles = vec![];
    for i in 0..10 {
        let bpm_clone = Arc::clone(&bpm);
        handles.push(tokio::spawn(async move {
            let page_id = PageId::new(i);
            for _ in 0..50 {
                let guard = bpm_clone.fetch_page(page_id).await.unwrap();
                assert_eq!(guard.data()[0], i as u8);
            }
        }));
    }

    for handle in handles {
        handle.await.unwrap();
    }
}

/// Test that NoFreeFrames error is returned when all frames are pinned.
#[tokio::test]
async fn test_no_free_frames_error() {
    let storage = MemoryStorage::new();

    // Allocate pages in storage
    for _ in 0..5 {
        storage.allocate_page().await.unwrap();
    }

    // Create a small buffer pool
    let replacer = LruReplacer::new(3);
    let bpm = BufferPool::new(storage, replacer, 3);

    // Pin all frames
    let _guard0 = bpm.fetch_page(PageId::new(0)).await.unwrap();
    let _guard1 = bpm.fetch_page(PageId::new(1)).await.unwrap();
    let _guard2 = bpm.fetch_page(PageId::new(2)).await.unwrap();

    // Try to fetch another page - should fail
    let result = bpm.fetch_page(PageId::new(3)).await;
    assert!(matches!(result, Err(BufferPoolError::NoFreeFrames)));
}

/// Test flush_all writes all dirty pages to storage.
#[tokio::test]
async fn test_flush_all() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("flush_all_test.db");

    // Create pages, modify them, and flush
    {
        let storage = FileStorage::open(&path).await.unwrap();
        let replacer = LruReplacer::new(10);
        let bpm = BufferPool::new(storage, replacer, 10);

        // Create multiple dirty pages
        for i in 0..5u8 {
            let mut guard = bpm.new_page().await.unwrap();
            guard.data_mut()[0] = i;
            guard.data_mut()[1] = i.wrapping_mul(2);
            guard.mark_dirty();
        }

        // Flush all dirty pages to storage
        bpm.flush_all().await.unwrap();
    }
    // BPM and storage dropped here, file closed

    // Reopen and verify data was persisted
    {
        let storage = FileStorage::open(&path).await.unwrap();
        let replacer = LruReplacer::new(10);
        let bpm = BufferPool::new(storage, replacer, 10);

        for i in 0..5u8 {
            let guard = bpm.fetch_page(PageId::new(i as u64)).await.unwrap();
            assert_eq!(guard.data()[0], i, "page {} byte 0 mismatch", i);
            assert_eq!(
                guard.data()[1],
                i.wrapping_mul(2),
                "page {} byte 1 mismatch",
                i
            );
        }
    }
}

/// Test page_count tracking.
#[tokio::test]
async fn test_page_count() {
    let storage = MemoryStorage::new();
    let replacer = LruReplacer::new(10);
    let bpm = BufferPool::new(storage, replacer, 10);

    assert_eq!(bpm.page_count(), 0);

    // Create pages
    for i in 1..=5 {
        let _guard = bpm.new_page().await.unwrap();
        assert_eq!(bpm.page_count(), i);
    }
}

/// Test custom replacer implementation.
struct FifoReplacer {
    queue: std::collections::VecDeque<usize>,
}

impl FifoReplacer {
    fn new(_capacity: usize) -> Self {
        Self {
            queue: std::collections::VecDeque::new(),
        }
    }
}

impl Replacer for FifoReplacer {
    fn unpin(&mut self, frame_id: usize) {
        if !self.queue.contains(&frame_id) {
            self.queue.push_back(frame_id);
        }
    }

    fn pin(&mut self, frame_id: usize) {
        self.queue.retain(|&id| id != frame_id);
    }

    fn evict(&mut self) -> Option<usize> {
        self.queue.pop_front()
    }

    fn size(&self) -> usize {
        self.queue.len()
    }
}

#[tokio::test]
async fn test_custom_replacer() {
    let storage = MemoryStorage::new();
    let replacer = FifoReplacer::new(3);
    let bpm = BufferPool::new(storage, replacer, 3);

    // Create pages
    for i in 0..3 {
        let mut guard = bpm.new_page().await.unwrap();
        guard.data_mut()[0] = i as u8;
        guard.mark_dirty();
    }

    // Create page 3 - should evict page 0 (FIFO order)
    {
        let mut guard = bpm.new_page().await.unwrap();
        guard.data_mut()[0] = 3;
        guard.mark_dirty();
    }

    // Verify page 0 was evicted but data preserved
    let guard = bpm.fetch_page(PageId::new(0)).await.unwrap();
    assert_eq!(guard.data()[0], 0);
}
