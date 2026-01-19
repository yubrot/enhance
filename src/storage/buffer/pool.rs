//! Buffer pool manager for caching pages in memory.
//!
//! The buffer pool manager sits between the storage layer and higher-level
//! components, caching frequently accessed pages in memory to reduce I/O.

use std::collections::HashMap;
use std::sync::Mutex;

use tokio::sync::RwLock;

use crate::storage::{PageData, PageId, Storage, StorageError};

use super::error::BufferPoolError;
use super::frame::{FrameId, FrameMetadata};
use super::guard::{PageReadGuard, PageWriteGuard};
use super::replacer::Replacer;

/// Buffer pool manager for caching pages in memory.
///
/// The buffer pool maintains a fixed number of frames (in-memory page slots)
/// and maps pages from storage to these frames on demand. When all frames
/// are in use, the LRU (or other) replacement policy selects a victim frame
/// for eviction.
///
/// # Architecture
///
/// ```text
/// +-------------------+
/// |   Query Engine    |
/// +-------------------+
///          |
///          v
/// +-------------------+
/// | BufferPool        |  <- You are here
/// +-------------------+
///          |
///          v
/// +-------------------+
/// |  Storage (trait)  |
/// +-------------------+
/// ```
///
/// # Thread Safety
///
/// The buffer pool is designed for concurrent access:
/// - Multiple readers can access different pages simultaneously
/// - Multiple readers can access the same page simultaneously (shared lock)
/// - Writers get exclusive access to their page (exclusive lock)
/// - The state (page table, metadata, replacer) is protected by a mutex
pub struct BufferPool<S: Storage, R: Replacer> {
    inner: BufferPoolInner<S, R>,
}

// # Latch Hierarchy
//
// To prevent deadlocks, locks must be acquired in strict order:
// 1. State mutex (page_table, frame_metadata, free_list, replacer)
// 2. Frame data RwLock (in PageId order when multiple frames needed)
//
// **NEVER** acquire the state lock while holding a frame data lock.
//
// NOTE: For production, consider these improvements:
// - Use `parking_lot::Mutex` for better performance (no poisoning)
// - Split state into multiple locks to reduce contention
// - Add metrics (hit rate, eviction count, dirty page count)
// - Implement background flusher thread for dirty pages
// - Support page prefetching for sequential scans

/// Internal state of the buffer pool manager.
///
/// This struct is exposed to guards for the unpin operation.
pub(super) struct BufferPoolInner<S: Storage, R: Replacer> {
    /// The underlying storage backend.
    storage: S,

    /// Frame data array (indexed by FrameId).
    ///
    /// Each element holds page data protected by an async RwLock for concurrent
    /// access. Corresponding metadata (page_id, pin_count, is_dirty) is stored
    /// in `state.frame_metadata` at the same index.
    frames: Vec<RwLock<PageData>>,

    /// Protected mutable state (page table, metadata, free list, replacer).
    ///
    /// Uses `std::sync::Mutex` to allow synchronous access from `Drop`.
    state: Mutex<BufferPoolState<R>>,
}

/// Mutable state protected by the state mutex.
struct BufferPoolState<R: Replacer> {
    /// Maps PageId -> FrameId for quick lookup.
    page_table: HashMap<PageId, FrameId>,

    /// Metadata for each frame (indexed by FrameId).
    frame_metadata: Vec<FrameMetadata>,

    /// Free frames (not currently holding any page).
    free_list: Vec<FrameId>,

    /// Replacement policy for selecting eviction victims.
    replacer: R,
}

impl<S: Storage, R: Replacer> BufferPool<S, R> {
    /// Creates a new buffer pool manager.
    ///
    /// # Arguments
    ///
    /// * `storage` - The underlying storage backend
    /// * `replacer` - The page replacement policy
    /// * `pool_size` - Number of frames the buffer pool can hold
    ///
    /// # Panics
    ///
    /// Panics if `pool_size` is 0.
    pub fn new(storage: S, replacer: R, pool_size: usize) -> Self {
        assert!(pool_size > 0, "pool_size must be > 0");

        let frames: Vec<_> = (0..pool_size)
            .map(|_| RwLock::new(PageData::new()))
            .collect();
        let frame_metadata: Vec<_> = (0..pool_size).map(|_| FrameMetadata::vacant()).collect();
        let free_list: Vec<_> = (0..pool_size).collect();

        let state = BufferPoolState {
            page_table: HashMap::with_capacity(pool_size),
            frame_metadata,
            free_list,
            replacer,
        };

        Self {
            inner: BufferPoolInner {
                storage,
                frames,
                state: Mutex::new(state),
            },
        }
    }

    /// Fetches a page for reading.
    ///
    /// Returns a guard that holds a pin on the page, preventing eviction
    /// until dropped.
    ///
    /// # Errors
    ///
    /// - `BufferPoolError::NoFreeFrames` if the pool is full and all pages are pinned
    /// - `BufferPoolError::Storage` if the page doesn't exist or I/O fails
    pub async fn fetch_page(
        &self,
        page_id: PageId,
    ) -> Result<PageReadGuard<'_, S, R>, BufferPoolError> {
        let frame_id = self.inner.acquire(page_id).await?;
        let data_guard = self.inner.frames[frame_id].read().await;

        Ok(PageReadGuard {
            inner: &self.inner,
            frame_id,
            page_id,
            data_guard,
        })
    }

    /// Fetches a page for writing.
    ///
    /// Returns a mutable guard. Call `mark_dirty()` after modifications.
    ///
    /// # Errors
    ///
    /// - `BufferPoolError::NoFreeFrames` if the pool is full and all pages are pinned
    /// - `BufferPoolError::Storage` if the page doesn't exist or I/O fails
    pub async fn fetch_page_mut(
        &self,
        page_id: PageId,
    ) -> Result<PageWriteGuard<'_, S, R>, BufferPoolError> {
        let frame_id = self.inner.acquire(page_id).await?;
        let data_guard = self.inner.frames[frame_id].write().await;

        Ok(PageWriteGuard {
            inner: &self.inner,
            frame_id,
            page_id,
            data_guard,
            is_dirty: false,
        })
    }

    /// Creates a new page in storage and returns a mutable guard.
    ///
    /// # Errors
    ///
    /// - `BufferPoolError::NoFreeFrames` if the pool is full and all pages are pinned
    /// - `BufferPoolError::Storage` if storage allocation fails
    pub async fn new_page(&self) -> Result<PageWriteGuard<'_, S, R>, BufferPoolError> {
        let page_id = self.inner.storage.allocate_page().await?;
        self.fetch_page_mut(page_id).await
    }

    /// Flushes a specific page to storage if dirty.
    ///
    /// # Errors
    ///
    /// Returns `BufferPoolError::Storage` if the write fails.
    pub async fn flush_page(&self, page_id: PageId) -> Result<(), BufferPoolError> {
        // Get frame_id and check if dirty while holding state lock briefly
        let frame_id = {
            let state = self.inner.state.lock().expect("state lock poisoned");
            match state.page_table.get(&page_id) {
                Some(&fid) if state.frame_metadata[fid].is_dirty => Some(fid),
                _ => None,
            }
        };

        if let Some(frame_id) = frame_id {
            // Acquire frame data lock for reading
            let data_guard = self.inner.frames[frame_id].read().await;

            // Write to storage
            self.inner
                .storage
                .write_page(page_id, data_guard.as_slice())
                .await?;

            // Clear dirty flag
            let mut state = self.inner.state.lock().expect("state lock poisoned");
            // Verify the frame still holds the same page
            if state.frame_metadata[frame_id].page_id == Some(page_id) {
                state.frame_metadata[frame_id].is_dirty = false;
            }
        }

        Ok(())
    }

    /// Flushes all dirty pages to storage.
    ///
    /// # Errors
    ///
    /// Returns `BufferPoolError::Storage` if any write fails.
    pub async fn flush_all(&self) -> Result<(), BufferPoolError> {
        // Collect all dirty pages first (to release state lock quickly)
        let dirty_pages: Vec<(FrameId, PageId)> = {
            let state = self.inner.state.lock().expect("state lock poisoned");
            state
                .frame_metadata
                .iter()
                .enumerate()
                .filter_map(|(frame_id, meta)| {
                    if meta.is_dirty {
                        meta.page_id.map(|page_id| (frame_id, page_id))
                    } else {
                        None
                    }
                })
                .collect()
        };

        // Flush each dirty page
        for (frame_id, page_id) in dirty_pages {
            let data_guard = self.inner.frames[frame_id].read().await;

            // Verify frame still holds the same page before writing
            {
                let state = self.inner.state.lock().expect("state lock poisoned");
                if state.frame_metadata[frame_id].page_id != Some(page_id) {
                    continue;
                }
            }

            self.inner
                .storage
                .write_page(page_id, data_guard.as_slice())
                .await?;

            // Clear dirty flag
            let mut state = self.inner.state.lock().expect("state lock poisoned");
            if state.frame_metadata[frame_id].page_id == Some(page_id) {
                state.frame_metadata[frame_id].is_dirty = false;
            }
        }

        // Sync to disk
        self.inner.storage.sync_all().await?;

        Ok(())
    }

    /// Returns the number of frames in the buffer pool.
    pub fn pool_size(&self) -> usize {
        self.inner.frames.len()
    }

    /// Returns the number of pages currently in the buffer pool.
    pub fn page_count(&self) -> usize {
        let state = self.inner.state.lock().expect("state lock poisoned");
        state.page_table.len()
    }
}

impl<S: Storage, R: Replacer> BufferPoolInner<S, R> {
    /// Acquires a frame for the given page, loading it from storage if necessary.
    ///
    /// This method handles:
    /// - Cache hit: Returns the existing frame (increments pin count)
    /// - Cache miss with free frame: Allocates a free frame and loads the page
    /// - Cache miss without free frame: Evicts a victim frame (writing back if dirty) and loads the page
    ///
    /// # Contract
    ///
    /// **The caller MUST call [`release`] exactly once for each successful `acquire`.**
    /// Failing to release will cause frame leaks (frames remain pinned forever).
    /// Releasing more than once will cause undefined behavior (double unpin).
    ///
    /// # Errors
    ///
    /// - `BufferPoolError::NoFreeFrames` if all frames are pinned
    /// - `BufferPoolError::Storage` if I/O fails
    async fn acquire(&self, page_id: PageId) -> Result<FrameId, BufferPoolError> {
        let new_frame_id = loop {
            let acquire_result = {
                let mut state = self.state.lock().expect("state lock poisoned");
                state.acquire_frame(page_id)
            };
            match acquire_result {
                AcquireFrame::Ready(frame_id) => return Ok(frame_id),
                AcquireFrame::ReadRequired(frame_id) => break frame_id,
                AcquireFrame::WriteBackRequired(frame_id, evict_page_id) => {
                    let write_result = {
                        let data = self.frames[frame_id].read().await;
                        self.storage.write_page(evict_page_id, data.as_slice()).await
                    };

                    let mut state = self.state.lock().expect("state lock poisoned");
                    match state.complete_write_back(frame_id, evict_page_id, write_result)? {
                        CompleteWriteBack::ReadRequired(frame_id) => break frame_id,
                        CompleteWriteBack::Retry => {}
                    }
                }
                AcquireFrame::Full => return Err(BufferPoolError::NoFreeFrames),
            }
            // FIXME: Potential busy loop if write back keeps failing
        };

        let read_result = {
            let mut data = self.frames[new_frame_id].write().await;
            self.storage.read_page(page_id, data.as_mut_slice()).await
        };

        let mut state = self.state.lock().expect("state lock poisoned");
        state.complete_read(new_frame_id, page_id, read_result)
    }

    /// Releases a previously acquired frame, decrementing its pin count.
    ///
    /// When the pin count reaches zero, the frame becomes eligible for eviction
    /// by the replacer.
    ///
    /// # Contract
    ///
    /// **This method MUST be called exactly once for each successful [`acquire`].**
    /// - Not calling release: Frame remains pinned forever (memory leak)
    /// - Calling release multiple times: Undefined behavior (double unpin)
    ///
    /// # Arguments
    ///
    /// * `frame_id` - The frame ID returned by a previous `acquire` call
    /// * `is_dirty` - If true, marks the frame as dirty (needs write-back before eviction)
    pub(super) fn release(&self, frame_id: FrameId, is_dirty: bool) {
        let mut state = self.state.lock().expect("state lock poisoned");
        state.unpin_frame(frame_id, is_dirty);
    }
}

#[derive(Debug, Clone, Copy)]
enum AcquireFrame {
    /// Page already in buffer pool, frame is pinned. Ready to use.
    Ready(FrameId),
    /// New frame allocated. Caller must read page and call `complete_read`.
    ReadRequired(FrameId),
    /// Dirty frame needs write back. Caller must write and call `complete_write_back`.
    WriteBackRequired(FrameId, PageId),
    /// All frames are pinned. Caller should return an error.
    Full,
}

#[derive(Debug, Clone, Copy)]
enum CompleteWriteBack {
    /// Write back succeeded and frame was evicted. Caller must read page and call `complete_read`.
    ReadRequired(FrameId),
    /// Eviction aborted (frame was pinned or dirtied during write back). Caller should retry `acquire_frame`.
    Retry,
}

impl<R: Replacer> BufferPoolState<R> {
    /// Acquires a frame for the given page.
    fn acquire_frame(&mut self, page_id: PageId) -> AcquireFrame {
        // Fast path: page already in buffer pool
        if let Some(&frame_id) = self.page_table.get(&page_id) {
            self.pin_frame(frame_id);
            return AcquireFrame::Ready(frame_id);
        }

        // Slow path: allocate a frame
        // Try to get a free frame first
        if let Some(frame_id) = self.free_list.pop() {
            return AcquireFrame::ReadRequired(frame_id);
        }

        // Need to evict - find a victim
        let Some(frame_id) = self.replacer.evict() else {
            return AcquireFrame::Full;
        };

        let Some(page_id) = self.frame_metadata[frame_id].page_id else {
            panic!("Evicted frame must be previously occupied");
        };
        debug_assert_eq!(self.frame_metadata[frame_id].pin_count, 0);

        if self.frame_metadata[frame_id].is_dirty {
            // Evicted frame is dirty - write back is required.
            // Pin the frame during write back to allow concurrent access to the same page
            // (other threads can use the in-memory data while we write it back).
            // Clear is_dirty so we can detect if someone modifies the page during write back.
            self.frame_metadata[frame_id].pin_count = 1;
            self.frame_metadata[frame_id].is_dirty = false;
            return AcquireFrame::WriteBackRequired(frame_id, page_id);
        }

        self.page_table.remove(&page_id);
        self.frame_metadata[frame_id] = FrameMetadata::vacant();
        AcquireFrame::ReadRequired(frame_id)
    }

    /// Completes a read operation initiated by `acquire_frame`.
    fn complete_read(
        &mut self,
        frame_id: FrameId,
        page_id: PageId,
        read_result: Result<(), StorageError>,
    ) -> Result<FrameId, BufferPoolError> {
        if let Err(e) = read_result {
            self.free_list.push(frame_id);
            return Err(e.into());
        }

        let frame_id = if let Some(&won_frame_id) = self.page_table.get(&page_id) {
            // Another thread won the race - discard our frame and use theirs
            self.free_list.push(frame_id);
            self.pin_frame(won_frame_id);
            won_frame_id
        } else {
            // Ready to use this frame
            self.page_table.insert(page_id, frame_id);
            self.frame_metadata[frame_id] = FrameMetadata::occupied(page_id);
            frame_id
        };

        Ok(frame_id)
    }

    /// Completes a write back operation initiated by `acquire_frame`.
    fn complete_write_back(
        &mut self,
        frame_id: FrameId,
        page_id: PageId,
        write_result: Result<(), StorageError>,
    ) -> Result<CompleteWriteBack, BufferPoolError> {
        if let Err(e) = write_result {
            // Write back failed: restore dirty flag
            self.unpin_frame(frame_id, true);
            return Err(e.into());
        }

        if self.frame_metadata[frame_id].pin_count > 1 || self.frame_metadata[frame_id].is_dirty {
            // Abort eviction if either:
            // - pin_count > 1: Another caller acquired this frame during write back and still holds it
            // - is_dirty: The page was modified during write back (the caller may have already released)
            // In both cases, preserve the current state and retry acquiring a frame.
            self.unpin_frame(frame_id, false /* don't add dirty flag */);
            return Ok(CompleteWriteBack::Retry);
        }

        // Success - complete eviction
        self.page_table.remove(&page_id);
        self.frame_metadata[frame_id] = FrameMetadata::vacant();
        Ok(CompleteWriteBack::ReadRequired(frame_id))
    }

    /// Increments pin count for a frame and notifies the replacer if needed.
    fn pin_frame(&mut self, frame_id: FrameId) {
        let meta = &mut self.frame_metadata[frame_id];

        meta.pin_count += 1;
        if meta.pin_count == 1 {
            self.replacer.pin(frame_id);
        }
    }

    /// Decrements pin count for a frame and notifies the replacer if needed.
    ///
    /// If `is_dirty` is true, the frame is marked as dirty.
    fn unpin_frame(&mut self, frame_id: FrameId, is_dirty: bool) {
        let meta = &mut self.frame_metadata[frame_id];
        debug_assert!(meta.pin_count > 0, "unpin called on unpinned frame");

        if is_dirty {
            meta.is_dirty = true;
        }
        meta.pin_count -= 1;
        if meta.pin_count == 0 {
            self.replacer.unpin(frame_id);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::LruReplacer;
    use super::*;
    use crate::storage::{MemoryStorage, StorageError, PAGE_SIZE};

    #[tokio::test]
    async fn test_new_buffer_pool() {
        let storage = MemoryStorage::new();
        let replacer = LruReplacer::new(10);
        let bpm = BufferPool::new(storage, replacer, 10);

        assert_eq!(bpm.pool_size(), 10);
        assert_eq!(bpm.page_count(), 0);
    }

    #[tokio::test]
    async fn test_new_page() {
        let storage = MemoryStorage::new();
        let replacer = LruReplacer::new(10);
        let bpm = BufferPool::new(storage, replacer, 10);

        let guard = bpm.new_page().await.unwrap();
        let page_id = guard.page_id();

        assert_eq!(page_id, PageId::new(0));
        assert_eq!(guard.data().len(), PAGE_SIZE);

        drop(guard);
        assert_eq!(bpm.page_count(), 1);
    }

    #[tokio::test]
    async fn test_fetch_page() {
        let storage = MemoryStorage::new();
        let page_id = storage.allocate_page().await.unwrap();

        let replacer = LruReplacer::new(10);
        let bpm = BufferPool::new(storage, replacer, 10);

        let guard = bpm.fetch_page(page_id).await.unwrap();
        assert_eq!(guard.page_id(), page_id);
        assert_eq!(guard.data().len(), PAGE_SIZE);
    }

    #[tokio::test]
    async fn test_fetch_same_page_twice() {
        let storage = MemoryStorage::new();
        let page_id = storage.allocate_page().await.unwrap();

        let replacer = LruReplacer::new(10);
        let bpm = BufferPool::new(storage, replacer, 10);

        // Fetch once
        let guard1 = bpm.fetch_page(page_id).await.unwrap();
        drop(guard1);

        // Fetch again - should hit buffer pool
        let guard2 = bpm.fetch_page(page_id).await.unwrap();
        assert_eq!(guard2.page_id(), page_id);

        assert_eq!(bpm.page_count(), 1);
    }

    #[tokio::test]
    async fn test_dirty_page_write_back() {
        let storage = MemoryStorage::new();
        let replacer = LruReplacer::new(10);
        let bpm = BufferPool::new(storage, replacer, 10);

        // Create and modify page
        let page_id;
        {
            let mut guard = bpm.new_page().await.unwrap();
            page_id = guard.page_id();
            guard.data_mut()[0] = 42;
            guard.mark_dirty();
        }

        // Flush to storage
        bpm.flush_page(page_id).await.unwrap();

        // Verify by fetching again
        let guard = bpm.fetch_page(page_id).await.unwrap();
        assert_eq!(guard.data()[0], 42);
    }

    #[tokio::test]
    async fn test_eviction_on_full_pool() {
        let storage = MemoryStorage::new();

        // Allocate more pages than pool size
        for _ in 0..5 {
            storage.allocate_page().await.unwrap();
        }

        // Pool size of 3
        let replacer = LruReplacer::new(3);
        let bpm = BufferPool::new(storage, replacer, 3);

        // Fetch all 5 pages - should trigger evictions
        for i in 0..5 {
            let guard = bpm.fetch_page(PageId::new(i)).await.unwrap();
            drop(guard); // Unpin immediately to allow eviction
        }

        // Should have 3 pages in pool (pool_size)
        assert_eq!(bpm.page_count(), 3);
    }

    #[tokio::test]
    async fn test_no_free_frames_all_pinned() {
        let storage = MemoryStorage::new();

        for _ in 0..3 {
            storage.allocate_page().await.unwrap();
        }

        let replacer = LruReplacer::new(2);
        let bpm = BufferPool::new(storage, replacer, 2);

        // Pin 2 pages (filling the pool)
        let _guard1 = bpm.fetch_page(PageId::new(0)).await.unwrap();
        let _guard2 = bpm.fetch_page(PageId::new(1)).await.unwrap();

        // Try to fetch a third - should fail
        let result = bpm.fetch_page(PageId::new(2)).await;
        assert!(matches!(result, Err(BufferPoolError::NoFreeFrames)));
    }

    #[tokio::test]
    async fn test_dirty_eviction_writes_back() {
        let storage = MemoryStorage::new();

        for _ in 0..3 {
            storage.allocate_page().await.unwrap();
        }

        let replacer = LruReplacer::new(2);
        let bpm = BufferPool::new(storage, replacer, 2);

        // Write to page 0
        {
            let mut guard = bpm.fetch_page_mut(PageId::new(0)).await.unwrap();
            guard.data_mut()[0] = 99;
            guard.mark_dirty();
        }

        // Fetch pages 1 and 2, forcing eviction of page 0
        {
            let _g1 = bpm.fetch_page(PageId::new(1)).await.unwrap();
        }
        {
            let _g2 = bpm.fetch_page(PageId::new(2)).await.unwrap();
        }

        // Page 0 should have been written back, fetch it again
        let guard = bpm.fetch_page(PageId::new(0)).await.unwrap();
        assert_eq!(guard.data()[0], 99);
    }

    #[tokio::test]
    async fn test_flush_all() {
        let storage = MemoryStorage::new();
        let replacer = LruReplacer::new(10);
        let bpm = BufferPool::new(storage, replacer, 10);

        // Create and modify multiple pages
        for i in 0..3 {
            let mut guard = bpm.new_page().await.unwrap();
            guard.data_mut()[0] = i as u8;
            guard.mark_dirty();
        }

        // Flush all
        bpm.flush_all().await.unwrap();

        // Verify all pages
        for i in 0..3 {
            let guard = bpm.fetch_page(PageId::new(i)).await.unwrap();
            assert_eq!(guard.data()[0], i as u8);
        }
    }

    #[tokio::test]
    async fn test_multiple_readers() {
        let storage = MemoryStorage::new();
        storage.allocate_page().await.unwrap();

        let replacer = LruReplacer::new(10);
        let bpm = BufferPool::new(storage, replacer, 10);

        // Multiple read guards should be allowed
        let guard1 = bpm.fetch_page(PageId::new(0)).await.unwrap();
        let guard2 = bpm.fetch_page(PageId::new(0)).await.unwrap();

        assert_eq!(guard1.page_id(), guard2.page_id());
    }

    #[tokio::test]
    async fn test_flush_page_not_in_pool() {
        let storage = MemoryStorage::new();
        let page_id = storage.allocate_page().await.unwrap();

        let replacer = LruReplacer::new(10);
        let bpm = BufferPool::new(storage, replacer, 10);

        // Flushing a page not in the buffer pool should succeed silently
        let result = bpm.flush_page(page_id).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_flush_page_clean() {
        let storage = MemoryStorage::new();
        let replacer = LruReplacer::new(10);
        let bpm = BufferPool::new(storage, replacer, 10);

        // Create a page but don't mark it dirty
        let page_id;
        {
            let guard = bpm.new_page().await.unwrap();
            page_id = guard.page_id();
            // Not calling mark_dirty()
        }

        // Flushing a clean page should succeed without writing
        let result = bpm.flush_page(page_id).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_fetch_page_not_allocated() {
        let storage = MemoryStorage::new();
        let replacer = LruReplacer::new(10);
        let bpm = BufferPool::new(storage, replacer, 10);

        // Fetching a non-existent page should return an error
        let result = bpm.fetch_page(PageId::new(999)).await;
        assert!(matches!(
            result,
            Err(BufferPoolError::Storage(StorageError::PageNotFound(_)))
        ));
    }

    #[tokio::test]
    async fn test_write_and_read_back() {
        let storage = MemoryStorage::new();
        let replacer = LruReplacer::new(10);
        let bpm = BufferPool::new(storage, replacer, 10);

        let page_id;
        {
            let mut guard = bpm.new_page().await.unwrap();
            page_id = guard.page_id();
            // Write a pattern
            for (i, byte) in guard.data_mut().iter_mut().enumerate() {
                *byte = (i % 256) as u8;
            }
            guard.mark_dirty();
        }

        // Read back and verify
        let guard = bpm.fetch_page(page_id).await.unwrap();
        for (i, byte) in guard.data().iter().enumerate() {
            assert_eq!(*byte, (i % 256) as u8);
        }
    }

    #[tokio::test]
    async fn test_multiple_writes_same_page() {
        let storage = MemoryStorage::new();
        let replacer = LruReplacer::new(10);
        let bpm = BufferPool::new(storage, replacer, 10);

        let page_id;
        {
            let mut guard = bpm.new_page().await.unwrap();
            page_id = guard.page_id();
            guard.data_mut()[0] = 1;
            guard.mark_dirty();
        }

        // Write again
        {
            let mut guard = bpm.fetch_page_mut(page_id).await.unwrap();
            assert_eq!(guard.data()[0], 1);
            guard.data_mut()[0] = 2;
            guard.mark_dirty();
        }

        // Verify
        let guard = bpm.fetch_page(page_id).await.unwrap();
        assert_eq!(guard.data()[0], 2);
    }

    #[tokio::test]
    async fn test_eviction_lru_order() {
        let storage = MemoryStorage::new();

        // Allocate 4 pages
        for _ in 0..4 {
            storage.allocate_page().await.unwrap();
        }

        // Pool size of 3
        let replacer = LruReplacer::new(3);
        let bpm = BufferPool::new(storage, replacer, 3);

        // Fetch pages 0, 1, 2 (fills the pool)
        for i in 0..3 {
            let _g = bpm.fetch_page(PageId::new(i)).await.unwrap();
        }
        assert_eq!(bpm.page_count(), 3);

        // Access page 0 again to make it most recently used
        {
            let _g = bpm.fetch_page(PageId::new(0)).await.unwrap();
        }

        // Fetch page 3 - should evict page 1 (LRU)
        {
            let _g = bpm.fetch_page(PageId::new(3)).await.unwrap();
        }

        // Page 1 should be evicted, pages 0, 2, 3 should remain
        // Verify by fetching page 0 (cache hit - still in pool)
        let guard = bpm.fetch_page(PageId::new(0)).await.unwrap();
        assert_eq!(guard.page_id(), PageId::new(0));
    }

    #[tokio::test]
    async fn test_concurrent_fetch_same_page() {
        use std::sync::Arc;

        let storage = MemoryStorage::new();
        let page_id = storage.allocate_page().await.unwrap();

        let replacer = LruReplacer::new(10);
        let bpm = Arc::new(BufferPool::new(storage, replacer, 10));

        // Spawn multiple tasks fetching the same page concurrently
        let mut handles = vec![];
        for _ in 0..10 {
            let bpm = Arc::clone(&bpm);
            handles.push(tokio::spawn(async move {
                let guard = bpm.fetch_page(page_id).await.unwrap();
                assert_eq!(guard.page_id(), page_id);
            }));
        }

        for handle in handles {
            handle.await.unwrap();
        }

        // Should only have 1 page in pool
        assert_eq!(bpm.page_count(), 1);
    }

    #[tokio::test]
    async fn test_concurrent_fetch_different_pages() {
        use std::sync::Arc;

        let storage = MemoryStorage::new();
        for _ in 0..5 {
            storage.allocate_page().await.unwrap();
        }

        let replacer = LruReplacer::new(10);
        let bpm = Arc::new(BufferPool::new(storage, replacer, 10));

        // Spawn tasks fetching different pages concurrently
        let mut handles = vec![];
        for i in 0..5 {
            let bpm = Arc::clone(&bpm);
            handles.push(tokio::spawn(async move {
                let guard = bpm.fetch_page(PageId::new(i)).await.unwrap();
                assert_eq!(guard.page_id(), PageId::new(i));
            }));
        }

        for handle in handles {
            handle.await.unwrap();
        }

        assert_eq!(bpm.page_count(), 5);
    }

    #[tokio::test]
    async fn test_pin_prevents_eviction() {
        let storage = MemoryStorage::new();

        for _ in 0..3 {
            storage.allocate_page().await.unwrap();
        }

        let replacer = LruReplacer::new(2);
        let bpm = BufferPool::new(storage, replacer, 2);

        // Pin page 0
        let _guard0 = bpm.fetch_page(PageId::new(0)).await.unwrap();

        // Fetch page 1 (fills pool)
        {
            let _g = bpm.fetch_page(PageId::new(1)).await.unwrap();
        }

        // Fetch page 2 - should evict page 1 (page 0 is pinned)
        {
            let _g = bpm.fetch_page(PageId::new(2)).await.unwrap();
        }

        // Page 0 should still be valid
        assert_eq!(_guard0.page_id(), PageId::new(0));
    }

    #[tokio::test]
    async fn test_deref_traits() {
        let storage = MemoryStorage::new();
        let replacer = LruReplacer::new(10);
        let bpm = BufferPool::new(storage, replacer, 10);

        // Test Deref for PageWriteGuard
        {
            let mut guard = bpm.new_page().await.unwrap();
            guard[0] = 42; // Uses DerefMut
            guard.mark_dirty();
        }

        // Test Deref for PageReadGuard
        let guard = bpm.fetch_page(PageId::new(0)).await.unwrap();
        assert_eq!(guard[0], 42); // Uses Deref
    }
}
