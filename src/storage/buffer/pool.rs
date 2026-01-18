//! Buffer pool manager for caching pages in memory.
//!
//! The buffer pool manager sits between the storage layer and higher-level
//! components, caching frequently accessed pages in memory to reduce I/O.

use std::collections::HashMap;
use std::sync::Mutex;

use crate::storage::{PageId, Storage};

use super::error::BufferPoolError;
use super::frame::{Frame, FrameId, FrameMetadata};
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
/// | BufferPool |  <- You are here
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
///
/// # Latch Hierarchy
///
/// To prevent deadlocks, locks must be acquired in strict order:
/// 1. State mutex (page_table, frame_metadata, free_list, replacer)
/// 2. Frame data RwLock (in PageId order when multiple frames needed)
///
/// **NEVER** acquire the state lock while holding a frame data lock.
///
/// NOTE: For production, consider these improvements:
/// - Use `parking_lot::Mutex` for better performance (no poisoning)
/// - Split state into multiple locks to reduce contention
/// - Add metrics (hit rate, eviction count, dirty page count)
/// - Implement background flusher thread for dirty pages
/// - Support page prefetching for sequential scans
pub struct BufferPool<S: Storage, R: Replacer> {
    inner: BufferPoolInner<S, R>,
}

/// Internal state of the buffer pool manager.
///
/// This struct is exposed to guards for the unpin operation.
pub(super) struct BufferPoolInner<S: Storage, R: Replacer> {
    /// The underlying storage backend.
    storage: S,

    /// Frame array - each frame's data is protected by its own RwLock.
    frames: Vec<Frame>,

    /// Protected mutable state (page table, metadata, free list, replacer).
    ///
    /// Uses `std::sync::Mutex` to allow synchronous access from `Drop`.
    state: Mutex<BufferPoolState<R>>,

    /// Number of frames in the pool.
    pool_size: usize,
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

        // Pre-allocate all frames
        let frames: Vec<_> = (0..pool_size).map(|_| Frame::new()).collect();

        // Pre-allocate all metadata
        let frame_metadata: Vec<_> = (0..pool_size).map(|_| FrameMetadata::new()).collect();

        // All frames start as free
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
                pool_size,
            },
        }
    }

    /// Fetches a page for reading.
    ///
    /// If the page is already in the buffer pool, returns it directly.
    /// Otherwise, reads it from storage into a free or evicted frame.
    ///
    /// The returned guard holds a pin on the page, preventing eviction
    /// until the guard is dropped.
    ///
    /// # Errors
    ///
    /// - `BufferPoolError::NoFreeFrames` if the pool is full and all pages are pinned
    /// - `BufferPoolError::Storage` if the page doesn't exist or I/O fails
    pub async fn fetch_page(
        &self,
        page_id: PageId,
    ) -> Result<PageReadGuard<'_, S, R>, BufferPoolError> {
        let frame_id = self.inner.get_or_allocate_frame(page_id).await?;

        // Acquire read lock on the frame's data
        let data_guard = self.inner.frames[frame_id].data.read().await;

        Ok(PageReadGuard {
            inner: &self.inner,
            frame_id,
            page_id,
            data_guard,
        })
    }

    /// Fetches a page for writing.
    ///
    /// Similar to `fetch_page`, but returns a mutable guard.
    /// The page is NOT automatically marked dirty; call `mark_dirty()`
    /// on the guard after modifications.
    ///
    /// # Errors
    ///
    /// - `BufferPoolError::NoFreeFrames` if the pool is full and all pages are pinned
    /// - `BufferPoolError::Storage` if the page doesn't exist or I/O fails
    pub async fn fetch_page_mut(
        &self,
        page_id: PageId,
    ) -> Result<PageWriteGuard<'_, S, R>, BufferPoolError> {
        let frame_id = self.inner.get_or_allocate_frame(page_id).await?;

        // Acquire write lock on the frame's data
        let data_guard = self.inner.frames[frame_id].data.write().await;

        Ok(PageWriteGuard {
            inner: &self.inner,
            frame_id,
            page_id,
            data_guard,
            is_dirty: false,
        })
    }

    /// Creates a new page in storage and fetches it into the buffer pool.
    ///
    /// The new page is initialized to zeros.
    ///
    /// # Errors
    ///
    /// - `BufferPoolError::NoFreeFrames` if the pool is full and all pages are pinned
    /// - `BufferPoolError::Storage` if storage allocation fails
    pub async fn new_page(&self) -> Result<PageWriteGuard<'_, S, R>, BufferPoolError> {
        // Allocate page in storage first
        let page_id = self.inner.storage.allocate_page().await?;

        // Then fetch it (will use a free/evicted frame)
        self.fetch_page_mut(page_id).await
    }

    /// Flushes a specific page to storage if it's dirty.
    ///
    /// Does nothing if the page is not in the buffer pool or not dirty.
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
            let data_guard = self.inner.frames[frame_id].data.read().await;

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
            let data_guard = self.inner.frames[frame_id].data.read().await;

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
        self.inner.pool_size
    }

    /// Returns the number of pages currently in the buffer pool.
    pub fn page_count(&self) -> usize {
        let state = self.inner.state.lock().expect("state lock poisoned");
        state.page_table.len()
    }
}

impl<S: Storage, R: Replacer> BufferPoolInner<S, R> {
    /// Gets or allocates a frame for a page.
    ///
    /// If the page is already in the buffer pool, increments its pin count.
    /// Otherwise, allocates a free frame or evicts a victim frame.
    ///
    /// # Concurrency Note
    ///
    /// If multiple threads concurrently request the same page that is not in
    /// the buffer pool, both may allocate frames and perform I/O. After I/O
    /// completes, we re-check the page table and discard the redundant frame
    /// if another thread won the race. This is inefficient but correct.
    async fn get_or_allocate_frame(&self, page_id: PageId) -> Result<FrameId, BufferPoolError> {
        // First, check if page is already in buffer pool (fast path)
        {
            let mut state = self.state.lock().expect("state lock poisoned");

            if let Some(&frame_id) = state.page_table.get(&page_id) {
                // Page hit - increment pin count
                state.frame_metadata[frame_id].pin_count += 1;

                // Remove from replacer since it's now pinned
                state.replacer.pin(frame_id);

                return Ok(frame_id);
            }
        }

        // Page miss - need to allocate a frame
        let frame_id = self.allocate_frame().await?;

        // Read page from storage into frame
        let read_result = {
            let mut data_guard = self.frames[frame_id].data.write().await;
            self.storage
                .read_page(page_id, data_guard.as_mut_slice())
                .await
        };

        // Handle read error - return frame to free list to avoid leak
        if let Err(e) = read_result {
            let mut state = self.state.lock().expect("state lock poisoned");
            state.free_list.push(frame_id);
            return Err(e.into());
        }

        // Update state
        {
            let mut state = self.state.lock().expect("state lock poisoned");

            // Check if another thread loaded this page while we were doing I/O
            if let Some(&existing_frame_id) = state.page_table.get(&page_id) {
                // Another thread won the race - discard our frame and use theirs
                state.free_list.push(frame_id);
                state.frame_metadata[existing_frame_id].pin_count += 1;
                state.replacer.pin(existing_frame_id);
                return Ok(existing_frame_id);
            }

            state.page_table.insert(page_id, frame_id);
            state.frame_metadata[frame_id].page_id = Some(page_id);
            state.frame_metadata[frame_id].pin_count = 1;
            state.frame_metadata[frame_id].is_dirty = false;
        }

        Ok(frame_id)
    }

    /// Allocates a free frame, evicting if necessary.
    async fn allocate_frame(&self) -> Result<FrameId, BufferPoolError> {
        // Try to get a free frame first
        {
            let mut state = self.state.lock().expect("state lock poisoned");

            if let Some(frame_id) = state.free_list.pop() {
                return Ok(frame_id);
            }
        }

        // Need to evict - find a victim
        loop {
            let victim = {
                let mut state = self.state.lock().expect("state lock poisoned");
                state.replacer.evict()
            };

            let frame_id = match victim {
                Some(fid) => fid,
                None => return Err(BufferPoolError::NoFreeFrames),
            };

            // Get victim's info and prepare for eviction
            let (old_page_id, is_dirty) = {
                let state = self.state.lock().expect("state lock poisoned");
                let meta = &state.frame_metadata[frame_id];
                (meta.page_id, meta.is_dirty)
            };

            // Write back if dirty
            if let Some(old_page_id) = old_page_id
                && is_dirty
            {
                let data_guard = self.frames[frame_id].data.read().await;
                self.storage
                    .write_page(old_page_id, data_guard.as_slice())
                    .await?;
            }

            // Complete eviction under state lock
            {
                let mut state = self.state.lock().expect("state lock poisoned");

                // Verify the frame wasn't re-pinned while we were doing I/O
                if state.frame_metadata[frame_id].pin_count > 0 {
                    // Frame was re-pinned, try again with another victim
                    continue;
                }

                // Remove from page table
                if let Some(old_page_id) = old_page_id {
                    state.page_table.remove(&old_page_id);
                }

                // Reset frame metadata
                state.frame_metadata[frame_id].reset();

                return Ok(frame_id);
            }
        }
    }

    /// Unpins a frame (called from PageGuard::drop).
    ///
    /// This is a synchronous operation because Drop is synchronous.
    pub(super) fn unpin(&self, frame_id: FrameId, is_dirty: bool) {
        let mut state = self.state.lock().expect("state lock poisoned");

        let meta = &mut state.frame_metadata[frame_id];

        if meta.pin_count > 0 {
            meta.pin_count -= 1;

            if is_dirty {
                meta.is_dirty = true;
            }

            // If unpinned (pin_count == 0), add to replacer
            if meta.pin_count == 0 {
                state.replacer.unpin(frame_id);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::LruReplacer;
    use super::*;
    use crate::storage::{MemoryStorage, PAGE_SIZE};

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
}
