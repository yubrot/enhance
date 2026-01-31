//! Buffer pool manager for caching pages in memory.
//!
//! The buffer pool manager sits between the storage layer and higher-level
//! components, caching frequently accessed pages in memory to reduce I/O.

use std::collections::HashMap;

use parking_lot::Mutex;
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
///
/// # Cancel Safety
///
/// **This implementation is NOT cancel-safe.**
///
/// If a Future returned by buffer pool methods (e.g., `fetch_page`, `flush_page`)
/// is dropped before completion, internal state may become inconsistent:
///
/// - **Frame leaks**: Pin counts may not be decremented, causing frames to remain
///   pinned indefinitely. This prevents those frames from being evicted, effectively
///   reducing the buffer pool capacity.
///
/// - **Inconsistent metadata**: The page table, frame metadata, or replacer state
///   may become out of sync with actual frame usage.
///
/// To avoid these issues:
/// - Always await buffer pool operations to completion or handle errors properly
/// - Do not use timeout operations (e.g., `tokio::time::timeout`) that may cancel
///   buffer pool operations
/// - Ensure that drop/cleanup code completes before task cancellation
///
/// This limitation exists because correct cancel safety would require significant
/// complexity (e.g., async drop, rollback mechanisms, or guard-based RAII that
/// works across await points).
pub struct BufferPool<S: Storage, R: Replacer> {
    inner: BufferPoolInner<S, R>,
}

// # Latch Ordering
//
// To prevent deadlocks, the following invariant must be maintained:
//
// **NEVER acquire a frame data lock while holding the state lock.**
//
// The reverse (acquiring state lock while holding frame lock) is permitted
// and necessary for:
// - Drop implementations (unpin while holding data lock)
// - Flush operations (clear dirty flag atomically with write)
//
// This ordering prevents circular wait: all code paths that acquire both
// locks do so in frame → state order, never state → frame.
//
// When acquiring multiple frame locks, acquire in ascending PageId order.
//
// # Data-PageId Consistency Invariants
//
// **Invariant 1: page_table and frame_metadata are always synchronized.**
//
// - If `page_table[page_id] == frame_id`, then `frame_metadata[frame_id].page_id == Some(page_id)`
// - If `frame_metadata[frame_id].page_id == Some(page_id)`, then `page_table[page_id] == frame_id`
//
// This holds because the code always updates both simultaneously:
// - `complete_read` sets both page_table entry and frame_metadata.page_id together
// - Eviction (`acquire_frame`, `complete_write_back`) clears both together
//
// **Invariant 2: When the mapping exists, frame data matches the page.**
//
// When `page_table[page_id] == frame_id` (equivalently, `frame_metadata[frame_id].page_id == Some(page_id)`),
// the data in `frames[frame_id]` is guaranteed to be that page's data.
//
// This holds because `complete_read` only establishes the mapping AFTER acquiring
// the frame's write lock and completing the storage read.
//
// Consequently, while holding a frame's read or write lock:
// - The frame's data cannot change (write lock is required for modification)
// - `frame_metadata[frame_id].page_id` may become None due to concurrent eviction
//   (state lock and frame lock are independent)
// - However, page_id cannot change to a DIFFERENT page (loading new data requires
//   write lock, which we hold or block)
//
// NOTE: For production, consider these improvements:
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
    /// Uses `parking_lot::Mutex` to allow synchronous access from `Drop`.
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

    /// Returns the number of frames in the buffer pool.
    pub fn pool_size(&self) -> usize {
        self.inner.frames.len()
    }

    /// Returns the total number of pages in storage.
    ///
    /// This queries the underlying storage to get the count of allocated pages.
    pub async fn page_count(&self) -> usize {
        self.inner.storage.page_count().await
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
    pub async fn flush_page(&self, page_id: PageId) -> Result<(), StorageError> {
        let frame_id = {
            let state = self.inner.state.lock();
            match state.page_table.get(&page_id) {
                Some(&fid) if state.frame_metadata[fid].is_dirty => fid,
                _ => return Ok(()),
            }
        };

        self.inner.flush(frame_id, page_id).await
    }

    /// Flushes all dirty pages to storage.
    ///
    /// # Errors
    ///
    /// Returns `BufferPoolError::Storage` if any write fails.
    pub async fn flush_all(&self) -> Result<(), BufferPoolError> {
        let dirty_pages: Vec<(FrameId, PageId)> = {
            let state = self.inner.state.lock();
            state
                .frame_metadata
                .iter()
                .enumerate()
                .filter(|(_, meta)| meta.is_dirty)
                .filter_map(|(frame_id, meta)| meta.page_id.map(|page_id| (frame_id, page_id)))
                .collect()
        };

        for (frame_id, page_id) in dirty_pages {
            self.inner.flush(frame_id, page_id).await?;
        }

        self.inner.storage.sync_all().await?;

        Ok(())
    }

    /// Returns a reference to the underlying storage.
    ///
    /// This is primarily used for operations that need direct storage access,
    /// such as fsync for critical metadata (e.g., superblock).
    pub fn storage(&self) -> &S {
        &self.inner.storage
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
            let action = {
                let mut state = self.state.lock();
                state.acquire_frame(page_id)
            };
            match action {
                AcquireFrame::Ready(frame_id) => return Ok(frame_id),
                AcquireFrame::ReadRequired(frame_id) => break frame_id,
                AcquireFrame::WriteBackRequired(frame_id, evicted_page_id) => {
                    let write_result = {
                        let data = self.frames[frame_id].read().await;
                        self.storage
                            .write_page(evicted_page_id, data.as_slice())
                            .await
                    };

                    let mut state = self.state.lock();
                    match state.complete_write_back(frame_id, evicted_page_id, write_result)? {
                        CompleteWriteBack::ReadRequired(frame_id) => break frame_id,
                        CompleteWriteBack::Retry => {}
                    }
                }
                AcquireFrame::Full => return Err(BufferPoolError::NoFreeFrames),
            }
            // FIXME: Potential busy loop if write back keeps failing
            tokio::task::yield_now().await;
        };

        let read_result = {
            let mut data = self.frames[new_frame_id].write().await;
            self.storage.read_page(page_id, data.as_mut_slice()).await
        };

        let mut state = self.state.lock();
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
        let mut state = self.state.lock();
        state.unpin_frame(frame_id, is_dirty);
    }

    /// Flushes a frame to storage if it still holds the expected page.
    async fn flush(&self, frame_id: FrameId, page_id: PageId) -> Result<(), StorageError> {
        let data_guard = self.frames[frame_id].read().await;

        // By the Data-PageId Consistency Invariant (see module-level comment),
        // if page_id matches while we hold read lock, data is guaranteed valid.
        {
            let state = self.state.lock();
            if state.frame_metadata[frame_id].page_id != Some(page_id) {
                return Ok(());
            }
        }

        self.storage
            .write_page(page_id, data_guard.as_slice())
            .await?;

        let mut state = self.state.lock();
        if state.frame_metadata[frame_id].page_id == Some(page_id) {
            state.frame_metadata[frame_id].is_dirty = false;
        }

        Ok(())
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

        let Some(evicted_page_id) = self.frame_metadata[frame_id].page_id else {
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
            return AcquireFrame::WriteBackRequired(frame_id, evicted_page_id);
        }

        self.page_table.remove(&evicted_page_id);
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
            // Read failed: return to free_list
            // NOTE: We may remove read_result argument when resolving cancel safety issues
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
            // NOTE: We may remove write_result argument when resolving cancel safety issues
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
    use std::sync::Arc;

    use super::super::LruReplacer;
    use super::*;
    use crate::storage::{MemoryStorage, PAGE_SIZE, StorageError};

    /// Helper function to create a buffer pool with pre-allocated pages.
    async fn create_pool(
        pool_size: usize,
        allocated_pages: usize,
    ) -> BufferPool<MemoryStorage, LruReplacer> {
        let storage = MemoryStorage::new();
        for _ in 0..allocated_pages {
            storage.allocate_page().await.unwrap();
        }
        let replacer = LruReplacer::new(pool_size);
        BufferPool::new(storage, replacer, pool_size)
    }

    /// Helper function to read a page directly from storage.
    async fn storage_data(
        pool: &BufferPool<MemoryStorage, LruReplacer>,
        page_id: PageId,
    ) -> Vec<u8> {
        let mut data = vec![0u8; PAGE_SIZE];
        pool.storage().read_page(page_id, &mut data).await.unwrap();
        data
    }

    #[tokio::test]
    async fn test_new_buffer_pool() {
        let pool = create_pool(10, 0).await;
        assert_eq!(pool.pool_size(), 10);
    }

    #[tokio::test]
    async fn test_new_page() {
        let pool = create_pool(10, 0).await;
        let guard = pool.new_page().await.unwrap();
        let page_id = guard.page_id();

        assert_eq!(page_id, PageId::new(0));
        assert_eq!(guard.data().len(), PAGE_SIZE);
    }

    #[tokio::test]
    async fn test_fetch_page() {
        let pool = create_pool(10, 1).await;
        let page_id = PageId::new(0);

        let guard = pool.fetch_page(page_id).await.unwrap();
        assert_eq!(guard.page_id(), page_id);
        assert_eq!(guard.data().len(), PAGE_SIZE);
    }

    #[tokio::test]
    async fn test_fetch_same_page_twice() {
        let pool = create_pool(10, 1).await;
        let page_id = PageId::new(0);

        // Fetch once
        {
            let _guard1 = pool.fetch_page(page_id).await.unwrap();
        }

        // Fetch again - should hit buffer pool
        let guard2 = pool.fetch_page(page_id).await.unwrap();
        assert_eq!(guard2.page_id(), page_id);
    }

    #[tokio::test]
    async fn test_fetch_same_page_write_and_read() {
        let pool = create_pool(10, 1).await;
        let page_id = PageId::new(0);

        // Fetch once
        {
            let mut guard1 = pool.fetch_page_mut(page_id).await.unwrap();
            guard1[0] = 111;
            guard1.mark_dirty();
        }

        // Fetch again - should hit buffer pool
        let guard2 = pool.fetch_page(page_id).await.unwrap();
        assert_eq!(guard2.page_id(), page_id);
        assert_eq!(guard2[0], 111);
    }

    #[tokio::test]
    async fn test_dirty_page_flush() {
        let pool = create_pool(10, 1).await;
        let page_id = PageId::new(0);

        // Create and modify page
        {
            let mut guard = pool.fetch_page_mut(page_id).await.unwrap();
            guard.data_mut()[0] = 42;
            guard.mark_dirty();
        }

        // Flush to storage
        pool.flush_page(page_id).await.unwrap();

        // Verify by reading from storage directly
        let data = storage_data(&pool, page_id).await;
        assert_eq!(data[0], 42);
    }

    #[tokio::test]
    async fn test_write_and_read_pages() {
        let pool = create_pool(3, 5).await;

        for i in 0..5 {
            let mut guard = pool.fetch_page_mut(PageId::new(i)).await.unwrap();
            guard[0] = (i * 10) as u8;
            guard.mark_dirty();
        }
        for i in 0..5 {
            let guard = pool.fetch_page(PageId::new(i)).await.unwrap();
            assert_eq!(guard[0], (i * 10) as u8);
        }
    }

    #[tokio::test]
    async fn test_dirty_eviction_writes_back() {
        let pool = create_pool(2, 3).await;

        // Write to page 0
        {
            let mut guard = pool.fetch_page_mut(PageId::new(0)).await.unwrap();
            guard.data_mut()[0] = 99;
            guard.mark_dirty();
        }

        // Write to page 1
        {
            let mut guard = pool.fetch_page_mut(PageId::new(1)).await.unwrap();
            guard.data_mut()[0] = 88;
            guard.mark_dirty();
        }

        // Write to page 2, forcing eviction of page 0
        {
            let mut guard = pool.fetch_page_mut(PageId::new(2)).await.unwrap();
            guard.data_mut()[0] = 77;
            guard.mark_dirty();
        }

        // Pages 0 should have been written back to storage by eviction
        let data0 = storage_data(&pool, PageId::new(0)).await;
        assert_eq!(data0[0], 99);

        // Page 1 and Page 2 will be written back by explicit flush
        let data1 = storage_data(&pool, PageId::new(1)).await;
        assert_eq!(data1[0], 0);
        let data2 = storage_data(&pool, PageId::new(2)).await;
        assert_eq!(data2[0], 0);

        pool.flush_page(PageId::new(1)).await.unwrap();
        let data1 = storage_data(&pool, PageId::new(1)).await;
        assert_eq!(data1[0], 88);
        let data2 = storage_data(&pool, PageId::new(2)).await;
        assert_eq!(data2[0], 0);
    }

    #[tokio::test]
    async fn test_no_free_frames_all_pinned() {
        let pool = create_pool(2, 3).await;

        // Pin 2 pages (filling the pool)
        let _guard1 = pool.fetch_page(PageId::new(0)).await.unwrap();
        let _guard2 = pool.fetch_page(PageId::new(1)).await.unwrap();

        // Try to fetch a third - should fail
        let result = pool.fetch_page(PageId::new(2)).await;
        assert!(matches!(result, Err(BufferPoolError::NoFreeFrames)));
    }

    #[tokio::test]
    async fn test_flush_all() {
        let pool = create_pool(10, 0).await;

        // Create and modify multiple pages
        for i in 0..3 {
            let mut guard = pool.new_page().await.unwrap();
            guard.data_mut()[0] = i as u8;
            guard.mark_dirty();
        }

        // Flush all
        pool.flush_all().await.unwrap();

        // Verify all pages by reading from storage directly
        for i in 0..3 {
            let data = storage_data(&pool, PageId::new(i)).await;
            assert_eq!(data[0], i as u8);
        }
    }

    #[tokio::test]
    async fn test_flush_page_not_in_pool() {
        let pool = create_pool(10, 1).await;
        let page_id = PageId::new(0);

        // Flushing a page not in the buffer pool should succeed silently
        let result = pool.flush_page(page_id).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_flush_page_clean() {
        let pool = create_pool(10, 0).await;

        // Create a page but don't mark it dirty
        let page_id;
        {
            let guard = pool.new_page().await.unwrap();
            page_id = guard.page_id();
            // Not calling mark_dirty()
        }

        // Flushing a clean page should succeed without writing
        let result = pool.flush_page(page_id).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_multiple_readers() {
        let pool = create_pool(10, 1).await;

        // Multiple read guards should be allowed
        let guard1 = pool.fetch_page(PageId::new(0)).await.unwrap();
        let guard2 = pool.fetch_page(PageId::new(0)).await.unwrap();

        assert_eq!(guard1.page_id(), guard2.page_id());
    }

    #[tokio::test]
    async fn test_fetch_page_not_allocated() {
        let pool = create_pool(10, 0).await;

        // Fetching a non-existent page should return an error
        let result = pool.fetch_page(PageId::new(999)).await;
        assert!(matches!(
            result,
            Err(BufferPoolError::Storage(StorageError::PageNotFound(_)))
        ));
    }

    #[tokio::test]
    async fn test_multiple_writes_same_page() {
        let pool = create_pool(10, 0).await;

        let page_id;
        {
            let mut guard = pool.new_page().await.unwrap();
            page_id = guard.page_id();
            guard.data_mut()[0] = 1;
            guard.mark_dirty();
        }

        // Write again
        {
            let mut guard = pool.fetch_page_mut(page_id).await.unwrap();
            assert_eq!(guard.data()[0], 1);
            guard.data_mut()[1] = 2;
            guard.mark_dirty();
        }

        // Verify
        let guard = pool.fetch_page(page_id).await.unwrap();
        assert_eq!(guard.data()[0], 1);
        assert_eq!(guard.data()[1], 2);
    }

    #[tokio::test]
    async fn test_concurrent_fetch_same_page() {
        use std::sync::Arc;

        let pool = Arc::new(create_pool(10, 1).await);
        let page_id = PageId::new(0);

        // Spawn multiple tasks fetching the same page concurrently
        let mut handles = vec![];
        for _ in 0..10 {
            let pool = Arc::clone(&pool);
            handles.push(tokio::spawn(async move {
                let guard = pool.fetch_page(page_id).await.unwrap();
                assert_eq!(guard.page_id(), page_id);
            }));
        }

        for handle in handles {
            handle.await.unwrap();
        }
    }

    #[tokio::test]
    async fn test_concurrent_fetch_different_pages() {
        use std::sync::Arc;

        let pool = Arc::new(create_pool(10, 5).await);

        // Spawn tasks fetching different pages concurrently
        let mut handles = vec![];
        for i in 0..5 {
            let pool = Arc::clone(&pool);
            handles.push(tokio::spawn(async move {
                let guard = pool.fetch_page(PageId::new(i)).await.unwrap();
                assert_eq!(guard.page_id(), PageId::new(i));
            }));
        }

        for handle in handles {
            handle.await.unwrap();
        }
    }

    #[tokio::test]
    async fn test_pin_prevents_eviction() {
        let pool = create_pool(2, 3).await;

        // Pin page 0
        let _guard0 = pool.fetch_page(PageId::new(0)).await.unwrap();

        // Fetch page 1 (fills pool)
        {
            let _g = pool.fetch_page(PageId::new(1)).await.unwrap();
        }

        // Fetch page 2 - should evict page 1 (page 0 is pinned)
        {
            let _g = pool.fetch_page(PageId::new(2)).await.unwrap();
        }

        // Page 0 should still be valid
        assert_eq!(_guard0.page_id(), PageId::new(0));
    }

    /// Storage wrapper that adds synchronization points for testing race conditions.
    struct SyncableStorage {
        inner: MemoryStorage,
        read_barrier: Option<Arc<tokio::sync::Barrier>>,
        write_started: Option<Arc<tokio::sync::Notify>>,
        write_barrier: Option<Arc<tokio::sync::Barrier>>,
    }

    impl SyncableStorage {
        fn new(inner: MemoryStorage) -> Self {
            Self {
                inner,
                read_barrier: None,
                write_started: None,
                write_barrier: None,
            }
        }

        fn with_read_barrier(mut self, barrier: Arc<tokio::sync::Barrier>) -> Self {
            self.read_barrier = Some(barrier);
            self
        }

        fn with_write_sync(
            mut self,
            started: Arc<tokio::sync::Notify>,
            barrier: Arc<tokio::sync::Barrier>,
        ) -> Self {
            self.write_started = Some(started);
            self.write_barrier = Some(barrier);
            self
        }
    }

    impl Storage for SyncableStorage {
        async fn read_page(&self, page_id: PageId, buf: &mut [u8]) -> Result<(), StorageError> {
            let result = self.inner.read_page(page_id, buf).await;
            if let Some(barrier) = &self.read_barrier {
                barrier.wait().await;
            }
            result
        }

        async fn write_page(&self, page_id: PageId, buf: &[u8]) -> Result<(), StorageError> {
            if let Some(notify) = &self.write_started {
                notify.notify_one();
            }
            let result = self.inner.write_page(page_id, buf).await;
            if let Some(barrier) = &self.write_barrier {
                barrier.wait().await;
            }
            result
        }

        async fn allocate_page(&self) -> Result<PageId, StorageError> {
            self.inner.allocate_page().await
        }

        async fn page_count(&self) -> usize {
            self.inner.page_count().await
        }

        async fn sync_all(&self) -> Result<(), StorageError> {
            self.inner.sync_all().await
        }
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn test_complete_read_race() {
        // Barrier(2): Both tasks synchronize after read completes
        let barrier = Arc::new(tokio::sync::Barrier::new(2));

        let inner = MemoryStorage::new();
        let page = inner.allocate_page().await.unwrap();
        let storage = SyncableStorage::new(inner).with_read_barrier(barrier);
        let pool = Arc::new(BufferPool::new(storage, LruReplacer::new(2), 2));

        let t1 = tokio::spawn({
            let pool = pool.clone();
            async move {
                let guard = pool.fetch_page(page).await.unwrap();
                guard.page_id()
            }
        });
        let t2 = tokio::spawn({
            let pool = pool.clone();
            async move {
                let guard = pool.fetch_page(page).await.unwrap();
                guard.page_id()
            }
        });

        let (r1, r2) = tokio::join!(t1, t2);
        assert_eq!(r1.unwrap(), page);
        assert_eq!(r2.unwrap(), page);
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn test_write_back_during_pin() {
        // write_started: notified when write_page begins
        // barrier: synchronize write_back completion with main thread
        let write_started = Arc::new(tokio::sync::Notify::new());
        let barrier = Arc::new(tokio::sync::Barrier::new(2));

        let inner = MemoryStorage::new();
        let page_0 = inner.allocate_page().await.unwrap();
        let page_1 = inner.allocate_page().await.unwrap();
        let storage =
            SyncableStorage::new(inner).with_write_sync(write_started.clone(), barrier.clone());
        let pool = Arc::new(BufferPool::new(storage, LruReplacer::new(1), 1));

        // Make page_0 dirty
        {
            let mut guard = pool.fetch_page_mut(page_0).await.unwrap();
            guard[0] = 42;
            guard.mark_dirty();
        }

        // Fetch page_1 → eviction starts, write_back begins
        let t1 = tokio::spawn({
            let pool = pool.clone();
            async move { pool.fetch_page(page_1).await.map(|g| g.page_id()) }
        });

        // Wait for write_back to start
        write_started.notified().await;

        // During write_back, fetch page_0 (pin_count becomes 2)
        // This should succeed because page_0 is still in the buffer (being written back)
        let guard = pool.fetch_page(page_0).await.unwrap();
        assert_eq!(guard[0], 42);

        // Release barrier to complete write_back → pin_count > 1 → Retry
        barrier.wait().await;

        // t1 retries but fails because frame is still pinned
        let r1 = t1.await.unwrap();
        assert!(matches!(r1, Err(BufferPoolError::NoFreeFrames)));
    }

    // NOTE: The `is_dirty` case in `complete_write_back` cannot be tested
    // deterministically with SyncableStorage. This race condition occurs in the narrow
    // window between frame read lock release and state lock acquisition, which cannot
    // be synchronized from within the Storage trait. Testing `is_dirty`  would require stress
    // testing or instrumentation within BufferPool itself.
}
