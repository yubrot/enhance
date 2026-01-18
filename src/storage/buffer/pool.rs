//! Buffer pool manager implementation.

use super::error::BufferPoolError;
use super::frame::{Frame, FrameId};
use super::guard::{PageReadGuard, PageWriteGuard};
use super::replacer::LruReplacer;
use crate::storage::{PageId, Storage};

use std::collections::HashMap;
use std::sync::Mutex;

/// Buffer Pool Manager for caching pages in memory.
///
/// The buffer pool manages a fixed-size collection of frames, each capable
/// of holding one 8KB page. It provides:
///
/// - Page caching with LRU replacement
/// - Concurrent page access via RAII guards
/// - Dirty page tracking and flush-on-eviction
/// - Configurable pool size
///
/// # Architecture
///
/// ```text
/// +---------------------+
/// | BufferPool<S>       |
/// +---------------------+
/// | page_table:         |  PageId -> FrameId mapping
/// | frames: Vec<Frame>  |  Fixed-size frame array
/// | free_list: Vec      |  Unused frame indices
/// | replacer: LruReplacer|  Eviction policy
/// | storage: S          |  Underlying Storage trait
/// +---------------------+
/// ```
///
/// # Latch Hierarchy
///
/// To prevent deadlocks, locks must be acquired in this order:
/// 1. Buffer pool latch (`page_table` mutex)
/// 2. Frame metadata (atomic operations, no lock)
/// 3. Page data latch (frame's RwLock)
/// 4. Storage I/O (Storage trait methods)
///
/// # Example
///
/// ```no_run
/// # use enhance::storage::{BufferPool, MemoryStorage, PageId};
/// # async fn example() {
/// # let storage = MemoryStorage::new();
/// let pool = BufferPool::new(storage, 100); // 100 frames
///
/// # let page_id = pool.new_page().await.unwrap().page_id();
/// // Fetch page for reading
/// let guard = pool.fetch_page_read(page_id).await.unwrap();
/// println!("first byte: {}", guard[0]);
/// # drop(guard);
///
/// // Fetch page for writing
/// let mut guard = pool.fetch_page_write(page_id).await.unwrap();
/// guard[0] = 42;
/// // Automatically marked dirty and unpinned on drop
/// # drop(guard);
///
/// // Flush all dirty pages
/// pool.flush_all().await.unwrap();
/// # }
/// ```
pub struct BufferPool<S: Storage> {
    /// Underlying storage backend.
    storage: S,

    /// Fixed array of frames.
    frames: Vec<Frame>,

    /// Mapping from PageId to FrameId.
    /// Protected by mutex for thread-safe access.
    page_table: Mutex<HashMap<PageId, FrameId>>,

    /// List of free (unused) frame IDs.
    /// Protected by mutex, accessed atomically with page_table.
    free_list: Mutex<Vec<FrameId>>,

    /// LRU replacer for eviction decisions.
    replacer: LruReplacer,
}

impl<S: Storage> BufferPool<S> {
    /// Creates a new buffer pool with the specified number of frames.
    ///
    /// # Arguments
    ///
    /// * `storage` - The underlying storage backend
    /// * `num_frames` - Number of frames (pages) the pool can hold
    ///
    /// # Panics
    ///
    /// Panics if `num_frames` is 0.
    pub fn new(storage: S, num_frames: usize) -> Self {
        assert!(num_frames > 0, "buffer pool must have at least 1 frame");

        let frames: Vec<Frame> = (0..num_frames).map(|_| Frame::new()).collect();
        let free_list: Vec<FrameId> = (0..num_frames as u32)
            .map(FrameId::new)
            .rev() // Reverse so pop() gives us 0, 1, 2, ...
            .collect();

        Self {
            storage,
            frames,
            page_table: Mutex::new(HashMap::new()),
            free_list: Mutex::new(free_list),
            replacer: LruReplacer::new(),
        }
    }

    /// Returns the number of frames in the pool.
    pub fn num_frames(&self) -> usize {
        self.frames.len()
    }

    /// Fetches a page for read-only access.
    ///
    /// If the page is in the buffer pool, returns it immediately.
    /// Otherwise, reads from storage (possibly evicting another page).
    ///
    /// # Errors
    ///
    /// - `BufferPoolError::PageNotFound` if page doesn't exist in storage
    /// - `BufferPoolError::NoFreeFrames` if all frames are pinned
    /// - `BufferPoolError::Storage` for I/O errors
    pub async fn fetch_page_read(
        &self,
        page_id: PageId,
    ) -> Result<PageReadGuard<'_, S>, BufferPoolError> {
        let frame_id = self.fetch_page_internal(page_id).await?;
        let frame = &self.frames[frame_id.index()];

        // Acquire read lock on page data
        let lock = frame.read().await;

        Ok(PageReadGuard::new(self, frame_id, page_id, lock))
    }

    /// Fetches a page for mutable access.
    ///
    /// If the page is in the buffer pool, returns it immediately.
    /// Otherwise, reads from storage (possibly evicting another page).
    ///
    /// The page is automatically marked dirty when the guard is dropped.
    ///
    /// # Errors
    ///
    /// Same as `fetch_page_read`.
    pub async fn fetch_page_write(
        &self,
        page_id: PageId,
    ) -> Result<PageWriteGuard<'_, S>, BufferPoolError> {
        let frame_id = self.fetch_page_internal(page_id).await?;
        let frame = &self.frames[frame_id.index()];

        // Acquire write lock on page data
        let lock = frame.write().await;

        Ok(PageWriteGuard::new(self, frame_id, page_id, lock))
    }

    /// Allocates a new page in storage and fetches it for writing.
    ///
    /// Returns a write guard for the newly allocated page.
    ///
    /// # Errors
    ///
    /// - `BufferPoolError::NoFreeFrames` if all frames are pinned
    /// - `BufferPoolError::Storage` for allocation/I/O errors
    pub async fn new_page(&self) -> Result<PageWriteGuard<'_, S>, BufferPoolError> {
        // Allocate page in storage first
        let page_id = self.storage.allocate_page().await?;

        // Now fetch it into the buffer pool
        self.fetch_page_write(page_id).await
    }

    /// Flushes a specific page to storage if dirty.
    ///
    /// # Errors
    ///
    /// - `BufferPoolError::PageNotFound` if page is not in the buffer pool
    /// - `BufferPoolError::Storage` for I/O errors
    pub async fn flush_page(&self, page_id: PageId) -> Result<(), BufferPoolError> {
        let frame_id = {
            let page_table = self.page_table.lock().unwrap();
            *page_table
                .get(&page_id)
                .ok_or(BufferPoolError::PageNotFound(page_id))?
        };

        self.flush_frame(frame_id).await
    }

    /// Flushes all dirty pages to storage.
    ///
    /// # Errors
    ///
    /// Returns the first I/O error encountered, but attempts to flush
    /// all pages regardless of errors.
    pub async fn flush_all(&self) -> Result<(), BufferPoolError> {
        let frame_ids: Vec<FrameId> = {
            let page_table = self.page_table.lock().unwrap();
            page_table.values().copied().collect()
        };

        let mut first_error: Option<BufferPoolError> = None;
        for frame_id in frame_ids {
            if let Err(e) = self.flush_frame(frame_id).await
                && first_error.is_none()
            {
                first_error = Some(e);
            }
        }

        match first_error {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }

    // ========== Internal Methods ==========

    /// Internal: Fetches a page and returns its frame ID.
    /// Handles page table lookup, eviction, and I/O.
    async fn fetch_page_internal(&self, page_id: PageId) -> Result<FrameId, BufferPoolError> {
        // Fast path: check if page is already in buffer pool
        loop {
            let frame_id = {
                let page_table = self.page_table.lock().unwrap();
                if let Some(&frame_id) = page_table.get(&page_id) {
                    let frame = &self.frames[frame_id.index()];
                    let old_pin = frame.pin_count();
                    frame.pin();

                    // If this frame was unpinned, remove from replacer
                    if old_pin == 0 {
                        self.replacer.pin(frame_id);
                    }

                    Some(frame_id)
                } else {
                    None
                }
            };

            if let Some(frame_id) = frame_id {
                let frame = &self.frames[frame_id.index()];

                // Double-check: verify page_id hasn't changed (防止 race condition)
                if frame.page_id() == Some(page_id) {
                    return Ok(frame_id);
                } else {
                    // Page was evicted concurrently, unpin and retry
                    frame.unpin();
                    if frame.pin_count() == 0 {
                        self.replacer.unpin(frame_id);
                    }
                    continue;
                }
            }

            // Not in pool, break to slow path
            break;
        }

        // Slow path: need to load from storage
        let frame_id = self.get_free_frame().await?;

        // Load page data from storage
        {
            let frame = &self.frames[frame_id.index()];
            let mut data = frame.write().await;
            self.storage
                .read_page(page_id, data.as_mut_slice())
                .await?;
            drop(data);

            frame.set_page_id(Some(page_id));
            frame.clear_dirty();
            frame.pin(); // Initial pin
        }

        // Update page table
        {
            let mut page_table = self.page_table.lock().unwrap();
            page_table.insert(page_id, frame_id);
        }

        Ok(frame_id)
    }

    /// Internal: Gets a free frame (from free list or by eviction).
    async fn get_free_frame(&self) -> Result<FrameId, BufferPoolError> {
        // Try free list first
        {
            let mut free_list = self.free_list.lock().unwrap();
            if let Some(frame_id) = free_list.pop() {
                return Ok(frame_id);
            }
        }

        // Need to evict
        self.evict_frame().await
    }

    /// Internal: Evicts a frame using LRU policy.
    async fn evict_frame(&self) -> Result<FrameId, BufferPoolError> {
        // Loop to handle concurrent pin scenarios
        loop {
            let frame_id = self
                .replacer
                .victim()
                .ok_or(BufferPoolError::NoFreeFrames)?;
            let frame = &self.frames[frame_id.index()];

            // Double-check: verify frame is still unpinned (防止 race condition)
            // Frame could have been pinned between replacer.victim() and here
            if frame.pin_count() > 0 {
                // Frame was pinned concurrently, skip it and try another
                continue;
            }

            // Get the old page ID before clearing
            let old_page_id = frame.page_id();

            // Flush if dirty
            if frame.is_dirty() {
                self.flush_frame(frame_id).await?;
            }

            // Remove from page table
            if let Some(old_id) = old_page_id {
                let mut page_table = self.page_table.lock().unwrap();
                page_table.remove(&old_id);
            }

            // Reset frame state
            frame.set_page_id(None);
            frame.clear_dirty();

            return Ok(frame_id);
        }
    }

    /// Internal: Flushes a frame to storage if dirty.
    async fn flush_frame(&self, frame_id: FrameId) -> Result<(), BufferPoolError> {
        let frame = &self.frames[frame_id.index()];

        if !frame.is_dirty() {
            return Ok(());
        }

        let page_id = frame.page_id().ok_or_else(|| {
            BufferPoolError::InternalError("dirty frame has no page_id".to_string())
        })?;

        // Read lock is sufficient for flushing
        let data = frame.read().await;
        self.storage.write_page(page_id, data.as_slice()).await?;
        drop(data);

        frame.clear_dirty();
        Ok(())
    }

    /// Internal: Called by guard Drop to unpin a frame.
    pub(super) fn unpin_internal(&self, frame_id: FrameId, is_dirty: bool) {
        let frame = &self.frames[frame_id.index()];

        if is_dirty {
            frame.mark_dirty();
        }

        let new_pin = frame.unpin();

        // If pin count reaches 0, add to replacer
        if new_pin == 0 {
            self.replacer.unpin(frame_id);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::MemoryStorage;

    #[tokio::test]
    async fn test_buffer_pool_new() {
        let storage = MemoryStorage::new();
        let pool = BufferPool::new(storage, 10);
        assert_eq!(pool.num_frames(), 10);
    }

    #[test]
    #[should_panic(expected = "buffer pool must have at least 1 frame")]
    fn test_buffer_pool_zero_frames() {
        let storage = MemoryStorage::new();
        let _pool = BufferPool::new(storage, 0);
    }

    #[tokio::test]
    async fn test_new_page() {
        let storage = MemoryStorage::new();
        let pool = BufferPool::new(storage, 10);

        let mut guard = pool.new_page().await.unwrap();
        assert_eq!(guard.page_id(), PageId::new(0));

        guard[0] = 42;
        drop(guard);

        // Read it back
        let guard = pool.fetch_page_read(PageId::new(0)).await.unwrap();
        assert_eq!(guard[0], 42);
    }

    #[tokio::test]
    async fn test_fetch_read_write() {
        let storage = MemoryStorage::new();
        let pool = BufferPool::new(storage, 10);

        let mut guard = pool.new_page().await.unwrap();
        let page_id = guard.page_id();
        guard[0] = 123;
        drop(guard);

        // Fetch for reading
        let guard = pool.fetch_page_read(page_id).await.unwrap();
        assert_eq!(guard[0], 123);
        drop(guard);

        // Fetch for writing
        let mut guard = pool.fetch_page_write(page_id).await.unwrap();
        guard[1] = 45;
        drop(guard);

        // Verify
        let guard = pool.fetch_page_read(page_id).await.unwrap();
        assert_eq!(guard[0], 123);
        assert_eq!(guard[1], 45);
    }

    #[tokio::test]
    async fn test_guard_drop_unpins() {
        let storage = MemoryStorage::new();
        let pool = BufferPool::new(storage, 2);

        let page_id = {
            let guard = pool.new_page().await.unwrap();
            guard.page_id()
        }; // guard dropped, should unpin

        // Should be able to fetch again
        let _guard = pool.fetch_page_read(page_id).await.unwrap();
    }

    #[tokio::test]
    async fn test_eviction_when_pool_full() {
        let storage = MemoryStorage::new();
        let pool = BufferPool::new(storage, 2);

        // Fill the pool
        let page0 = pool.new_page().await.unwrap().page_id();
        let _page1 = pool.new_page().await.unwrap().page_id();

        // Access page 2 (should evict page 0, the oldest)
        let _page2 = pool.new_page().await.unwrap();

        // Page 0 should have been evicted, so fetching it requires re-loading
        // (We can't easily verify this without internal state inspection,
        // but we can verify it doesn't error)
        let _guard = pool.fetch_page_read(page0).await.unwrap();
    }

    #[tokio::test]
    async fn test_eviction_flushes_dirty() {
        let storage = MemoryStorage::new();
        let pool = BufferPool::new(storage, 1);

        // Write to page 0
        let page0 = {
            let mut guard = pool.new_page().await.unwrap();
            guard[0] = 99;
            let pid = guard.page_id();
            drop(guard); // Explicitly drop to ensure unpin
            pid
        };

        // Allocate page 1 (evicts page 0)
        {
            let _page1 = pool.new_page().await.unwrap();
            // page1 guard dropped here
        }

        // Read page 0 back (should have been flushed to storage)
        let guard = pool.fetch_page_read(page0).await.unwrap();
        assert_eq!(guard[0], 99);
    }

    #[tokio::test]
    async fn test_no_eviction_all_pinned() {
        let storage = MemoryStorage::new();
        let pool = BufferPool::new(storage, 2);

        // Pin all frames
        let _guard0 = pool.new_page().await.unwrap();
        let _guard1 = pool.new_page().await.unwrap();

        // Try to allocate another page
        let result = pool.new_page().await;
        assert!(matches!(result, Err(BufferPoolError::NoFreeFrames)));
    }

    #[tokio::test]
    async fn test_flush_page() {
        let storage = MemoryStorage::new();
        let pool = BufferPool::new(storage, 10);

        let page_id = {
            let mut guard = pool.new_page().await.unwrap();
            guard[0] = 77;
            guard.page_id()
        };

        pool.flush_page(page_id).await.unwrap();

        // Dirty flag should be cleared
        // (We can't check this without internal state access)
    }

    #[tokio::test]
    async fn test_flush_all() {
        let storage = MemoryStorage::new();
        let pool = BufferPool::new(storage, 10);

        let _page0 = pool.new_page().await.unwrap();
        let _page1 = pool.new_page().await.unwrap();

        pool.flush_all().await.unwrap();
    }

    #[tokio::test]
    async fn test_concurrent_reads() {
        let storage = MemoryStorage::new();
        let pool = std::sync::Arc::new(BufferPool::new(storage, 10));

        let page_id = pool.new_page().await.unwrap().page_id();

        let pool1 = pool.clone();
        let pool2 = pool.clone();

        let t1 = tokio::spawn(async move {
            let _guard = pool1.fetch_page_read(page_id).await.unwrap();
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        });

        let t2 = tokio::spawn(async move {
            let _guard = pool2.fetch_page_read(page_id).await.unwrap();
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        });

        t1.await.unwrap();
        t2.await.unwrap();
    }
}
