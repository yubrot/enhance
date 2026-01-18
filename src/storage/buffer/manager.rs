//! Buffer Pool Manager implementation.

use super::error::BufferPoolError;
use super::frame::{Frame, FrameId};
use super::guard::{PageReadGuard, PageWriteGuard};
use crate::storage::{PageId, Storage};
use std::collections::HashMap;
use std::sync::RwLock;

/// Configuration for the Buffer Pool Manager.
#[derive(Debug, Clone)]
pub struct BufferPoolConfig {
    /// Number of frames in the buffer pool.
    ///
    /// This determines the maximum number of pages that can be cached in memory
    /// simultaneously. Common values:
    /// - 128 frames = 1MB (for testing)
    /// - 1024 frames = 8MB (small database)
    /// - 131072 frames = 1GB (production)
    pub pool_size: usize,
}

impl Default for BufferPoolConfig {
    fn default() -> Self {
        Self {
            pool_size: 1024, // 1024 * 8KB = 8MB
        }
    }
}

/// The Buffer Pool Manager caches pages in memory and manages page lifecycles.
///
/// # Architecture
///
/// ```text
/// +------------------+     +------------------+
/// | fetch_page()     |---->| Page Table       |
/// | unpin_page()     |     | (PageId->FrameId)|
/// +------------------+     +------------------+
///          |                       |
///          v                       v
/// +------------------+     +------------------+
/// | Free Frame List  |     | Frame Array      |
/// | (Week 7: simple) |     | [Frame; pool_sz] |
/// | (Week 8: LRU)    |     +------------------+
/// +------------------+              |
///                                   v
///                          +------------------+
///                          | Storage Trait    |
///                          +------------------+
/// ```
///
/// # Concurrency Model (Week 7)
///
/// Week 7 uses a global `RwLock` on internal state for simplicity.
/// Multiple readers can access the page table simultaneously, but writes
/// (page loads, unpins with dirty flag) require exclusive access.
///
/// # Week 8 Evolution
///
/// Week 8 will introduce:
/// - Fine-grained page-level latches (`RwLock` per frame)
/// - LRU Replacer for intelligent eviction
/// - Latch Crabbing for B+Tree operations
///
/// # Thread Safety
///
/// The BPM is safe to share across tasks via `Arc<BufferPoolManager>`.
pub struct BufferPoolManager<S: Storage> {
    /// The underlying storage backend.
    storage: S,

    /// Internal state protected by RwLock.
    ///
    /// Uses `std::sync::RwLock` instead of `tokio::sync::RwLock` to allow
    /// synchronous locking in `Drop` implementations.
    ///
    /// WEEK-7 LIMITATION: Storage I/O is currently performed while holding
    /// the lock (see fetch_page, fetch_page_mut, flush_page). This reduces
    /// concurrency but simplifies the implementation. The `#[allow(clippy::await_holding_lock)]`
    /// attributes acknowledge this tradeoff.
    ///
    /// WEEK-8: This will be split into finer-grained locks:
    /// - page_table: RwLock<HashMap<PageId, FrameId>>
    /// - replacer: Arc<Mutex<dyn Replacer>>
    /// - frames: Vec<Arc<RwLock<Frame>>>
    pub(super) inner: RwLock<BufferPoolInner>,

    /// Configuration (immutable after construction).
    config: BufferPoolConfig,
}

/// Internal state of the buffer pool.
pub(super) struct BufferPoolInner {
    /// Frame array. Index is `FrameId`.
    pub(super) frames: Vec<Frame>,

    /// Maps `PageId` to the `FrameId` where it is loaded.
    pub(super) page_table: HashMap<PageId, FrameId>,

    /// List of free (unoccupied) frame IDs.
    ///
    /// WEEK-8: Replace with LRU Replacer.
    /// The Replacer will track unpinned frames and select victims for eviction.
    /// Interface:
    /// - `Replacer::victim() -> Option<FrameId>`: Select a frame to evict
    /// - `Replacer::pin(frame_id)`: Mark frame as non-evictable
    /// - `Replacer::unpin(frame_id)`: Mark frame as evictable
    pub(super) free_list: Vec<FrameId>,
}

impl<S: Storage> BufferPoolManager<S> {
    /// Creates a new Buffer Pool Manager.
    ///
    /// # Arguments
    ///
    /// * `storage` - The underlying storage backend (MemoryStorage or FileStorage)
    /// * `config` - Configuration for the buffer pool
    ///
    /// # Example
    ///
    /// ```no_run
    /// use enhance::storage::{MemoryStorage, BufferPoolManager, BufferPoolConfig};
    ///
    /// let storage = MemoryStorage::new();
    /// let config = BufferPoolConfig::default();
    /// let bpm = BufferPoolManager::new(storage, config);
    /// ```
    pub fn new(storage: S, config: BufferPoolConfig) -> Self {
        let frames = (0..config.pool_size).map(|_| Frame::new()).collect();

        let free_list = (0..config.pool_size).map(FrameId::new).collect();

        Self {
            storage,
            inner: RwLock::new(BufferPoolInner {
                frames,
                page_table: HashMap::new(),
                free_list,
            }),
            config,
        }
    }

    /// Returns the buffer pool configuration.
    pub fn config(&self) -> &BufferPoolConfig {
        &self.config
    }

    /// Returns the number of frames currently in use (occupied).
    pub async fn frame_count(&self) -> usize {
        let inner = self.inner.read().unwrap();
        inner.frames.iter().filter(|f| f.is_occupied()).count()
    }

    /// Fetches a page into the buffer pool and returns a read guard.
    ///
    /// If the page is already in the buffer pool, increments the pin count
    /// and returns immediately. Otherwise, loads the page from storage into
    /// a free frame.
    ///
    /// # Pin Semantics
    ///
    /// The returned guard pins the page in memory. The page will not be
    /// evicted until the guard is dropped (which automatically unpins).
    ///
    /// # Errors
    ///
    /// - `BufferPoolError::PageNotFound` if the page doesn't exist in storage
    /// - `BufferPoolError::NoFreeFrames` if all frames are occupied and pinned (Week 7)
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use enhance::storage::{MemoryStorage, BufferPoolManager, BufferPoolConfig, PageId};
    /// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// # let storage = MemoryStorage::new();
    /// # let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());
    /// let guard = bpm.fetch_page(PageId::new(0)).await?;
    /// let data = guard.as_slice();
    /// // Page is automatically unpinned when guard is dropped
    /// # Ok(())
    /// # }
    /// ```
    #[allow(clippy::await_holding_lock)]
    pub async fn fetch_page(
        &self,
        page_id: PageId,
    ) -> Result<PageReadGuard<'_, S>, BufferPoolError> {
        // WEEK-8: Replace global RwLock with page-level latches.
        // The page_table will have its own RwLock, and each frame will
        // have an RwLock<PageData>. The latch hierarchy will be:
        // 1. Acquire page_table read lock to find frame_id
        // 2. Acquire frame's read lock for data access
        // 3. Release page_table lock
        //
        // For page loads, the sequence will be:
        // 1. Acquire page_table write lock
        // 2. Acquire replacer lock to get victim frame
        // 3. Acquire victim frame's write lock
        // 4. Load page from storage
        // 5. Update page_table
        // 6. Release locks, downgrade to read lock for return

        #[allow(clippy::readonly_write_lock)]
        let mut inner = self.inner.write().unwrap();

        // 1. Check if page is already in the buffer pool
        if let Some(&frame_id) = inner.page_table.get(&page_id) {
            let frame = &mut inner.frames[frame_id.as_usize()];
            frame.pin();
            drop(inner); // Release lock before returning guard
            return Ok(PageReadGuard::new(self, frame_id, page_id));
        }

        // 2. Get a free frame (Week 7: from free_list, Week 8: from LRU Replacer)
        let frame_id = inner.free_list.pop().ok_or(BufferPoolError::NoFreeFrames)?;

        // 3. Load page from storage
        let frame = &mut inner.frames[frame_id.as_usize()];
        self.storage
            .read_page(page_id, frame.data_mut().as_mut_slice())
            .await?;

        // 4. Update frame metadata and page table
        frame.reset(page_id);
        inner.page_table.insert(page_id, frame_id);

        drop(inner);
        Ok(PageReadGuard::new(self, frame_id, page_id))
    }

    /// Fetches a page for modification and returns a write guard.
    ///
    /// Same semantics as `fetch_page`, but the returned guard allows
    /// mutable access and marks the page as dirty on modification.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use enhance::storage::{MemoryStorage, BufferPoolManager, BufferPoolConfig, PageId};
    /// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// # let storage = MemoryStorage::new();
    /// # let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());
    /// let mut guard = bpm.fetch_page_mut(PageId::new(0)).await?;
    /// guard[0] = 42;
    /// // Page is marked dirty and unpinned when guard is dropped
    /// # Ok(())
    /// # }
    /// ```
    #[allow(clippy::await_holding_lock)]
    pub async fn fetch_page_mut(
        &self,
        page_id: PageId,
    ) -> Result<PageWriteGuard<'_, S>, BufferPoolError> {
        #[allow(clippy::readonly_write_lock)]
        let mut inner = self.inner.write().unwrap();

        // 1. Check if page is already in the buffer pool
        if let Some(&frame_id) = inner.page_table.get(&page_id) {
            let frame = &mut inner.frames[frame_id.as_usize()];
            frame.pin();
            drop(inner);
            return Ok(PageWriteGuard::new(self, frame_id, page_id));
        }

        // 2. Get a free frame
        let frame_id = inner.free_list.pop().ok_or(BufferPoolError::NoFreeFrames)?;

        // 3. Load page from storage
        let frame = &mut inner.frames[frame_id.as_usize()];
        self.storage
            .read_page(page_id, frame.data_mut().as_mut_slice())
            .await?;

        // 4. Update frame metadata and page table
        frame.reset(page_id);
        inner.page_table.insert(page_id, frame_id);

        drop(inner);
        Ok(PageWriteGuard::new(self, frame_id, page_id))
    }

    /// Explicitly unpins a page.
    ///
    /// This method is provided for advanced use cases. In normal usage,
    /// pages are automatically unpinned when `PageGuard` is dropped.
    ///
    /// # Arguments
    ///
    /// * `page_id` - The page to unpin
    /// * `is_dirty` - Whether the caller modified the page
    ///
    /// # Panics
    ///
    /// Panics if the page is not in the buffer pool or has `pin_count == 0`.
    pub async fn unpin_page(&self, page_id: PageId, is_dirty: bool) {
        let mut inner = self.inner.write().unwrap();

        let frame_id = inner
            .page_table
            .get(&page_id)
            .copied()
            .expect("unpin_page called for page not in buffer pool");

        let frame = &mut inner.frames[frame_id.as_usize()];
        frame.unpin();

        if is_dirty {
            frame.mark_dirty();
        }

        // WEEK-8: Notify LRU Replacer that frame is now evictable
        // if frame.pin_count() == 0 {
        //     replacer.unpin(frame_id);
        // }
    }

    /// Allocates a new page in storage and fetches it into the buffer pool.
    ///
    /// The new page is initialized with zeros and returned as a write guard.
    ///
    /// # Errors
    ///
    /// - `BufferPoolError::NoFreeFrames` if the buffer pool is full
    /// - `BufferPoolError::Storage` if storage allocation fails
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use enhance::storage::{MemoryStorage, BufferPoolManager, BufferPoolConfig};
    /// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// # let storage = MemoryStorage::new();
    /// # let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());
    /// let mut guard = bpm.new_page().await?;
    /// let page_id = guard.page_id();
    /// guard[0] = 42;
    /// # Ok(())
    /// # }
    /// ```
    #[allow(clippy::await_holding_lock)]
    pub async fn new_page(&self) -> Result<PageWriteGuard<'_, S>, BufferPoolError> {
        // 1. Get a free frame FIRST to avoid page leaks
        #[allow(clippy::readonly_write_lock)]
        let mut inner = self.inner.write().unwrap();
        let frame_id = inner.free_list.pop().ok_or(BufferPoolError::NoFreeFrames)?;
        drop(inner);

        // 2. Allocate a new page in storage
        let page_id = self.storage.allocate_page().await?;

        // 3. Initialize frame (no need to read from storage - it's already zeros)
        let mut inner = self.inner.write().unwrap();
        let frame = &mut inner.frames[frame_id.as_usize()];
        frame.reset(page_id);
        inner.page_table.insert(page_id, frame_id);

        drop(inner);
        Ok(PageWriteGuard::new(self, frame_id, page_id))
    }

    /// Flushes a specific page to disk if dirty.
    ///
    /// Does not unpin the page. If the page is not in the buffer pool,
    /// this is a no-op.
    ///
    /// # Errors
    ///
    /// - `BufferPoolError::Storage` if the write fails
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use enhance::storage::{MemoryStorage, BufferPoolManager, BufferPoolConfig, PageId};
    /// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// # let storage = MemoryStorage::new();
    /// # let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());
    /// bpm.flush_page(PageId::new(0)).await?;
    /// # Ok(())
    /// # }
    /// ```
    #[allow(clippy::await_holding_lock)]
    pub async fn flush_page(&self, page_id: PageId) -> Result<(), BufferPoolError> {
        #[allow(clippy::readonly_write_lock)]
        let mut inner = self.inner.write().unwrap();

        // If page is not in buffer pool, nothing to flush
        let Some(&frame_id) = inner.page_table.get(&page_id) else {
            return Ok(());
        };

        let frame = &mut inner.frames[frame_id.as_usize()];

        // Only flush if dirty
        if frame.is_dirty() {
            // WEEK-21: Before flushing, ensure WAL is flushed up to page_lsn
            // wal_manager.flush_to_lsn(frame.page_lsn).await?;

            self.storage
                .write_page(page_id, frame.data().as_slice())
                .await?;

            // Clear dirty flag after successful write
            frame.clear_dirty();
        }

        Ok(())
    }

    /// Flushes all dirty pages to disk.
    ///
    /// This is useful for checkpointing or graceful shutdown.
    ///
    /// # Errors
    ///
    /// Returns the first error encountered. Some pages may remain unflushed
    /// if an error occurs.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use enhance::storage::{MemoryStorage, BufferPoolManager, BufferPoolConfig};
    /// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// # let storage = MemoryStorage::new();
    /// # let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());
    /// bpm.flush_all().await?;
    /// # Ok(())
    /// # }
    /// ```
    #[allow(clippy::await_holding_lock)]
    pub async fn flush_all(&self) -> Result<(), BufferPoolError> {
        let inner = self.inner.read().unwrap();

        // Collect dirty pages
        let dirty_pages: Vec<(PageId, FrameId)> = inner
            .page_table
            .iter()
            .filter_map(|(&page_id, &frame_id)| {
                let frame = &inner.frames[frame_id.as_usize()];
                if frame.is_dirty() {
                    Some((page_id, frame_id))
                } else {
                    None
                }
            })
            .collect();

        drop(inner);

        // Flush each dirty page
        for (page_id, _frame_id) in dirty_pages {
            self.flush_page(page_id).await?;
        }

        Ok(())
    }

    /// Deletes a page from the buffer pool and storage.
    ///
    /// # Week 7 Limitation
    ///
    /// This method only removes the page from the buffer pool.
    /// It does NOT delete the page from storage (Storage trait has no delete_page method).
    ///
    /// # Arguments
    ///
    /// * `page_id` - The page to delete
    ///
    /// # Returns
    ///
    /// Returns `true` if the page was in the buffer pool and deleted, `false` otherwise.
    ///
    /// # Panics
    ///
    /// Panics if the page is currently pinned.
    pub async fn delete_page(&self, page_id: PageId) -> bool {
        let mut inner = self.inner.write().unwrap();

        let Some(&frame_id) = inner.page_table.get(&page_id) else {
            return false;
        };

        let frame = &mut inner.frames[frame_id.as_usize()];

        assert!(
            !frame.is_pinned(),
            "Cannot delete pinned page {:?}",
            page_id
        );

        // Clear frame and return to free list
        frame.clear();
        inner.page_table.remove(&page_id);
        inner.free_list.push(frame_id);

        true
    }
}

// NOTE: For production, the BufferPoolManager would need:
// - Graceful shutdown: flush all dirty pages and wait for all pins to be released
// - Metrics: track hit rate, eviction count, pin/unpin frequency
// - Connection with WAL Manager: ensure page_lsn ≤ flushed_lsn before evicting dirty pages
// - Error recovery: handle partial writes, corrupted pages, disk full scenarios

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::MemoryStorage;

    #[tokio::test]
    async fn test_new_bpm() {
        let storage = MemoryStorage::new();
        let config = BufferPoolConfig { pool_size: 10 };
        let bpm = BufferPoolManager::new(storage, config);

        assert_eq!(bpm.config().pool_size, 10);
        assert_eq!(bpm.frame_count().await, 0);
    }

    #[tokio::test]
    async fn test_new_page() {
        let storage = MemoryStorage::new();
        let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());

        let guard = bpm.new_page().await.unwrap();
        let page_id = guard.page_id();

        // Verify page was allocated
        assert!(page_id.page_num() < u64::MAX);
        assert_eq!(bpm.frame_count().await, 1);
    }

    #[tokio::test]
    async fn test_fetch_page_loads_from_storage() {
        let storage = MemoryStorage::new();
        let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());

        // Allocate and write a page directly to storage
        let page_id = bpm.storage.allocate_page().await.unwrap();
        let mut buf = vec![0u8; 8192];
        buf[0] = 42;
        bpm.storage.write_page(page_id, &buf).await.unwrap();

        // Fetch the page through BPM
        let guard = bpm.fetch_page(page_id).await.unwrap();
        assert_eq!(guard[0], 42);
        assert_eq!(bpm.frame_count().await, 1);
    }

    #[tokio::test]
    async fn test_fetch_page_returns_cached() {
        let storage = MemoryStorage::new();
        let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());

        let mut guard = bpm.new_page().await.unwrap();
        let page_id = guard.page_id();
        guard[0] = 99;
        drop(guard);

        // Fetch again - should return from cache
        let guard = bpm.fetch_page(page_id).await.unwrap();
        assert_eq!(guard[0], 99);
        assert_eq!(bpm.frame_count().await, 1); // Still only 1 frame occupied
    }

    #[tokio::test]
    async fn test_fetch_page_mut_marks_dirty() {
        let storage = MemoryStorage::new();
        let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());

        let page_id = bpm.storage.allocate_page().await.unwrap();
        let buf = vec![0u8; 8192];
        bpm.storage.write_page(page_id, &buf).await.unwrap();

        // Fetch for write
        let mut guard = bpm.fetch_page_mut(page_id).await.unwrap();
        guard[0] = 42;
        drop(guard);

        // Verify dirty flag is set
        let inner = bpm.inner.read().unwrap();
        let frame_id = *inner.page_table.get(&page_id).unwrap();
        let frame = &inner.frames[frame_id.as_usize()];
        assert!(frame.is_dirty());
    }

    #[tokio::test]
    async fn test_pin_count_management() {
        let storage = MemoryStorage::new();
        let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());

        let page_id = bpm.storage.allocate_page().await.unwrap();

        // Fetch twice
        let guard1 = bpm.fetch_page(page_id).await.unwrap();
        let guard2 = bpm.fetch_page(page_id).await.unwrap();

        // Check pin count
        let inner = bpm.inner.read().unwrap();
        let frame_id = *inner.page_table.get(&page_id).unwrap();
        let frame = &inner.frames[frame_id.as_usize()];
        assert_eq!(frame.pin_count(), 2);
        drop(inner);

        // Drop one guard
        drop(guard1);

        let inner = bpm.inner.read().unwrap();
        let frame = &inner.frames[frame_id.as_usize()];
        assert_eq!(frame.pin_count(), 1);
        drop(inner);

        // Drop second guard
        drop(guard2);

        let inner = bpm.inner.read().unwrap();
        let frame = &inner.frames[frame_id.as_usize()];
        assert_eq!(frame.pin_count(), 0);
    }

    #[tokio::test]
    async fn test_flush_page() {
        let storage = MemoryStorage::new();
        let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());

        let mut guard = bpm.new_page().await.unwrap();
        let page_id = guard.page_id();
        guard[0] = 42;
        drop(guard);

        // Flush the page
        bpm.flush_page(page_id).await.unwrap();

        // Verify dirty flag is cleared
        let inner = bpm.inner.read().unwrap();
        let frame_id = *inner.page_table.get(&page_id).unwrap();
        let frame = &inner.frames[frame_id.as_usize()];
        assert!(!frame.is_dirty());
        drop(inner);

        // Verify data persisted to storage
        let mut buf = vec![0u8; 8192];
        bpm.storage.read_page(page_id, &mut buf).await.unwrap();
        assert_eq!(buf[0], 42);
    }

    #[tokio::test]
    async fn test_flush_all() {
        let storage = MemoryStorage::new();
        let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());

        // Create and modify multiple pages
        let mut page_ids = Vec::new();
        for i in 0..5 {
            let mut guard = bpm.new_page().await.unwrap();
            guard[0] = i as u8;
            page_ids.push(guard.page_id());
        }

        // Flush all
        bpm.flush_all().await.unwrap();

        // Verify all pages are clean
        let inner = bpm.inner.read().unwrap();
        for &page_id in &page_ids {
            let frame_id = *inner.page_table.get(&page_id).unwrap();
            let frame = &inner.frames[frame_id.as_usize()];
            assert!(!frame.is_dirty());
        }
    }

    #[tokio::test]
    async fn test_no_free_frames_error() {
        let storage = MemoryStorage::new();
        let config = BufferPoolConfig { pool_size: 2 };
        let bpm = BufferPoolManager::new(storage, config);

        // Allocate all frames
        let _guard1 = bpm.new_page().await.unwrap();
        let _guard2 = bpm.new_page().await.unwrap();

        // Should fail - no free frames
        let result = bpm.new_page().await;
        assert!(matches!(result, Err(BufferPoolError::NoFreeFrames)));
    }

    #[tokio::test]
    async fn test_delete_page() {
        let storage = MemoryStorage::new();
        let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());

        let guard = bpm.new_page().await.unwrap();
        let page_id = guard.page_id();
        drop(guard);

        // Delete the page
        let deleted = bpm.delete_page(page_id).await;
        assert!(deleted);
        assert_eq!(bpm.frame_count().await, 0);

        // Try to delete again - should return false
        let deleted = bpm.delete_page(page_id).await;
        assert!(!deleted);
    }

    #[tokio::test]
    #[should_panic(expected = "Cannot delete pinned page")]
    async fn test_delete_pinned_page_panics() {
        let storage = MemoryStorage::new();
        let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());

        let guard = bpm.new_page().await.unwrap();
        let page_id = guard.page_id();

        // Should panic - page is still pinned
        bpm.delete_page(page_id).await;
    }
}
