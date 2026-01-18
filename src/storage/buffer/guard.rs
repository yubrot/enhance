//! RAII guards for page access.
//!
//! Guards automatically unpin pages when dropped, preventing pin leaks.

use super::frame::FrameId;
use super::manager::BufferPoolManager;
use crate::storage::{PageData, PageId, Storage};
use std::ops::{Deref, DerefMut};

/// Read guard for accessing a page in the buffer pool.
///
/// When dropped, automatically unpins the page. This prevents pin leaks
/// and ensures that pages can be evicted when no longer in use.
///
/// # Week 7 Implementation
///
/// The guard holds a reference to the `BufferPoolManager` and uses a
/// synchronous `Mutex` in `Drop` to avoid the async Drop problem.
///
/// # Week 8 Evolution
///
/// In Week 8, this will hold an `RwLockReadGuard` for page-level latching:
/// ```text
/// pub struct PageReadGuard<'a> {
///     _latch: RwLockReadGuard<'a, PageData>,
///     bpm: &'a BufferPoolManager,
///     frame_id: FrameId,
/// }
/// ```
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
/// println!("First byte: {}", data[0]);
/// // Page is automatically unpinned when guard is dropped
/// # Ok(())
/// # }
/// ```
pub struct PageReadGuard<'a, S: Storage> {
    bpm: &'a BufferPoolManager<S>,
    frame_id: FrameId,
    page_id: PageId,
}

impl<'a, S: Storage> PageReadGuard<'a, S> {
    /// Creates a new read guard (internal use only).
    pub(super) fn new(bpm: &'a BufferPoolManager<S>, frame_id: FrameId, page_id: PageId) -> Self {
        Self {
            bpm,
            frame_id,
            page_id,
        }
    }

    /// Returns the `PageId` of the guarded page.
    pub fn page_id(&self) -> PageId {
        self.page_id
    }

    /// Access the page data as a byte slice.
    pub fn as_slice(&self) -> &[u8] {
        // SAFETY: WEEK-7 LIMITATION - This implementation is only safe for
        // single-threaded/single-task usage. The transmute extends the lifetime
        // of the data reference beyond the RwLock guard, which means:
        // - The frame cannot be evicted (guaranteed by pin_count > 0)
        // - BUT the frame CAN be modified by another thread/task acquiring
        //   a write lock after this read lock is released
        //
        // For Week 7, all tests assume single-threaded access to each page.
        //
        // WEEK-8: This will be replaced with per-frame RwLock that is held
        // for the guard's lifetime, providing proper read/write exclusion:
        // ```rust
        // pub struct PageReadGuard<'a> {
        //     _latch: RwLockReadGuard<'a, PageData>,
        //     ...
        // }
        // ```
        let inner = self.bpm.inner.read().unwrap();
        let frame = &inner.frames[self.frame_id.as_usize()];

        unsafe { std::mem::transmute(frame.data().as_slice()) }
    }

    /// Manually releases the guard, unpinning the page.
    ///
    /// This should be called before dropping the guard to ensure proper cleanup.
    /// If not called, Drop will attempt to unpin but may fail in certain contexts.
    pub async fn release(self) {
        self.bpm.unpin_page(self.page_id, false).await;
        std::mem::forget(self); // Prevent Drop from running
    }
}

impl<S: Storage> Drop for PageReadGuard<'_, S> {
    fn drop(&mut self) {
        // WEEK-7: Simplified Drop implementation.
        // In Week 7, we use try_write to avoid blocking in Drop.
        // If the lock cannot be acquired, we skip unpinning (pin leak).
        //
        // WEEK-8: This will be replaced with per-frame locks that can be
        // acquired synchronously without blocking the runtime.

        if let Ok(mut inner) = self.bpm.inner.try_write() {
            let frame = &mut inner.frames[self.frame_id.as_usize()];
            frame.unpin();
        } else {
            eprintln!(
                "WARNING: Failed to unpin page {:?} in Drop - pin leak detected",
                self.page_id
            );
        }
    }
}

/// Write guard for accessing and modifying a page.
///
/// When dropped, marks the page as dirty and unpins it.
///
/// # Example
///
/// ```no_run
/// # use enhance::storage::{MemoryStorage, BufferPoolManager, BufferPoolConfig, PageId};
/// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
/// # let storage = MemoryStorage::new();
/// # let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());
/// let mut guard = bpm.fetch_page_mut(PageId::new(0)).await?;
/// guard.as_mut_slice()[0] = 42;
/// // Page is marked dirty and unpinned when guard is dropped
/// # Ok(())
/// # }
/// ```
pub struct PageWriteGuard<'a, S: Storage> {
    bpm: &'a BufferPoolManager<S>,
    frame_id: FrameId,
    page_id: PageId,
    /// Track whether the page was modified to set dirty flag on drop.
    was_modified: bool,
}

impl<'a, S: Storage> PageWriteGuard<'a, S> {
    /// Creates a new write guard (internal use only).
    pub(super) fn new(bpm: &'a BufferPoolManager<S>, frame_id: FrameId, page_id: PageId) -> Self {
        Self {
            bpm,
            frame_id,
            page_id,
            was_modified: false,
        }
    }

    /// Returns the `PageId` of the guarded page.
    pub fn page_id(&self) -> PageId {
        self.page_id
    }

    /// Access the page data as a byte slice.
    pub fn as_slice(&self) -> &[u8] {
        // SAFETY: See PageReadGuard::as_slice() for detailed safety discussion.
        // Week 7: single-threaded/single-task access only.
        let inner = self.bpm.inner.read().unwrap();
        let frame = &inner.frames[self.frame_id.as_usize()];
        unsafe { std::mem::transmute(frame.data().as_slice()) }
    }

    /// Access the page data as a mutable byte slice.
    ///
    /// Calling this method marks the page as dirty.
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        self.was_modified = true;

        let mut inner = self.bpm.inner.write().unwrap();
        let frame = &mut inner.frames[self.frame_id.as_usize()];

        // Mark dirty immediately (data_mut() will also mark dirty, but that's fine)
        frame.mark_dirty();

        // SAFETY: See PageReadGuard::as_slice() for detailed safety discussion.
        // Week 7: single-threaded/single-task access only.
        unsafe { std::mem::transmute(frame.data_mut().as_mut_slice()) }
    }

    /// Returns a reference to the underlying `PageData`.
    pub fn data(&self) -> &PageData {
        // SAFETY: See PageReadGuard::as_slice() for detailed safety discussion.
        // Week 7: single-threaded/single-task access only.
        let inner = self.bpm.inner.read().unwrap();
        let frame = &inner.frames[self.frame_id.as_usize()];
        unsafe { std::mem::transmute(frame.data()) }
    }

    /// Returns a mutable reference to the underlying `PageData`.
    ///
    /// Calling this method marks the page as dirty.
    pub fn data_mut(&mut self) -> &mut PageData {
        self.was_modified = true;

        let mut inner = self.bpm.inner.write().unwrap();
        let frame = &mut inner.frames[self.frame_id.as_usize()];

        // Mark dirty immediately
        frame.mark_dirty();

        // SAFETY: See PageReadGuard::as_slice() for detailed safety discussion.
        // Week 7: single-threaded/single-task access only.
        unsafe { std::mem::transmute(frame.data_mut()) }
    }

    /// Manually releases the guard, unpinning the page and marking it dirty if modified.
    ///
    /// This should be called before dropping the guard to ensure proper cleanup.
    pub async fn release(self) {
        self.bpm.unpin_page(self.page_id, self.was_modified).await;
        std::mem::forget(self); // Prevent Drop from running
    }
}

impl<S: Storage> Drop for PageWriteGuard<'_, S> {
    fn drop(&mut self) {
        // WEEK-7: Simplified Drop implementation using try_write.
        if let Ok(mut inner) = self.bpm.inner.try_write() {
            let frame = &mut inner.frames[self.frame_id.as_usize()];
            if self.was_modified {
                frame.mark_dirty();
            }
            frame.unpin();
        } else {
            eprintln!(
                "WARNING: Failed to unpin page {:?} in Drop - pin leak detected",
                self.page_id
            );
        }
    }
}

// Implement Deref for convenient access to PageData methods
impl<S: Storage> Deref for PageReadGuard<'_, S> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<S: Storage> Deref for PageWriteGuard<'_, S> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<S: Storage> DerefMut for PageWriteGuard<'_, S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

// NOTE: For production, consider:
// - Timeout for acquiring page latches (avoid indefinite blocking)
// - Debug mode assertions to detect common errors (double-unpin, use-after-drop)
// - Panic-safe Drop implementation (ensure unpin happens even if panic occurs)
