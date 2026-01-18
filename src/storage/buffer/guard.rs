//! RAII guards for page access.
//!
//! Guards automatically unpin pages when dropped, preventing pin leaks.

use super::frame::{FrameId, FrameInner};
use super::manager::BufferPoolManager;
use super::replacer::Replacer;
use crate::storage::{PageData, PageId, Storage};
use std::mem::ManuallyDrop;
use std::ops::{Deref, DerefMut};
use std::sync::{RwLockReadGuard, RwLockWriteGuard};

/// Read guard for accessing a page in the buffer pool.
///
/// When dropped, automatically unpins the page. This prevents pin leaks
/// and ensures that pages can be evicted when no longer in use.
///
/// # Week 8 Architecture
///
/// The guard holds an `RwLockReadGuard` for the frame's inner state,
/// providing safe read access without unsafe transmute.
///
/// # Limitation
///
/// While holding a `PageReadGuard`, do not call `BufferPoolManager` methods
/// that acquire frame locks (e.g., `frame_count()`, `pin_count()`). This may
/// cause deadlock due to `RwLock` semantics - the guard holds a read lock, and
/// the same thread cannot acquire another lock on the same frame.
///
/// Safe usage pattern:
/// ```no_run
/// # use enhance::storage::{MemoryStorage, BufferPoolManager, BufferPoolConfig, PageId};
/// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
/// # let storage = MemoryStorage::new();
/// # let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());
/// let data = {
///     let guard = bpm.fetch_page(PageId::new(0)).await?;
///     guard[0] // Read data
/// }; // Guard dropped here
///
/// // Now safe to call other BPM methods
/// let count = bpm.frame_count().await;
/// # Ok(())
/// # }
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
    /// The frame's read lock guard, wrapped in ManuallyDrop.
    ///
    /// We use ManuallyDrop to control when the lock is released in Drop.
    /// This allows us to drop the lock before trying to unpin.
    latch: ManuallyDrop<RwLockReadGuard<'a, FrameInner>>,

    /// Reference to the BPM for unpin on drop.
    bpm: &'a BufferPoolManager<S>,

    /// Frame ID for unpin operation.
    frame_id: FrameId,

    /// Page ID for unpin operation.
    page_id: PageId,
}

impl<'a, S: Storage> PageReadGuard<'a, S> {
    /// Creates a new read guard (internal use only).
    ///
    /// # Panics
    ///
    /// Panics if the frame's lock is poisoned.
    pub(super) fn new(bpm: &'a BufferPoolManager<S>, frame_id: FrameId, page_id: PageId) -> Self {
        // Acquire the frame's read lock
        let latch = bpm.frames[frame_id.as_usize()].read();

        Self {
            latch: ManuallyDrop::new(latch),
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
        self.latch.data().as_slice()
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
        //  Week 8: Since we hold a read lock in self.latch, we can't directly
        // unpin (which requires a write lock). We must drop the read lock first.
        //
        // SAFETY: Manually drop the latch to release the read lock.
        unsafe {
            ManuallyDrop::drop(&mut self.latch);
        }

        // Now the read lock is released, we can acquire write lock to unpin
        // Note: We use try_write with a fallback to handle edge cases
        let frame = &self.bpm.frames[self.frame_id.as_usize()];

        if let Some(mut frame_inner) = frame.try_write() {
            frame_inner.unpin();

            // Notify replacer if frame became unpinned
            let became_unpinned = frame_inner.pin_count() == 0;
            drop(frame_inner);

            if became_unpinned
                && let Ok(mut replacer) = self.bpm.replacer.lock()
            {
                replacer.unpin(self.frame_id);
            }
        } else {
            eprintln!(
                "WARNING: Failed to unpin page {:?} in Drop - pin leak",
                self.page_id
            );
        }
    }
}

/// Write guard for accessing and modifying a page.
///
/// When dropped, marks the page as dirty and unpins it.
///
/// # Limitation
///
/// While holding a `PageWriteGuard`, do not call `BufferPoolManager` methods
/// that acquire frame locks (e.g., `frame_count()`, `pin_count()`). This may
/// cause deadlock due to `RwLock` semantics - the guard holds a write lock, and
/// the same thread cannot acquire another lock on the same frame.
///
/// Safe usage pattern:
/// ```no_run
/// # use enhance::storage::{MemoryStorage, BufferPoolManager, BufferPoolConfig, PageId};
/// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
/// # let storage = MemoryStorage::new();
/// # let bpm = BufferPoolManager::new(storage, BufferPoolConfig::default());
/// let page_id = {
///     let mut guard = bpm.fetch_page_mut(PageId::new(0)).await?;
///     guard[0] = 42; // Modify data
///     guard.page_id()
/// }; // Guard dropped here
///
/// // Now safe to call other BPM methods
/// let count = bpm.frame_count().await;
/// # Ok(())
/// # }
/// ```
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
    /// The frame's write lock guard, wrapped in ManuallyDrop.
    ///
    /// We use ManuallyDrop to control when the lock is released in Drop.
    latch: ManuallyDrop<RwLockWriteGuard<'a, FrameInner>>,

    /// Reference to the BPM for unpin on drop.
    bpm: &'a BufferPoolManager<S>,

    /// Frame ID for unpin operation.
    frame_id: FrameId,

    /// Page ID for unpin operation.
    page_id: PageId,

    /// Track whether the page was modified to set dirty flag on drop.
    was_modified: bool,
}

impl<'a, S: Storage> PageWriteGuard<'a, S> {
    /// Creates a new write guard (internal use only).
    ///
    /// # Panics
    ///
    /// Panics if the frame's lock is poisoned.
    pub(super) fn new(bpm: &'a BufferPoolManager<S>, frame_id: FrameId, page_id: PageId) -> Self {
        // Acquire the frame's write lock
        let latch = bpm.frames[frame_id.as_usize()].write();

        Self {
            latch: ManuallyDrop::new(latch),
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
        self.latch.data().as_slice()
    }

    /// Access the page data as a mutable byte slice.
    ///
    /// Calling this method marks the page as dirty.
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        self.was_modified = true;
        self.latch.data_mut().as_mut_slice()
    }

    /// Returns a reference to the underlying `PageData`.
    pub fn data(&self) -> &PageData {
        self.latch.data()
    }

    /// Returns a mutable reference to the underlying `PageData`.
    ///
    /// Calling this method marks the page as dirty.
    pub fn data_mut(&mut self) -> &mut PageData {
        self.was_modified = true;
        self.latch.data_mut()
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
        // Mark dirty if was modified (while we still hold the lock)
        if self.was_modified {
            self.latch.mark_dirty();
        }

        // Unpin while we still hold the write lock
        self.latch.unpin();

        // Check if we need to notify replacer
        let became_unpinned = self.latch.pin_count() == 0;

        // Now manually drop the latch to release the write lock
        unsafe {
            ManuallyDrop::drop(&mut self.latch);
        }

        // Notify replacer if frame became unpinned (after releasing the lock)
        if became_unpinned
            && let Ok(mut replacer) = self.bpm.replacer.lock()
        {
            replacer.unpin(self.frame_id);
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
