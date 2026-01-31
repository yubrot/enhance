//! RAII guards for buffer pool pages.
//!
//! These guards provide safe access to page data and ensure automatic
//! unpinning when the guard is dropped.

use std::ops::{Deref, DerefMut};

use tokio::sync::{RwLockReadGuard, RwLockWriteGuard};

use super::frame::FrameId;
use super::pool::BufferPoolInner;
use super::replacer::Replacer;
use crate::storage::{PageData, PageId, Storage};

/// RAII guard for reading a page in the buffer pool.
///
/// When this guard is dropped, the page is automatically unpinned,
/// making it eligible for eviction if no other references exist.
///
/// # Latch Ordering
///
/// This guard holds a read lock on the frame's data. Multiple read guards
/// can exist for the same page simultaneously. When acquiring multiple pages,
/// always acquire in ascending `PageId` order to prevent deadlocks.
///
/// # Example
///
/// ```no_run
/// use enhance::storage::{BufferPool, LruReplacer, MemoryStorage, PageId};
///
/// # async fn example() -> Result<(), enhance::storage::BufferPoolError> {
/// let storage = MemoryStorage::new();
/// let replacer = LruReplacer::new(10);
/// let bpm = BufferPool::new(storage, replacer, 10);
/// let page_id = PageId::new(0);
///
/// let guard = bpm.fetch_page(page_id).await?;
/// let data: &[u8] = guard.data();
/// // Page is unpinned when guard goes out of scope
/// # Ok(())
/// # }
/// ```
pub struct PageReadGuard<'a, S: Storage, R: Replacer> {
    /// Reference to the buffer pool's inner state for unpinning.
    pub(super) inner: &'a BufferPoolInner<S, R>,

    /// The frame ID this guard references.
    pub(super) frame_id: FrameId,

    /// The page ID for this guard.
    pub(super) page_id: PageId,

    /// The read lock guard for the frame's data.
    pub(super) data_guard: RwLockReadGuard<'a, PageData>,
}

impl<S: Storage, R: Replacer> PageReadGuard<'_, S, R> {
    /// Returns the page ID.
    pub fn page_id(&self) -> PageId {
        self.page_id
    }

    /// Returns the page data as a byte slice.
    pub fn data(&self) -> &[u8] {
        self.data_guard.as_slice()
    }
}

impl<S: Storage, R: Replacer> AsRef<[u8]> for PageReadGuard<'_, S, R> {
    fn as_ref(&self) -> &[u8] {
        self.data()
    }
}

impl<S: Storage, R: Replacer> Deref for PageReadGuard<'_, S, R> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.data()
    }
}

impl<S: Storage, R: Replacer> Drop for PageReadGuard<'_, S, R> {
    fn drop(&mut self) {
        self.inner.release(self.frame_id, false);
    }
}

/// RAII guard for writing to a page in the buffer pool.
///
/// When this guard is dropped, the page is automatically unpinned.
/// If `mark_dirty()` was called, the dirty flag is set on the frame,
/// ensuring the page will be written back to storage before eviction.
///
/// # Latch Ordering
///
/// This guard holds a write lock on the frame's data. Only one write guard
/// can exist for a page at a time. When acquiring multiple pages, always
/// acquire in ascending `PageId` order to prevent deadlocks.
///
/// # Example
///
/// ```no_run
/// use enhance::storage::{BufferPool, LruReplacer, MemoryStorage, PageId};
///
/// # async fn example() -> Result<(), enhance::storage::BufferPoolError> {
/// let storage = MemoryStorage::new();
/// let replacer = LruReplacer::new(10);
/// let bpm = BufferPool::new(storage, replacer, 10);
/// let page_id = PageId::new(0);
///
/// let mut guard = bpm.fetch_page_mut(page_id).await?;
/// guard.data_mut()[0] = 42;
/// guard.mark_dirty();
/// // Page is unpinned (and marked dirty) when guard goes out of scope
/// # Ok(())
/// # }
/// ```
pub struct PageWriteGuard<'a, S: Storage, R: Replacer> {
    /// Reference to the buffer pool's inner state for unpinning.
    pub(super) inner: &'a BufferPoolInner<S, R>,

    /// The frame ID this guard references.
    pub(super) frame_id: FrameId,

    /// The page ID for this guard.
    pub(super) page_id: PageId,

    /// The write lock guard for the frame's data.
    pub(super) data_guard: RwLockWriteGuard<'a, PageData>,

    /// Whether this page has been marked dirty.
    pub(super) is_dirty: bool,
}

impl<S: Storage, R: Replacer> PageWriteGuard<'_, S, R> {
    /// Returns the page ID.
    pub fn page_id(&self) -> PageId {
        self.page_id
    }

    /// Returns the page data as a byte slice.
    pub fn data(&self) -> &[u8] {
        self.data_guard.as_slice()
    }

    /// Returns the page data as a mutable byte slice.
    pub fn data_mut(&mut self) -> &mut [u8] {
        self.data_guard.as_mut_slice()
    }

    /// Marks this page as dirty (modified).
    ///
    /// Dirty pages will be written back to storage before eviction.
    /// This must be called after modifying the page data.
    pub fn mark_dirty(&mut self) {
        self.is_dirty = true;
    }
}

impl<S: Storage, R: Replacer> AsRef<[u8]> for PageWriteGuard<'_, S, R> {
    fn as_ref(&self) -> &[u8] {
        self.data()
    }
}

impl<S: Storage, R: Replacer> AsMut<[u8]> for PageWriteGuard<'_, S, R> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.data_mut()
    }
}

impl<S: Storage, R: Replacer> Deref for PageWriteGuard<'_, S, R> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.data()
    }
}

impl<S: Storage, R: Replacer> DerefMut for PageWriteGuard<'_, S, R> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.data_mut()
    }
}

impl<S: Storage, R: Replacer> Drop for PageWriteGuard<'_, S, R> {
    fn drop(&mut self) {
        self.inner.release(self.frame_id, self.is_dirty);
    }
}
