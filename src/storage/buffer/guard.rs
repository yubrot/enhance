//! RAII guards for buffer pool page access.

use super::frame::FrameId;
use super::pool::BufferPool;
use crate::storage::{PageData, PageId, Storage};
use std::ops::{Deref, DerefMut};
use tokio::sync::{RwLockReadGuard, RwLockWriteGuard};

/// RAII guard for read-only page access.
///
/// When dropped, automatically unpins the page in the buffer pool.
/// Provides immutable access to the page data.
///
/// # Example
///
/// ```no_run
/// # use enhance::storage::{BufferPool, MemoryStorage, PageId};
/// # async fn example() {
/// # let storage = MemoryStorage::new();
/// # let pool = BufferPool::new(storage, 10);
/// # let page_id = pool.new_page().await.unwrap().page_id();
/// let guard = pool.fetch_page_read(page_id).await.unwrap();
/// let data: &[u8] = &*guard;
/// // guard automatically unpins when dropped
/// # }
/// ```
pub struct PageReadGuard<'a, S: Storage> {
    pool: &'a BufferPool<S>,
    frame_id: FrameId,
    page_id: PageId,
    _lock: RwLockReadGuard<'a, PageData>,
}

impl<'a, S: Storage> PageReadGuard<'a, S> {
    /// Creates a new read guard.
    pub(super) fn new(
        pool: &'a BufferPool<S>,
        frame_id: FrameId,
        page_id: PageId,
        lock: RwLockReadGuard<'a, PageData>,
    ) -> Self {
        Self {
            pool,
            frame_id,
            page_id,
            _lock: lock,
        }
    }

    /// Returns the PageId of this page.
    pub fn page_id(&self) -> PageId {
        self.page_id
    }
}

impl<'a, S: Storage> Deref for PageReadGuard<'a, S> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self._lock.as_slice()
    }
}

impl<'a, S: Storage> Drop for PageReadGuard<'a, S> {
    fn drop(&mut self) {
        // Unpin the page when the guard is dropped (not dirty)
        self.pool.unpin_internal(self.frame_id, false);
    }
}

// SAFETY: The guard is Send if the pool is Send
unsafe impl<'a, S: Storage> Send for PageReadGuard<'a, S> {}

/// RAII guard for mutable page access.
///
/// When dropped, automatically unpins the page and marks it dirty.
/// Provides mutable access to the page data.
///
/// # Example
///
/// ```no_run
/// # use enhance::storage::{BufferPool, MemoryStorage, PageId};
/// # async fn example() {
/// # let storage = MemoryStorage::new();
/// # let pool = BufferPool::new(storage, 10);
/// # let page_id = pool.new_page().await.unwrap().page_id();
/// let mut guard = pool.fetch_page_write(page_id).await.unwrap();
/// guard[0] = 42;
/// // guard automatically marks dirty and unpins when dropped
/// # }
/// ```
pub struct PageWriteGuard<'a, S: Storage> {
    pool: &'a BufferPool<S>,
    frame_id: FrameId,
    page_id: PageId,
    _lock: RwLockWriteGuard<'a, PageData>,
}

impl<'a, S: Storage> PageWriteGuard<'a, S> {
    /// Creates a new write guard.
    pub(super) fn new(
        pool: &'a BufferPool<S>,
        frame_id: FrameId,
        page_id: PageId,
        lock: RwLockWriteGuard<'a, PageData>,
    ) -> Self {
        Self {
            pool,
            frame_id,
            page_id,
            _lock: lock,
        }
    }

    /// Returns the PageId of this page.
    pub fn page_id(&self) -> PageId {
        self.page_id
    }
}

impl<'a, S: Storage> Deref for PageWriteGuard<'a, S> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self._lock.as_slice()
    }
}

impl<'a, S: Storage> DerefMut for PageWriteGuard<'a, S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self._lock.as_mut_slice()
    }
}

impl<'a, S: Storage> Drop for PageWriteGuard<'a, S> {
    fn drop(&mut self) {
        // Mark dirty and unpin when dropped
        self.pool.unpin_internal(self.frame_id, true);
    }
}

unsafe impl<'a, S: Storage> Send for PageWriteGuard<'a, S> {}
