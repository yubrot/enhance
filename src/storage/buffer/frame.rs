//! Frame management for the buffer pool.
//!
//! A frame is a slot in the buffer pool that can hold one 8KB page at a time.
//! Each frame tracks metadata about the loaded page (if any).

use crate::storage::{PageData, PageId};
use std::sync::RwLock;

/// Identifier for a frame in the buffer pool.
///
/// `FrameId` is distinct from `PageId`: `PageId` identifies a logical page on disk,
/// while `FrameId` identifies a physical memory slot in the buffer pool.
///
/// `FrameId`s are valid only within the context of a single `BufferPoolManager` instance
/// and range from 0 to pool_size-1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FrameId(usize);

impl FrameId {
    /// Creates a new `FrameId`.
    pub const fn new(id: usize) -> Self {
        Self(id)
    }

    /// Returns the frame ID as a `usize`.
    pub const fn as_usize(&self) -> usize {
        self.0
    }
}

/// A frame in the buffer pool with per-frame locking.
///
/// # Week 8 Architecture
///
/// The frame uses an `RwLock` to protect its internal state, enabling
/// fine-grained concurrency control. Multiple readers can access the frame
/// simultaneously, while writers have exclusive access.
///
/// # Lifecycle
///
/// 1. **Empty**: `page_id = None`, frame is in the free_list
/// 2. **Loaded**: Page is read from storage, `page_id = Some(...)`
/// 3. **Pinned**: `pin_count > 0`, page cannot be evicted
/// 4. **Unpinned**: `pin_count = 0`, page can be evicted
/// 5. **Evicted**: If dirty, written to storage, then returned to free_list
pub struct Frame {
    /// The frame's internal state, protected by RwLock.
    ///
    /// Read lock: for reading page data and metadata
    /// Write lock: for modifying page data, incrementing pin_count, or evicting
    inner: RwLock<FrameInner>,
}

/// Inner state of a frame protected by RwLock.
///
/// This structure contains all the mutable state of a frame. The `Frame`
/// struct wraps this in an `RwLock` to provide thread-safe access.
pub struct FrameInner {
    /// The page data buffer (always allocated).
    pub(super) data: PageData,

    /// The `PageId` currently loaded in this frame, if any.
    pub(super) page_id: Option<PageId>,

    /// Number of operations currently using this frame.
    ///
    /// A frame cannot be evicted while `pin_count > 0`.
    /// Each call to `fetch_page` increments this counter, and each `unpin_page`
    /// (or `PageGuard::drop`) decrements it.
    pub(super) pin_count: u32,

    /// Whether the page has been modified since loading from disk.
    ///
    /// Dirty pages must be written back to storage before eviction.
    pub(super) is_dirty: bool,
    // WEEK-21: WAL integration requires tracking the Log Sequence Number (LSN)
    // of the last modification to this page. Before flushing a dirty page,
    // the BPM must ensure that all WAL records up to page_lsn have been flushed.
    //
    // pub(super) page_lsn: Option<u64>,
}

impl Frame {
    /// Creates a new empty frame.
    pub fn new() -> Self {
        Self {
            inner: RwLock::new(FrameInner {
                data: PageData::new(),
                page_id: None,
                pin_count: 0,
                is_dirty: false,
            }),
        }
    }

    /// Acquires a read lock on the frame's inner state.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned.
    pub fn read(&self) -> std::sync::RwLockReadGuard<'_, FrameInner> {
        self.inner.read().unwrap()
    }

    /// Acquires a write lock on the frame's inner state.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned.
    pub fn write(&self) -> std::sync::RwLockWriteGuard<'_, FrameInner> {
        self.inner.write().unwrap()
    }

    /// Attempts to acquire a write lock without blocking.
    ///
    /// Returns `None` if the lock is currently held.
    pub fn try_write(&self) -> Option<std::sync::RwLockWriteGuard<'_, FrameInner>> {
        self.inner.try_write().ok()
    }

    /// Returns true if this frame is currently pinned (in use).
    pub fn is_pinned(&self) -> bool {
        self.read().pin_count > 0
    }

    /// Returns true if the frame contains a page.
    pub fn is_occupied(&self) -> bool {
        self.read().page_id.is_some()
    }

    /// Returns the `PageId` of the loaded page, if any.
    pub fn page_id(&self) -> Option<PageId> {
        self.read().page_id
    }

    /// Returns the pin count.
    pub fn pin_count(&self) -> u32 {
        self.read().pin_count
    }

    /// Returns true if the page has been modified.
    pub fn is_dirty(&self) -> bool {
        self.read().is_dirty
    }
}

impl Default for Frame {
    fn default() -> Self {
        Self::new()
    }
}

impl FrameInner {
    /// Returns true if this frame is currently pinned (in use).
    pub fn is_pinned(&self) -> bool {
        self.pin_count > 0
    }

    /// Returns true if the frame contains a page.
    pub fn is_occupied(&self) -> bool {
        self.page_id.is_some()
    }

    /// Returns the `PageId` of the loaded page, if any.
    pub fn page_id(&self) -> Option<PageId> {
        self.page_id
    }

    /// Returns the pin count.
    pub fn pin_count(&self) -> u32 {
        self.pin_count
    }

    /// Returns true if the page has been modified.
    pub fn is_dirty(&self) -> bool {
        self.is_dirty
    }

    /// Access the page data immutably.
    pub fn data(&self) -> &PageData {
        &self.data
    }

    /// Access the page data mutably and mark the page as dirty.
    ///
    /// IMPORTANT: Calling this method automatically sets `is_dirty = true`.
    pub fn data_mut(&mut self) -> &mut PageData {
        self.is_dirty = true;
        &mut self.data
    }

    /// Increments the pin count.
    pub(super) fn pin(&mut self) {
        self.pin_count = self.pin_count.checked_add(1).expect("pin_count overflow");
    }

    /// Decrements the pin count.
    ///
    /// # Panics
    ///
    /// Panics if the pin count is already 0.
    pub(super) fn unpin(&mut self) {
        assert!(self.pin_count > 0, "unpin called with pin_count == 0");
        self.pin_count -= 1;
    }

    /// Marks the frame as dirty.
    pub(super) fn mark_dirty(&mut self) {
        self.is_dirty = true;
    }

    /// Clears the dirty flag (after flushing to disk).
    pub(super) fn clear_dirty(&mut self) {
        self.is_dirty = false;
    }

    /// Sets the page ID and resets metadata for a new page load.
    pub(super) fn reset(&mut self, page_id: PageId) {
        self.page_id = Some(page_id);
        self.pin_count = 1; // Initially pinned
        self.is_dirty = false;
    }

    /// Clears the frame, returning it to the empty state.
    pub(super) fn clear(&mut self) {
        self.page_id = None;
        self.pin_count = 0;
        self.is_dirty = false;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_frame_new_is_empty() {
        let frame = Frame::new();
        assert!(!frame.is_occupied());
        assert!(!frame.is_pinned());
        assert!(!frame.is_dirty());
        assert_eq!(frame.pin_count(), 0);
        assert_eq!(frame.page_id(), None);
    }

    #[test]
    fn test_frame_reset() {
        let frame = Frame::new();
        let page_id = PageId::new(42);

        {
            let mut frame_inner = frame.write();
            frame_inner.reset(page_id);
        }

        assert!(frame.is_occupied());
        assert!(frame.is_pinned());
        assert!(!frame.is_dirty());
        assert_eq!(frame.page_id(), Some(page_id));
        assert_eq!(frame.pin_count(), 1);
    }

    #[test]
    fn test_frame_pin_unpin() {
        let frame = Frame::new();

        {
            let mut frame_inner = frame.write();
            frame_inner.reset(PageId::new(1));
        }

        assert_eq!(frame.pin_count(), 1);

        {
            let mut frame_inner = frame.write();
            frame_inner.pin();
        }
        assert_eq!(frame.pin_count(), 2);

        {
            let mut frame_inner = frame.write();
            frame_inner.unpin();
        }
        assert_eq!(frame.pin_count(), 1);
        assert!(frame.is_pinned());

        {
            let mut frame_inner = frame.write();
            frame_inner.unpin();
        }
        assert_eq!(frame.pin_count(), 0);
        assert!(!frame.is_pinned());
    }

    #[test]
    #[should_panic(expected = "unpin called with pin_count == 0")]
    fn test_frame_unpin_panics_when_zero() {
        let frame = Frame::new();
        let mut frame_inner = frame.write();
        frame_inner.unpin();
    }

    #[test]
    fn test_frame_data_mut_marks_dirty() {
        let frame = Frame::new();

        {
            let mut frame_inner = frame.write();
            frame_inner.reset(PageId::new(1));
        }

        assert!(!frame.is_dirty());

        {
            let mut frame_inner = frame.write();
            let _data = frame_inner.data_mut();
        }

        assert!(frame.is_dirty());
    }

    #[test]
    fn test_frame_clear() {
        let frame = Frame::new();

        {
            let mut frame_inner = frame.write();
            frame_inner.reset(PageId::new(1));
            frame_inner.mark_dirty();
        }

        {
            let mut frame_inner = frame.write();
            frame_inner.clear();
        }

        assert!(!frame.is_occupied());
        assert!(!frame.is_pinned());
        assert!(!frame.is_dirty());
        assert_eq!(frame.page_id(), None);
    }
}
