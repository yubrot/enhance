//! Frame management for the buffer pool.
//!
//! A frame is a slot in the buffer pool that can hold one 8KB page at a time.
//! Each frame tracks metadata about the loaded page (if any).

use crate::storage::{PageData, PageId};

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

/// A frame in the buffer pool containing page data and metadata.
///
/// Each frame can hold exactly one page at a time. The frame tracks:
/// - Which page is currently loaded (if any)
/// - How many operations are currently using the page (`pin_count`)
/// - Whether the page has been modified (`is_dirty`)
///
/// # Lifecycle
///
/// 1. **Empty**: `page_id = None`, frame is in the free_list
/// 2. **Loaded**: Page is read from storage, `page_id = Some(...)`
/// 3. **Pinned**: `pin_count > 0`, page cannot be evicted
/// 4. **Unpinned**: `pin_count = 0`, page can be evicted (Week 8+)
/// 5. **Evicted**: If dirty, written to storage, then returned to free_list
///
/// # Week 8 Evolution
///
/// The `Frame` struct will evolve to support fine-grained locking:
/// - `data: RwLock<PageData>` for page-level latches
/// - `meta: Mutex<FrameMeta>` for metadata protection
pub struct Frame {
    /// The page data buffer (always allocated).
    data: PageData,

    /// The `PageId` currently loaded in this frame, if any.
    page_id: Option<PageId>,

    /// Number of operations currently using this frame.
    ///
    /// A frame cannot be evicted while `pin_count > 0`.
    /// Each call to `fetch_page` increments this counter, and each `unpin_page`
    /// (or `PageGuard::drop`) decrements it.
    pin_count: u32,

    /// Whether the page has been modified since loading from disk.
    ///
    /// Dirty pages must be written back to storage before eviction.
    is_dirty: bool,
    // WEEK-21: WAL integration requires tracking the Log Sequence Number (LSN)
    // of the last modification to this page. Before flushing a dirty page,
    // the BPM must ensure that all WAL records up to page_lsn have been flushed.
    //
    // page_lsn: Option<u64>,
}

impl Frame {
    /// Creates a new empty frame.
    pub fn new() -> Self {
        Self {
            data: PageData::new(),
            page_id: None,
            pin_count: 0,
            is_dirty: false,
        }
    }

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

impl Default for Frame {
    fn default() -> Self {
        Self::new()
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
        let mut frame = Frame::new();
        let page_id = PageId::new(42);

        frame.reset(page_id);

        assert!(frame.is_occupied());
        assert!(frame.is_pinned());
        assert!(!frame.is_dirty());
        assert_eq!(frame.page_id(), Some(page_id));
        assert_eq!(frame.pin_count(), 1);
    }

    #[test]
    fn test_frame_pin_unpin() {
        let mut frame = Frame::new();
        frame.reset(PageId::new(1));

        assert_eq!(frame.pin_count(), 1);

        frame.pin();
        assert_eq!(frame.pin_count(), 2);

        frame.unpin();
        assert_eq!(frame.pin_count(), 1);
        assert!(frame.is_pinned());

        frame.unpin();
        assert_eq!(frame.pin_count(), 0);
        assert!(!frame.is_pinned());
    }

    #[test]
    #[should_panic(expected = "unpin called with pin_count == 0")]
    fn test_frame_unpin_panics_when_zero() {
        let mut frame = Frame::new();
        frame.unpin();
    }

    #[test]
    fn test_frame_data_mut_marks_dirty() {
        let mut frame = Frame::new();
        frame.reset(PageId::new(1));

        assert!(!frame.is_dirty());

        let _data = frame.data_mut();

        assert!(frame.is_dirty());
    }

    #[test]
    fn test_frame_clear() {
        let mut frame = Frame::new();
        frame.reset(PageId::new(1));
        frame.mark_dirty();

        frame.clear();

        assert!(!frame.is_occupied());
        assert!(!frame.is_pinned());
        assert!(!frame.is_dirty());
        assert_eq!(frame.page_id(), None);
    }
}
