//! Buffer pool frame management.

use crate::storage::{PageData, PageId};
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, Ordering};
use tokio::sync::RwLock;

/// Identifier for a frame within the buffer pool.
///
/// FrameId is an index into the pool's frame array.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FrameId(pub(crate) u32);

impl FrameId {
    /// Creates a new FrameId.
    pub(crate) const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Returns the frame index.
    pub(crate) const fn index(&self) -> usize {
        self.0 as usize
    }
}

/// A frame in the buffer pool holding one page.
///
/// Each frame contains:
/// - The page data (8KB buffer)
/// - Metadata (page_id, dirty flag, pin count)
/// - RwLock for concurrent read/write access
///
/// # Concurrency Model
///
/// The frame uses a two-level locking scheme:
/// 1. `page_id`, `dirty`, `pin_count` are atomic for fast metadata access
/// 2. `data` is protected by RwLock for page content access
pub(crate) struct Frame {
    /// The page data buffer (8KB, page-aligned).
    data: RwLock<PageData>,

    /// The PageId currently stored in this frame, or None if empty.
    /// Uses Option<PageId> internally but stored as atomic u64 for lock-free access.
    /// u64::MAX represents None.
    page_id: AtomicU64,

    /// Whether this frame has been modified since last flush.
    dirty: AtomicBool,

    /// Number of users currently holding this frame.
    /// A frame can only be evicted when pin_count == 0.
    pin_count: AtomicU32,
}

impl Frame {
    /// Creates a new empty frame.
    pub fn new() -> Self {
        Self {
            data: RwLock::new(PageData::new()),
            page_id: AtomicU64::new(u64::MAX), // None sentinel
            dirty: AtomicBool::new(false),
            pin_count: AtomicU32::new(0),
        }
    }

    /// Returns the current page ID, if any.
    pub fn page_id(&self) -> Option<PageId> {
        let raw = self.page_id.load(Ordering::Acquire);
        if raw == u64::MAX {
            None
        } else {
            Some(PageId::new(raw))
        }
    }

    /// Sets the page ID for this frame.
    pub fn set_page_id(&self, page_id: Option<PageId>) {
        let raw = page_id.map(|p| p.page_num()).unwrap_or(u64::MAX);
        self.page_id.store(raw, Ordering::Release);
    }

    /// Returns whether the frame is dirty.
    pub fn is_dirty(&self) -> bool {
        self.dirty.load(Ordering::Acquire)
    }

    /// Marks the frame as dirty.
    pub fn mark_dirty(&self) {
        self.dirty.store(true, Ordering::Release);
    }

    /// Clears the dirty flag.
    pub fn clear_dirty(&self) {
        self.dirty.store(false, Ordering::Release);
    }

    /// Returns the current pin count.
    pub fn pin_count(&self) -> u32 {
        self.pin_count.load(Ordering::Acquire)
    }

    /// Increments the pin count. Returns new count.
    pub fn pin(&self) -> u32 {
        self.pin_count.fetch_add(1, Ordering::AcqRel) + 1
    }

    /// Decrements the pin count. Returns new count.
    ///
    /// # Safety
    ///
    /// If called when pin_count is already 0, this method will restore the count
    /// to 0 and return 0. In debug builds, this triggers a debug assertion.
    /// This design prevents panics in Drop implementations while catching bugs
    /// during development.
    pub fn unpin(&self) -> u32 {
        let old = self.pin_count.fetch_sub(1, Ordering::AcqRel);

        if old == 0 {
            // Underflow detected - restore to 0
            self.pin_count.fetch_add(1, Ordering::AcqRel);
            debug_assert!(false, "unpin called on frame with pin_count 0");
            return 0;
        }

        old - 1
    }

    /// Returns true if this frame can be evicted (pin_count == 0).
    #[allow(dead_code)]
    pub fn is_evictable(&self) -> bool {
        self.pin_count() == 0
    }

    /// Acquires a read lock on the page data.
    pub async fn read(&self) -> tokio::sync::RwLockReadGuard<'_, PageData> {
        self.data.read().await
    }

    /// Acquires a write lock on the page data.
    pub async fn write(&self) -> tokio::sync::RwLockWriteGuard<'_, PageData> {
        self.data.write().await
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
    fn test_frame_id() {
        let frame_id = FrameId::new(42);
        assert_eq!(frame_id.index(), 42);
    }

    #[test]
    fn test_frame_new() {
        let frame = Frame::new();
        assert_eq!(frame.page_id(), None);
        assert!(!frame.is_dirty());
        assert_eq!(frame.pin_count(), 0);
        assert!(frame.is_evictable());
    }

    #[test]
    fn test_frame_page_id() {
        let frame = Frame::new();
        assert_eq!(frame.page_id(), None);

        frame.set_page_id(Some(PageId::new(123)));
        assert_eq!(frame.page_id(), Some(PageId::new(123)));

        frame.set_page_id(None);
        assert_eq!(frame.page_id(), None);
    }

    #[test]
    fn test_frame_dirty() {
        let frame = Frame::new();
        assert!(!frame.is_dirty());

        frame.mark_dirty();
        assert!(frame.is_dirty());

        frame.clear_dirty();
        assert!(!frame.is_dirty());
    }

    #[test]
    fn test_frame_pin_unpin() {
        let frame = Frame::new();
        assert_eq!(frame.pin_count(), 0);
        assert!(frame.is_evictable());

        let count = frame.pin();
        assert_eq!(count, 1);
        assert_eq!(frame.pin_count(), 1);
        assert!(!frame.is_evictable());

        let count = frame.pin();
        assert_eq!(count, 2);

        let count = frame.unpin();
        assert_eq!(count, 1);

        let count = frame.unpin();
        assert_eq!(count, 0);
        assert!(frame.is_evictable());
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn test_frame_unpin_underflow() {
        // Underflow protection: unpin on already-0 count returns 0
        // Only tested in release mode to avoid debug_assert! panic
        let frame = Frame::new();
        assert_eq!(frame.pin_count(), 0);

        // Should not panic, should return 0 and keep count at 0
        let count = frame.unpin();
        assert_eq!(count, 0);
        assert_eq!(frame.pin_count(), 0);
    }

    #[tokio::test]
    async fn test_frame_read_write_lock() {
        let frame = Frame::new();

        // Write some data
        {
            let mut guard = frame.write().await;
            guard.as_mut_slice()[0] = 42;
        }

        // Read it back
        {
            let guard = frame.read().await;
            assert_eq!(guard.as_slice()[0], 42);
        }

        // Multiple readers can coexist
        {
            let _guard1 = frame.read().await;
            let _guard2 = frame.read().await;
        }
    }
}
