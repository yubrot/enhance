//! Buffer pool frame representation.
//!
//! A frame is an in-memory slot that can hold one page. The buffer pool
//! maintains a fixed number of frames and maps pages to frames on demand.

use tokio::sync::RwLock;

use crate::storage::{PageData, PageId};

/// Index into the frame table (0..pool_size).
pub type FrameId = usize;

/// A buffer pool frame holding page data.
///
/// Each frame contains exactly one page's worth of data (8KB). The data
/// is protected by an `RwLock` to allow concurrent read access while
/// ensuring exclusive write access.
///
/// # Thread Safety
///
/// The `data` field is protected by `tokio::sync::RwLock` for async access.
/// Frame metadata (page_id, pin_count, is_dirty) is stored separately in
/// `FrameMetadata` and protected by the buffer pool's state lock.
///
/// NOTE: For production, consider using `parking_lot::RwLock` for
/// synchronous access patterns, which avoids the overhead of async locks
/// when the critical section is short and non-blocking.
pub struct Frame {
    /// The page data protected by an async RwLock.
    ///
    /// The RwLock allows multiple concurrent readers or one exclusive writer.
    pub(crate) data: RwLock<PageData>,
}

impl Frame {
    /// Creates a new frame with zero-initialized page data.
    pub fn new() -> Self {
        Self {
            data: RwLock::new(PageData::new()),
        }
    }
}

impl Default for Frame {
    fn default() -> Self {
        Self::new()
    }
}

/// Metadata for a buffer pool frame.
///
/// This metadata is stored separately from the frame data and is protected
/// by the buffer pool's state lock. This design allows metadata updates
/// (pin_count, is_dirty) without holding the frame's data lock.
///
/// # Fields
///
/// - `page_id`: The PageId currently stored in this frame, or None if empty.
/// - `pin_count`: Number of active references to this frame.
/// - `is_dirty`: Whether the page has been modified since loaded from storage.
#[derive(Debug, Clone)]
pub struct FrameMetadata {
    /// The PageId currently stored in this frame, if valid.
    ///
    /// `None` indicates this frame is empty and available for use.
    pub(crate) page_id: Option<PageId>,

    /// Number of active pins (references) to this frame.
    ///
    /// A frame with `pin_count > 0` cannot be evicted. Each `fetch_page`
    /// increments this counter, and each `PageGuard` drop decrements it.
    pub(crate) pin_count: u32,

    /// Whether the page has been modified since it was read from storage.
    ///
    /// Dirty pages must be written back to storage before eviction.
    pub(crate) is_dirty: bool,
}

impl FrameMetadata {
    /// Creates new metadata for an empty frame.
    pub fn new() -> Self {
        Self {
            page_id: None,
            pin_count: 0,
            is_dirty: false,
        }
    }

    /// Returns true if this frame contains valid page data.
    #[allow(dead_code)]
    pub fn is_valid(&self) -> bool {
        self.page_id.is_some()
    }

    /// Returns true if this frame can be evicted (not pinned).
    #[allow(dead_code)]
    pub fn is_evictable(&self) -> bool {
        self.pin_count == 0
    }

    /// Resets the metadata to empty state (after eviction).
    pub fn reset(&mut self) {
        self.page_id = None;
        self.pin_count = 0;
        self.is_dirty = false;
    }
}

impl Default for FrameMetadata {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_frame_metadata_new() {
        let meta = FrameMetadata::new();
        assert!(!meta.is_valid());
        assert!(meta.is_evictable());
        assert_eq!(meta.pin_count, 0);
        assert!(!meta.is_dirty);
    }

    #[test]
    fn test_frame_metadata_is_valid() {
        let mut meta = FrameMetadata::new();
        assert!(!meta.is_valid());

        meta.page_id = Some(PageId::new(42));
        assert!(meta.is_valid());
    }

    #[test]
    fn test_frame_metadata_is_evictable() {
        let mut meta = FrameMetadata::new();
        assert!(meta.is_evictable());

        meta.pin_count = 1;
        assert!(!meta.is_evictable());

        meta.pin_count = 0;
        assert!(meta.is_evictable());
    }

    #[test]
    fn test_frame_metadata_reset() {
        let mut meta = FrameMetadata::new();
        meta.page_id = Some(PageId::new(1));
        meta.pin_count = 5;
        meta.is_dirty = true;

        meta.reset();

        assert!(!meta.is_valid());
        assert_eq!(meta.pin_count, 0);
        assert!(!meta.is_dirty);
    }

    #[tokio::test]
    async fn test_frame_new() {
        let frame = Frame::new();
        let data = frame.data.read().await;
        assert_eq!(data.as_slice().len(), crate::storage::PAGE_SIZE);
        // Data should be zero-initialized
        assert!(data.as_slice().iter().all(|&b| b == 0));
    }
}
