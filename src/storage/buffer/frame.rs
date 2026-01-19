//! Buffer pool frame metadata and indexing.
//!
//! A frame is an in-memory slot that can hold one page. The buffer pool
//! maintains a fixed number of frames (each containing `RwLock<PageData>`)
//! and maps pages to frames on demand.

use crate::storage::PageId;

/// Index into the frame table (0..pool_size).
pub type FrameId = usize;

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
#[derive(Debug, Clone, Copy)]
pub struct FrameMetadata {
    /// The PageId currently stored in this frame, if valid.
    ///
    /// `None` indicates this frame is empty and available for use.
    pub page_id: Option<PageId>,

    /// Number of active pins (references) to this frame.
    ///
    /// A frame with `pin_count > 0` cannot be evicted. Each `fetch_page`
    /// increments this counter, and each `PageGuard` drop decrements it.
    pub pin_count: u32,

    /// Whether the page has been modified since it was read from storage.
    ///
    /// Dirty pages must be written back to storage before eviction.
    pub is_dirty: bool,
}

impl FrameMetadata {
    pub fn vacant() -> Self {
        Self {
            page_id: None,
            pin_count: 0,
            is_dirty: false,
        }
    }

    pub fn occupied(page_id: PageId) -> Self {
        Self {
            page_id: Some(page_id),
            pin_count: 1,
            is_dirty: false,
        }
    }
}

impl Default for FrameMetadata {
    fn default() -> Self {
        Self::vacant()
    }
}
