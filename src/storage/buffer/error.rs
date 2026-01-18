//! Buffer Pool Manager error types.

use crate::storage::{PageId, StorageError};
use std::fmt;

/// Errors that can occur during buffer pool operations.
#[derive(Debug)]
pub enum BufferPoolError {
    /// The requested page does not exist in storage.
    PageNotFound(PageId),

    /// No free frames available and all frames are pinned.
    ///
    /// This error occurs when the buffer pool is full and eviction cannot proceed
    /// because all frames have `pin_count > 0`.
    ///
    /// # Week 7 Limitation
    ///
    /// In Week 7, eviction is not implemented. This error occurs when the free_list
    /// is empty, even if some frames are unpinned.
    ///
    /// # Week 8 Evolution
    ///
    /// In Week 8, the LRU Replacer will enable eviction of unpinned frames, reducing
    /// the frequency of this error.
    NoFreeFrames,

    /// Underlying storage I/O error.
    Storage(StorageError),
}

impl fmt::Display for BufferPoolError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PageNotFound(page_id) => {
                write!(f, "Page {:?} not found in storage", page_id)
            }
            Self::NoFreeFrames => {
                write!(f, "No free frames available in buffer pool")
            }
            Self::Storage(err) => {
                write!(f, "Storage error: {}", err)
            }
        }
    }
}

impl std::error::Error for BufferPoolError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Storage(err) => Some(err),
            _ => None,
        }
    }
}

impl From<StorageError> for BufferPoolError {
    fn from(err: StorageError) -> Self {
        match err {
            StorageError::PageNotFound(page_id) => Self::PageNotFound(page_id),
            _ => Self::Storage(err),
        }
    }
}

// NOTE: For production, consider adding more specific error variants:
// - FrameEvictionFailed: WAL not flushed before evicting dirty page
// - InvalidPageState: Internal consistency check failure
// - LatchTimeout: Failed to acquire page latch within timeout
