//! Buffer pool errors.

use crate::storage::{PageId, StorageError};

/// Errors that can occur during buffer pool operations.
#[derive(Debug)]
pub enum BufferPoolError {
    /// No free frames available and all pages are pinned.
    ///
    /// This occurs when the buffer pool is full and no pages can be evicted
    /// because they are all currently in use (pin_count > 0).
    NoFreeFrames,

    /// The requested page does not exist in storage.
    PageNotFound(PageId),

    /// Underlying storage I/O error.
    Storage(StorageError),

    /// Internal invariant violation (should not happen in correct usage).
    InternalError(String),
}

impl std::fmt::Display for BufferPoolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BufferPoolError::NoFreeFrames => {
                write!(f, "no free frames available and all pages are pinned")
            }
            BufferPoolError::PageNotFound(page_id) => {
                write!(f, "page not found: {:?}", page_id)
            }
            BufferPoolError::Storage(e) => {
                write!(f, "storage error: {}", e)
            }
            BufferPoolError::InternalError(msg) => {
                write!(f, "internal error: {}", msg)
            }
        }
    }
}

impl std::error::Error for BufferPoolError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            BufferPoolError::Storage(e) => Some(e),
            _ => None,
        }
    }
}

impl From<StorageError> for BufferPoolError {
    fn from(e: StorageError) -> Self {
        match e {
            StorageError::PageNotFound(id) => BufferPoolError::PageNotFound(id),
            other => BufferPoolError::Storage(other),
        }
    }
}
