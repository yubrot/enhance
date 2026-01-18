//! Buffer pool errors.

use crate::storage::StorageError;

/// Buffer pool errors.
///
/// This error type wraps storage-level errors and adds buffer-pool-specific
/// error conditions.
#[derive(Debug)]
pub enum BufferPoolError {
    /// No free frames available and all pages are pinned.
    ///
    /// This occurs when the buffer pool is full and no unpinned pages
    /// are available for eviction. Either increase the pool size or
    /// ensure pages are being unpinned after use.
    NoFreeFrames,

    /// Underlying storage error.
    ///
    /// This includes `StorageError::PageNotFound` when attempting to fetch
    /// a page that doesn't exist in storage.
    Storage(StorageError),
}

impl std::fmt::Display for BufferPoolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BufferPoolError::NoFreeFrames => {
                write!(f, "buffer pool exhausted: all frames are pinned")
            }
            BufferPoolError::Storage(e) => write!(f, "storage error: {}", e),
        }
    }
}

impl std::error::Error for BufferPoolError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            BufferPoolError::NoFreeFrames => None,
            BufferPoolError::Storage(e) => Some(e),
        }
    }
}

impl From<StorageError> for BufferPoolError {
    fn from(e: StorageError) -> Self {
        BufferPoolError::Storage(e)
    }
}
