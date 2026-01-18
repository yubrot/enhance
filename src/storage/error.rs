//! Storage layer errors.

use crate::storage::PageId;

/// Storage layer errors.
#[derive(Debug)]
pub enum StorageError {
    /// Page not found in storage.
    ///
    /// This occurs when attempting to read or write a page that has not been
    /// allocated yet. Use `allocate_page` to create new pages.
    PageNotFound(PageId),

    /// Invalid buffer size provided to read_page or write_page.
    ///
    /// Buffers must be exactly PAGE_SIZE bytes.
    InvalidBufferSize {
        /// Expected buffer size (PAGE_SIZE)
        expected: usize,
        /// Actual buffer size provided
        actual: usize,
    },

    /// I/O error from underlying file system.
    Io(std::io::Error),

    /// Storage is full (cannot allocate new pages).
    ///
    /// This is primarily used by MemoryStorage with max_pages limit for testing.
    /// FileStorage may return this if the file system is full.
    ///
    /// NOTE: Currently unused. For production implementation:
    /// - MemoryStorage: Add `max_pages` limit in constructor
    /// - FileStorage: Check available disk space or set max file size
    /// - Buffer Pool: Return this when all frames are pinned and no eviction possible
    StorageFull,

    /// Data corruption detected.
    ///
    /// This indicates that the storage file has an invalid format or size.
    Corrupted(String),
}

impl std::fmt::Display for StorageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StorageError::PageNotFound(id) => write!(f, "page not found: {:?}", id),
            StorageError::InvalidBufferSize { expected, actual } => {
                write!(f, "invalid buffer size: expected {}, got {}", expected, actual)
            }
            StorageError::Io(e) => write!(f, "I/O error: {}", e),
            StorageError::StorageFull => write!(f, "storage is full"),
            StorageError::Corrupted(msg) => write!(f, "data corruption: {}", msg),
        }
    }
}

impl std::error::Error for StorageError {}

impl From<std::io::Error> for StorageError {
    fn from(e: std::io::Error) -> Self {
        StorageError::Io(e)
    }
}
