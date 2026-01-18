//! Page I/O backend implementations.
//!
//! This module provides the `Storage` trait for page-based I/O operations,
//! along with MemoryStorage and FileStorage implementations.

mod file;
mod memory;

pub use file::FileStorage;
pub use memory::MemoryStorage;

use super::page::PageId;
use crate::storage::error::StorageError;

/// Page I/O backend trait for page-based storage.
///
/// This trait defines the interface for reading and writing 8KB pages using
/// caller-owned buffers. Implementations include:
/// - `io::MemoryStorage`: In-memory storage
/// - `io::FileStorage`: Disk-backed storage using tokio::fs
///
/// # Design Decisions
///
/// 1. **Async trait**: Uses `async fn` (Rust 1.75+) for compatibility with tokio.
///    File I/O is inherently blocking, so FileStorage will use spawn_blocking or
///    tokio::fs for async I/O.
///
/// 2. **Caller-owned buffers**: Storage is responsible for reading and writing
///    raw bytes only. Memory management is the responsibility of the caller
///    (typically the Buffer Pool Manager in Week 7-8).
///
/// 3. **Page-level operations**: All I/O is page-sized (8KB) for alignment with
///    OS page sizes and efficient disk I/O.
///
/// 4. **Explicit allocation**: `allocate_page()` grows the storage. This allows
///    the storage to track total pages and pre-allocate space.
///
/// 5. **No caching**: This layer does not cache pages. Caching is the responsibility
///    of the Buffer Pool Manager (Week 7-8).
///
/// # Thread Safety
///
/// Implementations must be thread-safe (Sync + Send). The Buffer Pool Manager
/// will handle page-level locking; this trait handles only raw I/O.
pub trait Storage: Send + Sync {
    /// Reads a page into caller-provided buffer.
    ///
    /// # Arguments
    ///
    /// * `page_id` - The page identifier to read
    /// * `buf` - Buffer to read into (must be exactly PAGE_SIZE bytes)
    ///
    /// # Errors
    ///
    /// Returns `StorageError::PageNotFound` if the page has not been allocated.
    /// Returns `StorageError::InvalidBufferSize` if `buf.len() != PAGE_SIZE`.
    fn read_page(
        &self,
        page_id: PageId,
        buf: &mut [u8],
    ) -> impl std::future::Future<Output = Result<(), StorageError>> + Send;

    /// Writes a page from caller-provided buffer.
    ///
    /// # Arguments
    ///
    /// * `page_id` - The page identifier to write
    /// * `buf` - Buffer to write from (must be exactly PAGE_SIZE bytes)
    ///
    /// # Errors
    ///
    /// Returns `StorageError::PageNotFound` if the page has not been allocated.
    /// Returns `StorageError::InvalidBufferSize` if `buf.len() != PAGE_SIZE`.
    fn write_page(
        &self,
        page_id: PageId,
        buf: &[u8],
    ) -> impl std::future::Future<Output = Result<(), StorageError>> + Send;

    /// Allocates a new page and returns its PageId.
    ///
    /// The new page is initialized to zeros.
    ///
    /// # Page ID Allocation
    ///
    /// The first call to `allocate_page()` on an empty storage is guaranteed to
    /// return `PageId(0)`. The order of subsequent allocations is implementation-defined.
    ///
    /// # Errors
    ///
    /// Returns `StorageError::StorageFull` if storage limit is reached.
    fn allocate_page(
        &self,
    ) -> impl std::future::Future<Output = Result<PageId, StorageError>> + Send;

    /// Returns the total number of allocated pages.
    fn page_count(&self) -> impl std::future::Future<Output = usize> + Send;

    /// Syncs all pending writes to physical disk (fsync).
    ///
    /// For io::MemoryStorage, this is a no-op.
    /// For io::FileStorage, this calls `sync_all()` to ensure durability.
    ///
    /// This method makes the distinction between:
    /// - Memory → OS buffer: write (implicit)
    /// - OS buffer → physical disk: sync_all (explicit)
    fn sync_all(&self) -> impl std::future::Future<Output = Result<(), StorageError>> + Send;
}
