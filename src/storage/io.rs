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

/// Generic test functions for Storage implementations.
///
/// Each implementation module should import these and call them in their own tests.
#[cfg(test)]
mod tests {
    use super::Storage;
    use crate::storage::{PAGE_SIZE, PageId, StorageError};
    use std::sync::Arc;

    /// Write a single byte value to a page.
    pub async fn write_test_data<S: Storage>(storage: &S, page_id: PageId, value: u8) {
        let mut buf = [0u8; PAGE_SIZE];
        buf[0] = value;
        storage.write_page(page_id, &buf).await.unwrap();
    }

    /// Verify the first byte of a page matches expected value.
    pub async fn verify_test_data<S: Storage>(storage: &S, page_id: PageId, expected: u8) {
        let mut buf = [0u8; PAGE_SIZE];
        storage.read_page(page_id, &mut buf).await.unwrap();
        assert_eq!(buf[0], expected);
    }

    /// Allocate a page and write a test value to it.
    pub async fn allocate_and_write<S: Storage>(storage: &S, value: u8) -> PageId {
        let page_id = storage.allocate_page().await.unwrap();
        write_test_data(storage, page_id, value).await;
        page_id
    }

    /// Test basic operations: allocate, write, read, page_count, sync_all.
    pub async fn test_basic_operations<S: Storage>(storage: S) {
        assert_eq!(storage.page_count().await, 0);

        let id0 = allocate_and_write(&storage, 10).await;
        let id1 = allocate_and_write(&storage, 20).await;
        let id2 = allocate_and_write(&storage, 30).await;

        assert_eq!(id0.page_num(), 0);
        assert_eq!(id1.page_num(), 1);
        assert_eq!(id2.page_num(), 2);
        assert_eq!(storage.page_count().await, 3);

        verify_test_data(&storage, id0, 10).await;
        verify_test_data(&storage, id1, 20).await;
        verify_test_data(&storage, id2, 30).await;

        storage.sync_all().await.unwrap();
    }

    /// Test concurrent writes to different pages.
    pub async fn test_concurrent_access<S: Storage + 'static>(storage: S) {
        let storage = Arc::new(storage);
        let mut page_ids = vec![];
        for _ in 0..10 {
            page_ids.push(storage.allocate_page().await.unwrap());
        }

        let mut handles = vec![];
        for (i, page_id) in page_ids.iter().enumerate() {
            let storage = storage.clone();
            let page_id = *page_id;
            handles.push(tokio::spawn(async move {
                write_test_data(&*storage, page_id, i as u8).await;
            }));
        }

        for handle in handles {
            handle.await.unwrap();
        }

        storage.sync_all().await.unwrap();

        for (i, page_id) in page_ids.iter().enumerate() {
            verify_test_data(&*storage, *page_id, i as u8).await;
        }
    }

    /// Test buffer size validation for read and write.
    pub async fn test_buffer_size_validation<S: Storage>(storage: S) {
        let page_id = storage.allocate_page().await.unwrap();

        let mut small_buf = [0u8; 100];
        let result = storage.read_page(page_id, &mut small_buf).await;
        assert!(matches!(
            result,
            Err(StorageError::InvalidBufferSize {
                expected: PAGE_SIZE,
                actual: 100
            })
        ));

        let small_buf = [0u8; 100];
        let result = storage.write_page(page_id, &small_buf).await;
        assert!(matches!(
            result,
            Err(StorageError::InvalidBufferSize {
                expected: PAGE_SIZE,
                actual: 100
            })
        ));
    }

    /// Test reading/writing unallocated pages returns PageNotFound.
    pub async fn test_page_not_found<S: Storage>(storage: S) {
        let mut buf = [0u8; PAGE_SIZE];
        let result = storage.read_page(PageId::new(0), &mut buf).await;
        assert!(matches!(result, Err(StorageError::PageNotFound(_))));

        let buf = [0u8; PAGE_SIZE];
        let result = storage.write_page(PageId::new(0), &buf).await;
        assert!(matches!(result, Err(StorageError::PageNotFound(_))));
    }
}
