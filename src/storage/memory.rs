//! In-memory storage implementation for testing.

use std::collections::HashMap;
use std::sync::Mutex;

use crate::storage::{PageId, Storage, StorageError, PAGE_SIZE};

/// In-memory storage implementation for testing.
///
/// Uses a `HashMap<PageId, Box<[u8; PAGE_SIZE]>>` protected by a `Mutex` for
/// thread safety. This implementation is not persistent - all data is lost
/// when dropped.
///
/// # Concurrency
///
/// Uses `std::sync::Mutex` (not `tokio::sync::Mutex`) because:
/// 1. Operations are fast (just HashMap access and memory copies)
/// 2. No I/O blocking occurs within the lock
/// 3. Avoids async overhead for simple operations
///
/// # NOTE: Production considerations
/// - Could use RwLock for better read concurrency
/// - Could partition pages across multiple maps to reduce contention
pub struct MemoryStorage {
    /// Raw page data: PageId -> [u8; PAGE_SIZE]
    pages: Mutex<HashMap<PageId, Box<[u8; PAGE_SIZE]>>>,
    /// Next page ID to allocate
    next_page_id: Mutex<u64>,
    /// Optional maximum page count (for testing storage full scenarios)
    max_pages: Option<u64>,
}

impl MemoryStorage {
    /// Creates a new empty memory storage.
    pub fn new() -> Self {
        Self {
            pages: Mutex::new(HashMap::new()),
            next_page_id: Mutex::new(0),
            max_pages: None,
        }
    }

    /// Creates a new memory storage with a maximum page limit.
    ///
    /// This is useful for testing `StorageFull` error scenarios.
    pub fn with_max_pages(max_pages: u64) -> Self {
        Self {
            pages: Mutex::new(HashMap::new()),
            next_page_id: Mutex::new(0),
            max_pages: Some(max_pages),
        }
    }
}

impl Default for MemoryStorage {
    fn default() -> Self {
        Self::new()
    }
}

impl Storage for MemoryStorage {
    async fn read_page(&self, page_id: PageId, buf: &mut [u8]) -> Result<(), StorageError> {
        // Validate buffer size
        if buf.len() != PAGE_SIZE {
            return Err(StorageError::InvalidBufferSize {
                expected: PAGE_SIZE,
                actual: buf.len(),
            });
        }

        let pages = self.pages.lock().expect("lock poisoned");
        let page = pages
            .get(&page_id)
            .ok_or(StorageError::PageNotFound(page_id))?;

        buf.copy_from_slice(&**page);
        Ok(())
    }

    async fn write_page(&self, page_id: PageId, buf: &[u8]) -> Result<(), StorageError> {
        // Validate buffer size
        if buf.len() != PAGE_SIZE {
            return Err(StorageError::InvalidBufferSize {
                expected: PAGE_SIZE,
                actual: buf.len(),
            });
        }

        let mut pages = self.pages.lock().expect("lock poisoned");
        let page = pages
            .get_mut(&page_id)
            .ok_or(StorageError::InvalidPageId(page_id))?;

        page.copy_from_slice(buf);
        Ok(())
    }

    async fn allocate_page(&self) -> Result<PageId, StorageError> {
        let mut next_id = self.next_page_id.lock().expect("lock poisoned");

        // Check max pages limit
        if let Some(max) = self.max_pages
            && *next_id >= max
        {
            return Err(StorageError::StorageFull);
        }

        let page_id = PageId::new(*next_id);
        *next_id += 1;

        // Initialize page with zeros
        let mut pages = self.pages.lock().expect("lock poisoned");
        pages.insert(page_id, Box::new([0u8; PAGE_SIZE]));

        Ok(page_id)
    }

    async fn page_count(&self) -> u64 {
        *self.next_page_id.lock().expect("lock poisoned")
    }

    async fn sync_all(&self) -> Result<(), StorageError> {
        // No-op for memory storage - data is already in memory
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_allocate_and_read() {
        let storage = MemoryStorage::new();

        let page_id = storage.allocate_page().await.unwrap();
        assert_eq!(page_id, PageId::new(0));

        let mut buf = [0u8; PAGE_SIZE];
        storage.read_page(page_id, &mut buf).await.unwrap();
        assert!(buf.iter().all(|&b| b == 0));
    }

    #[tokio::test]
    async fn test_write_and_read() {
        let storage = MemoryStorage::new();
        let page_id = storage.allocate_page().await.unwrap();

        // Write data
        let mut write_buf = [0u8; PAGE_SIZE];
        write_buf[0..4].copy_from_slice(&[1, 2, 3, 4]);
        storage.write_page(page_id, &write_buf).await.unwrap();

        // Read back
        let mut read_buf = [0u8; PAGE_SIZE];
        storage.read_page(page_id, &mut read_buf).await.unwrap();
        assert_eq!(&read_buf[0..4], &[1, 2, 3, 4]);
        assert_eq!(&read_buf[4..8], &[0, 0, 0, 0]);
    }

    #[tokio::test]
    async fn test_read_unallocated_page() {
        let storage = MemoryStorage::new();
        let mut buf = [0u8; PAGE_SIZE];
        let result = storage.read_page(PageId::new(0), &mut buf).await;
        assert!(matches!(result, Err(StorageError::PageNotFound(_))));
    }

    #[tokio::test]
    async fn test_write_unallocated_page() {
        let storage = MemoryStorage::new();
        let buf = [0u8; PAGE_SIZE];
        let result = storage.write_page(PageId::new(0), &buf).await;
        assert!(matches!(result, Err(StorageError::InvalidPageId(_))));
    }

    #[tokio::test]
    async fn test_page_count() {
        let storage = MemoryStorage::new();
        assert_eq!(storage.page_count().await, 0);

        storage.allocate_page().await.unwrap();
        assert_eq!(storage.page_count().await, 1);

        storage.allocate_page().await.unwrap();
        assert_eq!(storage.page_count().await, 2);
    }

    #[tokio::test]
    async fn test_storage_full() {
        let storage = MemoryStorage::with_max_pages(2);

        storage.allocate_page().await.unwrap();
        storage.allocate_page().await.unwrap();

        let result = storage.allocate_page().await;
        assert!(matches!(result, Err(StorageError::StorageFull)));
    }

    #[tokio::test]
    async fn test_invalid_buffer_size_read() {
        let storage = MemoryStorage::new();
        let page_id = storage.allocate_page().await.unwrap();

        let mut buf = [0u8; 100]; // Wrong size
        let result = storage.read_page(page_id, &mut buf).await;
        assert!(matches!(
            result,
            Err(StorageError::InvalidBufferSize { expected: PAGE_SIZE, actual: 100 })
        ));
    }

    #[tokio::test]
    async fn test_invalid_buffer_size_write() {
        let storage = MemoryStorage::new();
        let page_id = storage.allocate_page().await.unwrap();

        let buf = [0u8; 100]; // Wrong size
        let result = storage.write_page(page_id, &buf).await;
        assert!(matches!(
            result,
            Err(StorageError::InvalidBufferSize { expected: PAGE_SIZE, actual: 100 })
        ));
    }

    #[tokio::test]
    async fn test_sync_all() {
        let storage = MemoryStorage::new();
        // Should be a no-op and not error
        storage.sync_all().await.unwrap();
    }

    #[tokio::test]
    async fn test_multiple_pages() {
        let storage = MemoryStorage::new();

        // Allocate multiple pages
        let id0 = storage.allocate_page().await.unwrap();
        let id1 = storage.allocate_page().await.unwrap();
        let id2 = storage.allocate_page().await.unwrap();

        // Write distinct data to each
        for (id, value) in [(id0, 10u8), (id1, 20u8), (id2, 30u8)] {
            let mut buf = [0u8; PAGE_SIZE];
            buf[0] = value;
            storage.write_page(id, &buf).await.unwrap();
        }

        // Read back and verify
        let mut buf = [0u8; PAGE_SIZE];
        storage.read_page(id0, &mut buf).await.unwrap();
        assert_eq!(buf[0], 10);

        storage.read_page(id1, &mut buf).await.unwrap();
        assert_eq!(buf[0], 20);

        storage.read_page(id2, &mut buf).await.unwrap();
        assert_eq!(buf[0], 30);
    }
}
