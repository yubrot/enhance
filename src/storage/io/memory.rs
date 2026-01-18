//! In-memory page storage implementation.
//!
//! NOTE: This implementation uses `unwrap()` on Mutex locks for simplicity.
//! For production:
//! - Use `parking_lot::Mutex` which doesn't poison on panic
//! - Or handle `PoisonError` by recovering or propagating as `StorageError`

use std::sync::Mutex;

use super::Storage;
use crate::storage::error::StorageError;
use crate::storage::page::PageData;
use crate::storage::page::{PAGE_SIZE, PageId};

/// In-memory page storage for testing and development.
///
/// Stores pages in a Vec backed by aligned memory allocations.
/// PageIds are assigned sequentially as Vec indices.
/// All operations are synchronous but wrapped in async for trait compatibility.
pub struct MemoryStorage {
    pages: Mutex<Vec<PageData>>,
}

impl MemoryStorage {
    /// Creates a new empty in-memory storage.
    pub fn new() -> Self {
        Self {
            pages: Mutex::new(Vec::new()),
        }
    }
}

impl Storage for MemoryStorage {
    async fn read_page(&self, page_id: PageId, buf: &mut [u8]) -> Result<(), StorageError> {
        if buf.len() != PAGE_SIZE {
            return Err(StorageError::InvalidBufferSize {
                expected: PAGE_SIZE,
                actual: buf.len(),
            });
        }

        let pages = self.pages.lock().unwrap();
        let page = pages
            .get(page_id.page_num() as usize)
            .ok_or(StorageError::PageNotFound(page_id))?;

        buf.copy_from_slice(page.as_slice());
        Ok(())
    }

    async fn write_page(&self, page_id: PageId, buf: &[u8]) -> Result<(), StorageError> {
        if buf.len() != PAGE_SIZE {
            return Err(StorageError::InvalidBufferSize {
                expected: PAGE_SIZE,
                actual: buf.len(),
            });
        }

        let mut pages = self.pages.lock().unwrap();
        let page = pages
            .get_mut(page_id.page_num() as usize)
            .ok_or(StorageError::PageNotFound(page_id))?;

        page.as_mut_slice().copy_from_slice(buf);
        Ok(())
    }

    async fn allocate_page(&self) -> Result<PageId, StorageError> {
        let mut pages = self.pages.lock().unwrap();
        let page_id = PageId::new(pages.len() as u64);
        pages.push(PageData::new());
        Ok(page_id)
    }

    async fn page_count(&self) -> usize {
        self.pages.lock().unwrap().len()
    }

    async fn sync_all(&self) -> Result<(), StorageError> {
        // No-op for in-memory storage
        Ok(())
    }
}

impl Default for MemoryStorage {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_allocate_and_read() {
        let storage = MemoryStorage::new();
        let page_id = storage.allocate_page().await.unwrap();
        let mut buf = vec![0u8; PAGE_SIZE];
        storage.read_page(page_id, &mut buf).await.unwrap();
        assert!(buf.iter().all(|&b| b == 0));
    }

    #[tokio::test]
    async fn test_write_and_read() {
        let storage = MemoryStorage::new();
        let page_id = storage.allocate_page().await.unwrap();

        let mut write_buf = vec![0u8; PAGE_SIZE];
        write_buf[0] = 42;
        write_buf[100] = 99;
        storage.write_page(page_id, &write_buf).await.unwrap();

        let mut read_buf = vec![0u8; PAGE_SIZE];
        storage.read_page(page_id, &mut read_buf).await.unwrap();
        assert_eq!(read_buf[0], 42);
        assert_eq!(read_buf[100], 99);
    }

    #[tokio::test]
    async fn test_page_not_found() {
        let storage = MemoryStorage::new();
        let mut buf = vec![0u8; PAGE_SIZE];
        let result = storage.read_page(PageId::new(999), &mut buf).await;
        assert!(matches!(result, Err(StorageError::PageNotFound(_))));
    }

    #[tokio::test]
    async fn test_invalid_buffer_size() {
        let storage = MemoryStorage::new();
        let page_id = storage.allocate_page().await.unwrap();
        let mut buf = vec![0u8; 100];
        let result = storage.read_page(page_id, &mut buf).await;
        assert!(matches!(
            result,
            Err(StorageError::InvalidBufferSize { .. })
        ));
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
    async fn test_sync_all() {
        let storage = MemoryStorage::new();
        // Should not panic
        storage.sync_all().await.unwrap();
    }
}
