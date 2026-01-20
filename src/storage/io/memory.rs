//! In-memory page storage implementation.

use parking_lot::Mutex;

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

        let pages = self.pages.lock();
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

        let mut pages = self.pages.lock();
        let page = pages
            .get_mut(page_id.page_num() as usize)
            .ok_or(StorageError::PageNotFound(page_id))?;

        page.as_mut_slice().copy_from_slice(buf);
        Ok(())
    }

    async fn allocate_page(&self) -> Result<PageId, StorageError> {
        let mut pages = self.pages.lock();
        let page_id = PageId::new(pages.len() as u64);
        pages.push(PageData::new());
        Ok(page_id)
    }

    async fn page_count(&self) -> usize {
        self.pages.lock().len()
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
    use super::super::tests as generic;
    use super::*;

    #[tokio::test]
    async fn test_basic_operations() {
        generic::test_basic_operations(MemoryStorage::new()).await;
    }

    #[tokio::test]
    async fn test_concurrent_access() {
        generic::test_concurrent_access(MemoryStorage::new()).await;
    }

    #[tokio::test]
    async fn test_buffer_size_validation() {
        generic::test_buffer_size_validation(MemoryStorage::new()).await;
    }

    #[tokio::test]
    async fn test_page_not_found() {
        generic::test_page_not_found(MemoryStorage::new()).await;
    }
}
