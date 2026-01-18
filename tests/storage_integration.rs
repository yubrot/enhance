//! Integration tests for storage layer.

use enhance::storage::{FileStorage, MemoryStorage, PAGE_SIZE, PageId, Storage, StorageError};
use std::sync::Arc;
use tempfile::{TempDir, tempdir};

/// Helper for creating temporary FileStorage instances for testing.
struct TempFileStorage {
    dir: TempDir,
}

impl TempFileStorage {
    async fn new() -> Self {
        let dir = tempdir().unwrap();
        Self { dir }
    }

    async fn storage(&self) -> FileStorage {
        FileStorage::open(self.dir.path().join("test.db"))
            .await
            .unwrap()
    }
}

/// Helper: Write test data (single byte value) to a page.
async fn write_test_data<S: Storage>(storage: &S, page_id: PageId, value: u8) {
    let mut buf = [0u8; PAGE_SIZE];
    buf[0] = value;
    storage.write_page(page_id, &buf).await.unwrap();
}

/// Helper: Read a page and verify the first byte matches expected value.
async fn verify_test_data<S: Storage>(storage: &S, page_id: PageId, expected: u8) {
    let mut buf = [0u8; PAGE_SIZE];
    storage.read_page(page_id, &mut buf).await.unwrap();
    assert_eq!(buf[0], expected);
}

/// Helper: Allocate a page and write test data to it.
async fn allocate_and_write<S: Storage>(storage: &S, value: u8) -> PageId {
    let page_id = storage.allocate_page().await.unwrap();
    write_test_data(storage, page_id, value).await;
    page_id
}

/// Generic test runner for any Storage implementation.
async fn test_storage_basic_operations<S: Storage>(storage: S) {
    // Initially empty
    assert_eq!(storage.page_count().await, 0);

    // Allocate and write to multiple pages
    let id0 = allocate_and_write(&storage, 10).await;
    let id1 = allocate_and_write(&storage, 20).await;
    let id2 = allocate_and_write(&storage, 30).await;

    assert_eq!(id0.page_num(), 0);
    assert_eq!(id1.page_num(), 1);
    assert_eq!(id2.page_num(), 2);
    assert_eq!(storage.page_count().await, 3);

    // Read back and verify
    verify_test_data(&storage, id0, 10).await;
    verify_test_data(&storage, id1, 20).await;
    verify_test_data(&storage, id2, 30).await;

    // sync_all should succeed
    storage.sync_all().await.unwrap();
}

#[tokio::test]
async fn test_memory_storage_basic() {
    test_storage_basic_operations(MemoryStorage::new()).await;
}

#[tokio::test]
async fn test_file_storage_basic() {
    let temp_storage = TempFileStorage::new().await;
    test_storage_basic_operations(temp_storage.storage().await).await;
}

/// Generic test for concurrent access (important for Buffer Pool Manager integration).
async fn test_storage_concurrent_access<S: Storage + 'static>(storage: S) {
    let storage = Arc::new(storage);

    // Allocate pages first and collect their IDs
    let mut page_ids = vec![];
    for _ in 0..10 {
        page_ids.push(storage.allocate_page().await.unwrap());
    }

    // Spawn multiple tasks writing to different pages
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

    // Verify all writes using the allocated page IDs
    for (i, page_id) in page_ids.iter().enumerate() {
        verify_test_data(&*storage, *page_id, i as u8).await;
    }
}

#[tokio::test]
async fn test_memory_storage_concurrent() {
    test_storage_concurrent_access(MemoryStorage::new()).await;
}

#[tokio::test]
async fn test_file_storage_concurrent() {
    let temp_storage = TempFileStorage::new().await;
    test_storage_concurrent_access(temp_storage.storage().await).await;
}

/// Generic test for buffer size validation.
async fn test_storage_buffer_size_validation<S: Storage>(storage: S) {
    let page_id = storage.allocate_page().await.unwrap();

    // Wrong size for read
    let mut small_buf = [0u8; 100];
    let result = storage.read_page(page_id, &mut small_buf).await;
    assert!(matches!(
        result,
        Err(StorageError::InvalidBufferSize {
            expected: PAGE_SIZE,
            actual: 100
        })
    ));

    // Wrong size for write
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

#[tokio::test]
async fn test_memory_storage_buffer_size_validation() {
    test_storage_buffer_size_validation(MemoryStorage::new()).await;
}

#[tokio::test]
async fn test_file_storage_buffer_size_validation() {
    let temp_storage = TempFileStorage::new().await;
    test_storage_buffer_size_validation(temp_storage.storage().await).await;
}

/// Test persistence across multiple File instances.
#[tokio::test]
async fn test_file_persistence_across_instances() {
    let temp_storage = TempFileStorage::new().await;
    let mut page_ids = Vec::new();

    // First instance: allocate and write 5 pages
    {
        let storage = temp_storage.storage().await;
        for i in 0..5 {
            page_ids.push(allocate_and_write(&storage, (i * 10) as u8).await);
        }
        storage.sync_all().await.unwrap();
    }

    // Second instance: verify existing pages
    {
        let storage = temp_storage.storage().await;
        assert_eq!(storage.page_count().await, 5);
        for (i, &page_id) in page_ids.iter().enumerate() {
            verify_test_data(&storage, page_id, (i * 10) as u8).await;
        }
    }

    // Third instance: append 5 more pages
    {
        let storage = temp_storage.storage().await;
        assert_eq!(storage.page_count().await, 5);
        for i in 5..10 {
            page_ids.push(allocate_and_write(&storage, (i * 10) as u8).await);
        }
        storage.sync_all().await.unwrap();
    }

    // Fourth instance: verify all 10 pages
    {
        let storage = temp_storage.storage().await;
        assert_eq!(storage.page_count().await, 10);
        for (i, &page_id) in page_ids.iter().enumerate() {
            verify_test_data(&storage, page_id, (i * 10) as u8).await;
        }
    }
}
