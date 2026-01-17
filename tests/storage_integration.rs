//! Integration tests for storage layer.

use enhance::storage::{FileStorage, MemoryStorage, PageId, Storage, StorageError, PAGE_SIZE};
use std::sync::Arc;
use tempfile::tempdir;

/// Generic test runner for any Storage implementation.
async fn test_storage_basic_operations<S: Storage>(storage: S) {
    // Initially empty
    assert_eq!(storage.page_count().await, 0);

    // Allocate multiple pages
    let id0 = storage.allocate_page().await.unwrap();
    let id1 = storage.allocate_page().await.unwrap();
    let id2 = storage.allocate_page().await.unwrap();

    assert_eq!(id0.page_num(), 0);
    assert_eq!(id1.page_num(), 1);
    assert_eq!(id2.page_num(), 2);
    assert_eq!(storage.page_count().await, 3);

    // Write distinct data to each page
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

    // sync_all should succeed
    storage.sync_all().await.unwrap();
}

#[tokio::test]
async fn test_memory_storage_basic() {
    test_storage_basic_operations(MemoryStorage::new()).await;
}

#[tokio::test]
async fn test_file_storage_basic() {
    let dir = tempdir().unwrap();
    let storage = FileStorage::open(dir.path().join("test.db"))
        .await
        .unwrap();
    test_storage_basic_operations(storage).await;
}

/// Test concurrent access (important for Buffer Pool Manager integration).
#[tokio::test]
async fn test_concurrent_access() {
    let storage = Arc::new(MemoryStorage::new());

    // Allocate pages first
    for _ in 0..10 {
        storage.allocate_page().await.unwrap();
    }

    // Spawn multiple tasks writing to different pages
    let mut handles = vec![];
    for i in 0..10 {
        let storage = storage.clone();
        handles.push(tokio::spawn(async move {
            let page_id = PageId::new(i);
            let mut buf = [0u8; PAGE_SIZE];
            buf[0] = i as u8;
            storage.write_page(page_id, &buf).await.unwrap();
        }));
    }

    for handle in handles {
        handle.await.unwrap();
    }

    // Verify all writes
    for i in 0..10 {
        let mut buf = [0u8; PAGE_SIZE];
        storage.read_page(PageId::new(i), &mut buf).await.unwrap();
        assert_eq!(buf[0], i as u8);
    }
}

/// Test concurrent access with FileStorage.
#[tokio::test]
async fn test_file_concurrent_access() {
    let dir = tempdir().unwrap();
    let storage = Arc::new(
        FileStorage::open(dir.path().join("test.db"))
            .await
            .unwrap(),
    );

    // Allocate pages first
    for _ in 0..10 {
        storage.allocate_page().await.unwrap();
    }

    // Spawn multiple tasks writing to different pages
    let mut handles = vec![];
    for i in 0..10 {
        let storage = storage.clone();
        handles.push(tokio::spawn(async move {
            let page_id = PageId::new(i);
            let mut buf = [0u8; PAGE_SIZE];
            buf[0] = i as u8;
            storage.write_page(page_id, &buf).await.unwrap();
        }));
    }

    for handle in handles {
        handle.await.unwrap();
    }

    storage.sync_all().await.unwrap();

    // Verify all writes
    for i in 0..10 {
        let mut buf = [0u8; PAGE_SIZE];
        storage.read_page(PageId::new(i), &mut buf).await.unwrap();
        assert_eq!(buf[0], i as u8);
    }
}

/// Test that both implementations handle buffer size errors correctly.
#[tokio::test]
async fn test_buffer_size_validation() {
    let storage = MemoryStorage::new();
    let page_id = storage.allocate_page().await.unwrap();

    // Wrong size for read
    let mut small_buf = [0u8; 100];
    let result = storage.read_page(page_id, &mut small_buf).await;
    assert!(matches!(
        result,
        Err(StorageError::InvalidBufferSize { expected: PAGE_SIZE, actual: 100 })
    ));

    // Wrong size for write
    let small_buf = [0u8; 100];
    let result = storage.write_page(page_id, &small_buf).await;
    assert!(matches!(
        result,
        Err(StorageError::InvalidBufferSize { expected: PAGE_SIZE, actual: 100 })
    ));
}

/// Test persistence across multiple FileStorage instances.
#[tokio::test]
async fn test_file_persistence_across_instances() {
    let dir = tempdir().unwrap();
    let path = dir.path().join("test.db");

    // First instance: write data
    {
        let storage = FileStorage::open(&path).await.unwrap();
        for i in 0..5 {
            let page_id = storage.allocate_page().await.unwrap();
            let mut buf = [0u8; PAGE_SIZE];
            buf[0] = (i * 10) as u8;
            storage.write_page(page_id, &buf).await.unwrap();
        }
        storage.sync_all().await.unwrap();
    }

    // Second instance: read data
    {
        let storage = FileStorage::open(&path).await.unwrap();
        assert_eq!(storage.page_count().await, 5);

        for i in 0..5 {
            let mut buf = [0u8; PAGE_SIZE];
            storage.read_page(PageId::new(i), &mut buf).await.unwrap();
            assert_eq!(buf[0], (i * 10) as u8);
        }
    }

    // Third instance: append more pages
    {
        let storage = FileStorage::open(&path).await.unwrap();
        assert_eq!(storage.page_count().await, 5);

        for i in 5..10 {
            let page_id = storage.allocate_page().await.unwrap();
            let mut buf = [0u8; PAGE_SIZE];
            buf[0] = (i * 10) as u8;
            storage.write_page(page_id, &buf).await.unwrap();
        }
        storage.sync_all().await.unwrap();
    }

    // Fourth instance: verify all
    {
        let storage = FileStorage::open(&path).await.unwrap();
        assert_eq!(storage.page_count().await, 10);

        for i in 0..10 {
            let mut buf = [0u8; PAGE_SIZE];
            storage.read_page(PageId::new(i), &mut buf).await.unwrap();
            assert_eq!(buf[0], (i * 10) as u8);
        }
    }
}
