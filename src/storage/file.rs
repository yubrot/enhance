//! File-backed storage implementation.

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use tokio::fs::{File, OpenOptions};
use tokio::io::{AsyncReadExt, AsyncSeekExt, AsyncWriteExt};
use tokio::sync::Mutex;

use crate::storage::{PageId, Storage, StorageError, PAGE_SIZE};

/// File-backed storage implementation.
///
/// Stores pages as contiguous 8KB blocks in a single file.
/// Uses `tokio::fs` for async file I/O.
///
/// # File Layout
///
/// ```text
/// +------------------+------------------+------------------+
/// | Page 0 (8KB)     | Page 1 (8KB)     | Page 2 (8KB)     | ...
/// +------------------+------------------+------------------+
/// ^ offset 0         ^ offset 8192      ^ offset 16384
/// ```
///
/// # Concurrency
///
/// Uses a `tokio::Mutex` around the file handle to serialize I/O operations.
///
/// NOTE: For production systems with better concurrency:
/// - Use multiple file handles (one per thread)
/// - Use pread/pwrite for concurrent access to different offsets
/// - Implement Direct I/O to bypass OS cache
///
/// # Durability
///
/// The `sync_all()` method calls `File::sync_all()` to ensure data reaches disk.
/// Without calling sync_all, data may be lost on crash.
pub struct FileStorage {
    /// Path to the storage file
    path: PathBuf,
    /// File handle wrapped in async mutex for serialized access
    file: Mutex<File>,
    /// Number of pages currently in the file
    page_count: AtomicU64,
}

impl FileStorage {
    /// Opens or creates a storage file at the given path.
    ///
    /// If the file exists, its page count is calculated from file size.
    /// If the file doesn't exist, it is created empty.
    ///
    /// # Errors
    ///
    /// Returns `StorageError::Corrupted` if the file size is not a multiple
    /// of PAGE_SIZE.
    pub async fn open(path: impl Into<PathBuf>) -> Result<Self, StorageError> {
        let path = path.into();

        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&path)
            .await?;

        let metadata = file.metadata().await?;
        let file_size = metadata.len();

        // Validate file size is a multiple of PAGE_SIZE
        if file_size % PAGE_SIZE as u64 != 0 {
            return Err(StorageError::Corrupted(format!(
                "file size {} is not a multiple of page size {}",
                file_size, PAGE_SIZE
            )));
        }

        let page_count = file_size / PAGE_SIZE as u64;

        Ok(Self {
            path,
            file: Mutex::new(file),
            page_count: AtomicU64::new(page_count),
        })
    }

    /// Returns the path to the storage file.
    pub fn path(&self) -> &PathBuf {
        &self.path
    }
}

impl Storage for FileStorage {
    async fn read_page(&self, page_id: PageId, buf: &mut [u8]) -> Result<(), StorageError> {
        // Validate buffer size
        if buf.len() != PAGE_SIZE {
            return Err(StorageError::InvalidBufferSize {
                expected: PAGE_SIZE,
                actual: buf.len(),
            });
        }

        let current_count = self.page_count.load(Ordering::Acquire);
        if page_id.page_num() >= current_count {
            return Err(StorageError::PageNotFound(page_id));
        }

        let mut file = self.file.lock().await;
        file.seek(std::io::SeekFrom::Start(page_id.byte_offset()))
            .await?;
        file.read_exact(buf).await?;

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

        let current_count = self.page_count.load(Ordering::Acquire);
        if page_id.page_num() >= current_count {
            return Err(StorageError::InvalidPageId(page_id));
        }

        let mut file = self.file.lock().await;
        file.seek(std::io::SeekFrom::Start(page_id.byte_offset()))
            .await?;
        file.write_all(buf).await?;

        Ok(())
    }

    async fn allocate_page(&self) -> Result<PageId, StorageError> {
        let mut file = self.file.lock().await;

        // Get current end of file
        let page_num = self.page_count.load(Ordering::Acquire);
        let page_id = PageId::new(page_num);

        // Extend file with zeroed page
        file.seek(std::io::SeekFrom::Start(page_id.byte_offset()))
            .await?;
        file.write_all(&[0u8; PAGE_SIZE]).await?;

        // Update page count
        self.page_count.store(page_num + 1, Ordering::Release);

        Ok(page_id)
    }

    async fn page_count(&self) -> u64 {
        self.page_count.load(Ordering::Acquire)
    }

    async fn sync_all(&self) -> Result<(), StorageError> {
        let file = self.file.lock().await;
        file.sync_all().await?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[tokio::test]
    async fn test_create_new_file() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("test.db");

        let storage = FileStorage::open(&path).await.unwrap();
        assert_eq!(storage.page_count().await, 0);
        assert!(path.exists());
    }

    #[tokio::test]
    async fn test_allocate_and_read() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("test.db");

        let storage = FileStorage::open(&path).await.unwrap();
        let page_id = storage.allocate_page().await.unwrap();

        let mut buf = [0u8; PAGE_SIZE];
        storage.read_page(page_id, &mut buf).await.unwrap();
        assert!(buf.iter().all(|&b| b == 0));
    }

    #[tokio::test]
    async fn test_write_and_read() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("test.db");

        let storage = FileStorage::open(&path).await.unwrap();
        let page_id = storage.allocate_page().await.unwrap();

        // Write data
        let mut write_buf = [0u8; PAGE_SIZE];
        write_buf[0..4].copy_from_slice(&[1, 2, 3, 4]);
        storage.write_page(page_id, &write_buf).await.unwrap();
        storage.sync_all().await.unwrap();

        // Read back
        let mut read_buf = [0u8; PAGE_SIZE];
        storage.read_page(page_id, &mut read_buf).await.unwrap();
        assert_eq!(&read_buf[0..4], &[1, 2, 3, 4]);
    }

    #[tokio::test]
    async fn test_persistence() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("test.db");

        // Write data
        {
            let storage = FileStorage::open(&path).await.unwrap();
            let page_id = storage.allocate_page().await.unwrap();

            let mut buf = [0u8; PAGE_SIZE];
            buf[0] = 42;
            storage.write_page(page_id, &buf).await.unwrap();
            storage.sync_all().await.unwrap();
        }

        // Reopen and verify
        {
            let storage = FileStorage::open(&path).await.unwrap();
            assert_eq!(storage.page_count().await, 1);

            let mut buf = [0u8; PAGE_SIZE];
            storage.read_page(PageId::new(0), &mut buf).await.unwrap();
            assert_eq!(buf[0], 42);
        }
    }

    #[tokio::test]
    async fn test_corrupted_file_size() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("test.db");

        // Create file with invalid size
        tokio::fs::write(&path, vec![0u8; 100]).await.unwrap();

        let result = FileStorage::open(&path).await;
        assert!(matches!(result, Err(StorageError::Corrupted(_))));
    }

    #[tokio::test]
    async fn test_read_unallocated_page() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("test.db");

        let storage = FileStorage::open(&path).await.unwrap();
        let mut buf = [0u8; PAGE_SIZE];
        let result = storage.read_page(PageId::new(0), &mut buf).await;
        assert!(matches!(result, Err(StorageError::PageNotFound(_))));
    }

    #[tokio::test]
    async fn test_write_unallocated_page() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("test.db");

        let storage = FileStorage::open(&path).await.unwrap();
        let buf = [0u8; PAGE_SIZE];
        let result = storage.write_page(PageId::new(0), &buf).await;
        assert!(matches!(result, Err(StorageError::InvalidPageId(_))));
    }

    #[tokio::test]
    async fn test_invalid_buffer_size_read() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("test.db");

        let storage = FileStorage::open(&path).await.unwrap();
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
        let dir = tempdir().unwrap();
        let path = dir.path().join("test.db");

        let storage = FileStorage::open(&path).await.unwrap();
        let page_id = storage.allocate_page().await.unwrap();

        let buf = [0u8; 100]; // Wrong size
        let result = storage.write_page(page_id, &buf).await;
        assert!(matches!(
            result,
            Err(StorageError::InvalidBufferSize { expected: PAGE_SIZE, actual: 100 })
        ));
    }

    #[tokio::test]
    async fn test_multiple_pages() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("test.db");

        let storage = FileStorage::open(&path).await.unwrap();

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

        storage.sync_all().await.unwrap();

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
