//! File-backed storage implementation.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use tokio::fs::{File as TokioFile, OpenOptions};
use tokio::io::{AsyncReadExt, AsyncSeekExt, AsyncWriteExt};
use tokio::sync::Mutex;

use super::Storage;
use crate::storage::error::StorageError;
use crate::storage::page::{PAGE_SIZE, PageId};

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
/// - I/O retry logic for transient failures (EINTR, etc.)
///
/// # Durability
///
/// The `sync_all()` method calls `File::sync_all()` to ensure data reaches disk.
/// Without calling sync_all, data may be lost on crash.
pub struct FileStorage {
    /// Path to the storage file
    path: PathBuf,
    /// File handle wrapped in async mutex for serialized access
    file: Mutex<TokioFile>,
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
    pub fn path(&self) -> &Path {
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
            return Err(StorageError::PageNotFound(page_id));
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

    async fn page_count(&self) -> usize {
        self.page_count.load(Ordering::Acquire) as usize
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
    use super::super::tests as generic;
    use crate::storage::StorageError;
    use tempfile::{TempDir, tempdir};

    /// Helper for creating temporary FileStorage instances for testing.
    struct TempFileStorage {
        dir: TempDir,
    }

    impl TempFileStorage {
        fn new() -> Self {
            Self {
                dir: tempdir().unwrap(),
            }
        }

        async fn storage(&self) -> FileStorage {
            FileStorage::open(self.dir.path().join("test.db"))
                .await
                .unwrap()
        }
    }

    // === Generic tests ===

    #[tokio::test]
    async fn test_basic_operations() {
        generic::test_basic_operations(TempFileStorage::new().storage().await).await;
    }

    #[tokio::test]
    async fn test_concurrent_access() {
        generic::test_concurrent_access(TempFileStorage::new().storage().await).await;
    }

    #[tokio::test]
    async fn test_buffer_size_validation() {
        generic::test_buffer_size_validation(TempFileStorage::new().storage().await).await;
    }

    #[tokio::test]
    async fn test_page_not_found() {
        generic::test_page_not_found(TempFileStorage::new().storage().await).await;
    }

    // === FileStorage-specific tests ===

    #[tokio::test]
    async fn test_create_new_file() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("test.db");
        let storage = FileStorage::open(&path).await.unwrap();
        assert_eq!(storage.page_count().await, 0);
        assert!(path.exists());
    }

    #[tokio::test]
    async fn test_corrupted_file_size() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("test.db");
        tokio::fs::write(&path, vec![0u8; 100]).await.unwrap();
        let result = FileStorage::open(&path).await;
        assert!(matches!(result, Err(StorageError::Corrupted(_))));
    }

    #[tokio::test]
    async fn test_persistence_across_instances() {
        let temp = TempFileStorage::new();
        let mut page_ids = Vec::new();

        {
            let storage = temp.storage().await;
            for i in 0..5 {
                page_ids.push(generic::allocate_and_write(&storage, (i * 10) as u8).await);
            }
            storage.sync_all().await.unwrap();
        }

        {
            let storage = temp.storage().await;
            assert_eq!(storage.page_count().await, 5);
            for (i, &page_id) in page_ids.iter().enumerate() {
                generic::verify_test_data(&storage, page_id, (i * 10) as u8).await;
            }
        }
    }
}
