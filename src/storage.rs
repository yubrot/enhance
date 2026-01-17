//! Storage layer for page-based I/O.
//!
//! This module provides the VFS (Virtual File System) abstraction for the
//! enhance RDBMS. All persistent data is stored in 8KB pages, aligned with
//! OS page sizes and PostgreSQL conventions.
//!
//! # Architecture
//!
//! ```text
//! +-------------------+
//! | Buffer Pool       |  <- Week 7-8
//! +-------------------+
//!          |
//!          v
//! +-------------------+
//! | Storage Trait     |  <- This module
//! +-------------------+
//!       /      \
//!      v        v
//! +--------+ +--------+
//! | Memory | | File   |
//! +--------+ +--------+
//! ```
//!
//! # Usage
//!
//! ```rust,no_run
//! use enhance::storage::{MemoryStorage, Storage, PAGE_SIZE};
//!
//! # async fn example() -> Result<(), enhance::storage::StorageError> {
//! let storage = MemoryStorage::new();
//!
//! // Allocate a page
//! let page_id = storage.allocate_page().await?;
//!
//! // Write data
//! let mut buf = [0u8; PAGE_SIZE];
//! buf[0..5].copy_from_slice(b"hello");
//! storage.write_page(page_id, &buf).await?;
//!
//! // Read data
//! let mut read_buf = [0u8; PAGE_SIZE];
//! storage.read_page(page_id, &mut read_buf).await?;
//! assert_eq!(&read_buf[0..5], b"hello");
//! # Ok(())
//! # }
//! ```

mod error;
mod file;
mod memory;
mod page;
mod traits;

pub use error::StorageError;
pub use file::FileStorage;
pub use memory::MemoryStorage;
pub use page::{PageId, PAGE_SIZE};
pub use traits::Storage;
