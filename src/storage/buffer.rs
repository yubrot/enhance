//! Buffer pool for page caching.
//!
//! The buffer pool manager provides in-memory caching of pages with
//! LRU replacement policy and RAII-based access guards.
//!
//! # Example
//!
//! ```no_run
//! use enhance::storage::{BufferPool, MemoryStorage, PageId};
//!
//! # async fn example() {
//! let storage = MemoryStorage::new();
//! let pool = BufferPool::new(storage, 64); // 64 frames = 512KB
//!
//! // Allocate and write a new page
//! let mut guard = pool.new_page().await.unwrap();
//! guard[0..5].copy_from_slice(b"hello");
//! drop(guard); // Unpins and marks dirty
//!
//! // Read the page back
//! let guard = pool.fetch_page_read(PageId::new(0)).await.unwrap();
//! assert_eq!(&guard[0..5], b"hello");
//! # }
//! ```

mod error;
mod frame;
mod guard;
mod pool;
mod replacer;

pub use error::BufferPoolError;
pub use guard::{PageReadGuard, PageWriteGuard};
pub use pool::BufferPool;

// Re-export FrameId for testing/debugging (but not Frame internals)
pub use frame::FrameId;
