//! Buffer pool for caching pages in memory.
//!
//! The buffer pool sits between the storage layer and query execution,
//! caching frequently accessed pages to minimize disk I/O.
//!
//! # Components
//!
//! - [`BufferPool`]: Main interface for page access
//! - [`PageReadGuard`], [`PageWriteGuard`]: RAII guards for automatic unpinning
//! - [`Replacer`]: Trait for page replacement policies
//! - [`LruReplacer`]: LRU (Least Recently Used) implementation
//!
//! # Latch Hierarchy
//!
//! To prevent deadlocks, locks must be acquired in this order:
//! 1. BufferPoolState mutex (page_table, frame_metadata, free_list, replacer)
//! 2. Frame data RwLocks (in PageId order when multiple frames needed)
//!
//! See [`BufferPool`] documentation for detailed latch ordering rules.
//!
//! # Example
//!
//! ```no_run
//! use enhance::storage::{MemoryStorage, BufferPool, LruReplacer};
//!
//! # async fn example() -> Result<(), enhance::storage::BufferPoolError> {
//! let storage = MemoryStorage::new();
//! let replacer = LruReplacer::new(100);
//! let bpm = BufferPool::new(storage, replacer, 100);
//!
//! // Create a new page
//! let mut guard = bpm.new_page().await?;
//! guard.data_mut()[0] = 42;
//! guard.mark_dirty();
//! let page_id = guard.page_id();
//! drop(guard);
//!
//! // Fetch it later
//! let guard = bpm.fetch_page(page_id).await?;
//! assert_eq!(guard.data()[0], 42);
//! # Ok(())
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
pub use replacer::{LruReplacer, Replacer};
