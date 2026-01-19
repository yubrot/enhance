//! Buffer pool for caching pages in memory.
//!
//! The buffer pool sits between the storage layer and query execution,
//! caching frequently accessed pages to minimize disk I/O.
//!
//! # Latch Hierarchy
//!
//! To prevent deadlocks, locks must be acquired in this order:
//! 1. BufferPoolState mutex (page_table, frame_metadata, free_list, replacer)
//! 2. Frame data RwLocks (in PageId order when multiple frames needed)
//!
//! See [`BufferPool`] documentation for detailed latch ordering rules.

mod error;
mod frame;
mod guard;
mod pool;
mod replacer;

pub use error::BufferPoolError;
pub use guard::{PageReadGuard, PageWriteGuard};
pub use pool::BufferPool;
pub use replacer::{LruReplacer, Replacer};
