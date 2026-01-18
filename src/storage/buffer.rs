//! Buffer Pool Manager for in-memory page caching.
//!
//! The Buffer Pool Manager sits between upper layers (Executor, B+Tree) and
//! the Storage trait. It caches pages in memory to avoid repeated disk I/O.
//!
//! # Week 7 Scope
//!
//! - Basic fetch_page / fetch_page_mut / unpin_page functionality
//! - PageId → FrameId mapping via page_table
//! - Simple FIFO free_list (no eviction if full)
//!
//! # Future Extensions
//!
//! - Week 8: LRU Replacer and Page-level Latches
//! - Week 21: WAL integration (page_lsn tracking)

pub mod error;
pub mod frame;
pub mod guard;
pub mod manager;

pub use error::BufferPoolError;
pub use frame::{Frame, FrameId};
pub use guard::{PageReadGuard, PageWriteGuard};
pub use manager::{BufferPoolConfig, BufferPoolManager};
