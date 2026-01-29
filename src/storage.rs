//! Storage layer for page-based I/O.
//!
//! The storage layer provides page I/O abstractions for the enhance RDBMS.
//! All persistent data is stored in 8KB pages, aligned with OS page sizes
//! and intentionally using PostgreSQL-compatible conventions for learning purposes.
//!
//! # Architecture
//!
//! ```text
//! +------------+
//! | BufferPool |  <- buffer
//! +------------+
//!          |
//!          v
//! +-------------------+
//! | Storage Trait     |  <- io
//! +-------------------+
//!       /      \
//!      v        v
//! +--------------+ +-------------+
//! | MemoryStorage| | FileStorage |
//! +--------------+ +-------------+
//! ```

pub mod buffer;
pub mod error;
pub mod io;
pub mod page;

pub use buffer::{
    BufferPool, BufferPoolError, LruReplacer, PageReadGuard, PageWriteGuard, Replacer,
};
pub use error::StorageError;
pub use io::{FileStorage, MemoryStorage, Storage};
pub use page::{PAGE_HEADER_SIZE, PAGE_SIZE, PAGE_VERSION, PageData, PageHeader, PageId, PageType};
