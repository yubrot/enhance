//! Storage layer for page-based I/O.
//!
//! The storage layer provides page I/O abstractions for the enhance RDBMS.
//! All persistent data is stored in 8KB pages, aligned with OS page sizes
//! and PostgreSQL conventions.
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
//! | Storage Trait     |  <- io
//! +-------------------+
//!       /      \
//!      v        v
//! +--------------+ +-------------+
//! | MemoryStorage| | FileStorage |
//! +--------------+ +-------------+
//! ```

pub mod error;
pub mod io;
pub mod page;

pub use error::StorageError;
pub use io::{FileStorage, MemoryStorage, Storage};
pub use page::{PageData, PageId, PAGE_SIZE};
