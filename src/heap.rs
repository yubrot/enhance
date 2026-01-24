//! Heap storage for variable-length records.
//!
//! This module provides the heap file implementation, which stores table rows
//! (tuples/records) in slotted pages. The term "heap" refers to an unordered
//! collection of records, as opposed to indexed structures like B+trees.
//!
//! - [`HeapPage`]: Page-level record storage using slotted page structure
//! - [`Record`]: A row/tuple of [`Value`]s with compact serialization
//! - [`Value`]: Typed database value enum

mod error;
mod page;
mod record;
mod value;

pub use error::{HeapError, SerializationError};
pub use page::{HeapPage, RecordId, SlotEntry, SlotId, MAX_RECORD_SIZE, SLOT_SIZE};
pub use record::Record;
pub use value::Value;

// Re-export page header types from storage for convenience
pub use crate::storage::{PageHeader, PageType, PAGE_HEADER_SIZE, PAGE_VERSION};
