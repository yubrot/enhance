//! Heap storage for table data.
//!
//! This module provides the heap file implementation, which stores table rows
//! as tuples in slotted pages. The heap is an unordered collection of tuples.
//!
//! ## Terminology
//!
//! - **Tuple**: Complete stored unit = TupleHeader (MVCC metadata) + Record (data).
//!   This is a conceptual term for the on-disk format, not a struct.
//! - **Record**: Data values only (Vec<Value>), without MVCC information
//!
//! ## Components
//!
//! - [`HeapPage`]: Page-level tuple storage using slotted page structure
//! - [`Record`]: Data values for a row (combined with TupleHeader to form a tuple)
//! - [`TupleId`]: Physical location of a tuple (page + slot)

mod error;
mod page;
mod record;
mod scan;
mod write;

pub use error::HeapError;
pub use page::{HeapPage, MAX_RECORD_SIZE, SlotId};
pub use record::Record;
pub use scan::scan_visible_page;
pub use write::insert;

/// Physical location of a tuple within the heap storage.
///
/// Combines a page identifier with a slot position on that page,
/// uniquely identifying a tuple for future DML operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TupleId {
    /// Page containing the tuple.
    pub page_id: crate::storage::PageId,
    /// Slot within the page.
    pub slot_id: SlotId,
}
