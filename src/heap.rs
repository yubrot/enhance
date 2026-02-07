//! Heap storage for table data.
//!
//! This module provides the heap file implementation, which stores table rows
//! as tuples in slotted pages. The heap is an unordered collection of tuples.
//!
//! ## Terminology
//!
//! - **Tuple**: Complete stored unit = TupleHeader (MVCC metadata) + Record (data)
//! - **Record**: Data values only (Vec<Value>), without MVCC information
//!
//! ## Components
//!
//! - [`HeapPage`]: Page-level tuple storage using slotted page structure
//! - [`Record`]: Data values for a row (combined with TupleHeader to form a tuple)
//! - [`TupleId`]: Physical location of a tuple (page + slot)
//! - [`Tuple`]: Record with optional physical location

mod error;
mod page;
mod record;

pub use error::HeapError;
pub use page::{HeapPage, MAX_RECORD_SIZE, SlotId};
pub use record::Record;

use crate::storage::PageId;

/// Physical location of a tuple within the heap storage.
///
/// Combines a page identifier with a slot position on that page,
/// uniquely identifying a tuple for future DML operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TupleId {
    /// Page containing the tuple.
    pub page_id: PageId,
    /// Slot within the page.
    pub slot_id: SlotId,
}

/// A single tuple produced by the executor.
///
/// Wraps a [`Record`] with an optional physical location ([`TupleId`]).
/// Tuples originating from heap scans carry a `TupleId`; computed tuples
/// (from projections, expressions) have `tid: None`.
#[derive(Debug, Clone)]
pub struct Tuple {
    /// Physical location in the heap (if applicable).
    pub tid: Option<TupleId>,
    /// The column values.
    pub record: Record,
}

impl Tuple {
    /// Creates a tuple originating from a heap page scan.
    pub fn from_heap(tid: TupleId, record: Record) -> Self {
        Self {
            tid: Some(tid),
            record,
        }
    }

    /// Creates a computed tuple without a physical location.
    pub fn computed(record: Record) -> Self {
        Self { tid: None, record }
    }
}
