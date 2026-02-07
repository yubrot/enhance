//! Core types for the query executor.

use crate::datum::Type;
use crate::heap::Record;
use crate::storage::PageId;

/// Metadata describing a result column.
#[derive(Debug, Clone)]
pub struct ColumnDesc {
    /// Column name (or alias).
    pub name: String,
    /// OID of the source table (0 if not from a table).
    pub table_oid: i32,
    /// Column attribute number within the source table (0 if not from a table).
    pub column_id: i16,
    /// Data type.
    pub data_type: Type,
}

/// Physical location of a tuple within the heap storage.
///
/// Combines a page identifier with a slot position on that page,
/// uniquely identifying a tuple for future DML operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TupleId {
    /// Page containing the tuple.
    pub page_id: PageId,
    /// Slot within the page.
    pub slot_id: u16,
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
