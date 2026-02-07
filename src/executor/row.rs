//! Row type produced by executor nodes.
//!
//! A [`Row`] wraps a [`Record`] with an optional physical location ([`TupleId`]).
//! This separates the executor's logical output from the low-level "tuple"
//! concept (TupleHeader + Record) used in heap storage.

use crate::heap::{Record, TupleId};

/// A single row produced by the executor.
///
/// Rows originating from heap scans carry a [`TupleId`] for future DML
/// operations (DELETE, UPDATE). Computed rows (from projections, expressions)
/// have `tid: None`.
#[derive(Debug, Clone)]
pub struct Row {
    /// Physical location in the heap (if applicable).
    pub tid: Option<TupleId>,
    /// The column values.
    pub record: Record,
}

impl Row {
    /// Creates a row originating from a heap page scan.
    pub fn from_heap(tid: TupleId, record: Record) -> Self {
        Self {
            tid: Some(tid),
            record,
        }
    }

    /// Creates a computed row without a physical location.
    pub fn computed(record: Record) -> Self {
        Self { tid: None, record }
    }
}
