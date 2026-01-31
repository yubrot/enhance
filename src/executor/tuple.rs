//! Tuple types for query execution.
//!
//! A [`Tuple`] represents a row during query execution. It combines the
//! physical location ([`TupleId`]), MVCC metadata ([`TupleHeader`]), and
//! the actual data ([`Record`]).

use crate::heap::{Record, SlotId};
use crate::storage::PageId;
use crate::tx::TupleHeader;

/// Physical location of a tuple in storage.
///
/// Identifies a tuple by its page and slot within that page.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TupleId {
    /// Page containing this tuple.
    pub page_id: PageId,
    /// Slot within the page.
    pub slot_id: SlotId,
}

impl TupleId {
    /// Creates a new tuple ID.
    pub fn new(page_id: PageId, slot_id: SlotId) -> Self {
        Self { page_id, slot_id }
    }
}

/// A row during query execution.
///
/// Tuples flow through the executor pipeline. They may come from:
/// - **Heap scan**: Has tid, header, and record from storage
/// - **Projection/computation**: Has only record (computed values)
///
/// The optional fields allow the executor to distinguish between
/// physical tuples (which can be updated/deleted) and derived tuples.
#[derive(Debug, Clone)]
pub struct Tuple {
    /// Physical location (None for computed tuples).
    pub tid: Option<TupleId>,
    /// MVCC header (None for computed tuples).
    pub header: Option<TupleHeader>,
    /// The actual row data.
    pub record: Record,
}

impl Tuple {
    /// Creates a tuple from a heap scan result.
    pub fn from_heap(tid: TupleId, header: TupleHeader, record: Record) -> Self {
        Self {
            tid: Some(tid),
            header: Some(header),
            record,
        }
    }

    /// Creates a computed tuple (e.g., from projection).
    pub fn computed(record: Record) -> Self {
        Self {
            tid: None,
            header: None,
            record,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::heap::Value;
    use crate::tx::{CommandId, TxId};

    #[test]
    fn test_tuple_id() {
        let tid = TupleId::new(PageId::new(1), 5);
        assert_eq!(tid.page_id, PageId::new(1));
        assert_eq!(tid.slot_id, 5);
    }

    #[test]
    fn test_tuple_from_heap() {
        let tid = TupleId::new(PageId::new(0), 0);
        let header = TupleHeader::new(TxId::new(100), CommandId::new(0));
        let record = Record::new(vec![Value::Int32(42)]);

        let tuple = Tuple::from_heap(tid, header, record.clone());
        assert!(tuple.tid.is_some());
        assert!(tuple.header.is_some());
        assert_eq!(tuple.record, record);
    }

    #[test]
    fn test_tuple_computed() {
        let record = Record::new(vec![Value::Int32(42)]);
        let tuple = Tuple::computed(record.clone());
        assert!(tuple.tid.is_none());
        assert!(tuple.header.is_none());
        assert_eq!(tuple.record, record);
    }
}
