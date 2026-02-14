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
//! ## Interface Layers
//!
//! - **[`HeapPage`]** — Low-level, single-page operations. Callers manage page
//!   fetching and chain traversal themselves. Used for page initialization,
//!   catalog bootstrap, and MVCC-bypassing in-place updates (e.g., sequences).
//! - **[`insert`], [`delete`], [`update`], [`scan_visible_page`]** — High-level
//!   functions that operate on a heap page chain, handling page traversal,
//!   allocation, and MVCC visibility automatically.
//!
//! ## Other Components
//!
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
pub use write::{delete, insert, update};

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

/// Test helpers for heap-layer tests used across multiple test modules.
#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::storage::{BufferPool, PageId, Replacer, Storage};

    impl<S: Storage, R: Replacer> BufferPool<S, R> {
        /// Creates and initializes a heap table page.
        pub async fn new_heap_page(
            &self,
            initializer: impl FnOnce(&mut HeapPage<&mut [u8]>),
        ) -> PageId {
            let mut guard = self.new_page().await.unwrap();
            let page_id = guard.page_id();
            let mut page = HeapPage::new(guard.as_mut());
            page.init();
            initializer(&mut page);
            page_id
        }
    }
}
