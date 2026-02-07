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

mod error;
mod page;
mod record;

pub use error::HeapError;
pub use page::{HeapPage, MAX_RECORD_SIZE, SlotId};
pub use record::Record;
