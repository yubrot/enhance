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
//! - [`Value`]: Typed database value enum

mod error;
mod page;
mod record;
mod value;

pub use error::{HeapError, SerializationError};
pub use page::{
    HeapPage, MAX_RECORD_SIZE, MAX_SLOT_DATA_SIZE, SLOT_SIZE, SlotEntry, SlotId,
};
pub use record::Record;
pub use value::Value;
