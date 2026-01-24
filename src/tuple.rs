//! Tuple (record) storage and serialization.
//!
//! This module provides:
//! - [`Slotted`]: Page-level record storage with variable-length records
//! - [`Value`]: Typed database value enum
//! - [`Record`]: A row/tuple of values
//!
//! # Page Layout
//!
//! Records are stored in slotted pages with the following structure:
//!
//! ```text
//! +------------------+ offset 0
//! | PageHeader (24B) |
//! +------------------+ offset 24
//! | Slot Array       | (grows downward)
//! +------------------+
//! | Free Space       |
//! +------------------+
//! | Records          | (grows upward from bottom)
//! +------------------+ offset 8192
//! ```
//!
//! # Record Serialization
//!
//! Records are serialized with a null bitmap followed by value data:
//!
//! ```text
//! +---------------------------+
//! | Null Bitmap (ceil(n/8) B) |  bit=1: NOT NULL, bit=0: NULL
//! +---------------------------+
//! | Value[0] (if not null)    |
//! | Value[1] (if not null)    |
//! | ...                       |
//! +---------------------------+
//! ```

mod error;
mod record;
mod slotted_page;
mod value;

pub use error::{SerdeError, SlottedPageError};
pub use record::Record;
pub use slotted_page::{
    PageHeader, PageType, RecordId, SlotEntry, SlotId, Slotted, MAX_RECORD_SIZE, PAGE_HEADER_SIZE,
    SLOT_SIZE,
};
pub use value::Value;
