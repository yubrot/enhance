//! Transaction management and MVCC (Multi-Version Concurrency Control) infrastructure.
//!
//! This module implements the core components for MVCC:
//! - Transaction ID allocation and lifecycle management
//! - Tuple headers with xmin/xmax for versioning
//! - Snapshot isolation for consistent reads
//! - Visibility rules to determine which tuple versions are visible

pub mod error;
pub mod manager;
pub mod snapshot;
pub mod tuple_header;
pub mod types;
pub mod visibility;

pub use error::TxError;
pub use manager::{TransactionManager, TransactionState};
pub use snapshot::Snapshot;
pub use tuple_header::{TupleHeader, TUPLE_HEADER_SIZE};
pub use types::{CommandId, Infomask, TxId};
pub use visibility::is_visible;
