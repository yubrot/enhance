//! Transaction management and MVCC (Multi-Version Concurrency Control) infrastructure.
//!
//! This module implements the core components for MVCC:
//! - Transaction ID allocation and lifecycle management ([`TransactionManager`])
//! - Tuple headers with xmin/xmax for versioning ([`TupleHeader`])
//! - Snapshot isolation for consistent reads ([`Snapshot`])

pub mod error;
pub mod manager;
pub mod snapshot;
pub mod tuple_header;
pub mod types;

pub use error::TxError;
pub use manager::TransactionManager;
pub use snapshot::Snapshot;
pub use tuple_header::{TUPLE_HEADER_SIZE, TupleHeader};
pub use types::{CommandId, Infomask, TxId, TxState};
