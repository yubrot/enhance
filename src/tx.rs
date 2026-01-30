//! Transaction management and MVCC (Multi-Version Concurrency Control).
//!
//! This module implements the core infrastructure for MVCC, providing
//! transaction isolation through tuple versioning and snapshot-based visibility.
//!
//! ## Terminology
//!
//! - **TxId**: Transaction identifier assigned at BEGIN
//! - **CommandId**: Per-statement counter within a transaction
//! - **Infomask**: Bit flags for tuple state (committed, aborted, etc.)
//! - **TupleHeader**: MVCC metadata (xmin/xmax/cid/infomask) attached to each tuple
//! - **Snapshot**: Point-in-time view of active transactions for visibility checks
//! - **TransactionManager**: Allocates TxIds and tracks transaction states

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
