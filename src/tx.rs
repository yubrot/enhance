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

use std::fmt;

pub mod error;
pub mod manager;
pub mod snapshot;
pub mod tuple_header;

pub use error::TxError;
pub use manager::TransactionManager;
pub use snapshot::{Snapshot, Visibility};
pub use tuple_header::{Infomask, TUPLE_HEADER_SIZE, TupleHeader};

/// Transaction ID (64-bit).
///
/// TxIds are allocated sequentially starting from 1. TxId 0 is reserved as INVALID.
/// Using 64-bit IDs eliminates wraparound concerns (PostgreSQL uses 32-bit, requiring VACUUM FREEZE).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TxId(u64);

impl TxId {
    /// Invalid transaction ID (0).
    pub const INVALID: Self = Self(0);

    /// Frozen transaction ID (1).
    ///
    /// This special transaction ID is always considered committed and visible
    /// to all snapshots. Used for:
    /// - Sequence tuple updates (nextval) which are not transactional
    /// - Catalog tuples that should be visible immediately after bootstrap
    ///
    /// Following PostgreSQL's FrozenTransactionId semantics.
    pub const FROZEN: Self = Self(1);

    /// Create a new transaction ID.
    pub const fn new(id: u64) -> Self {
        Self(id)
    }

    /// Get the raw u64 value.
    pub const fn as_u64(&self) -> u64 {
        self.0
    }

    /// Get the next transaction ID.
    pub const fn next(&self) -> Self {
        Self(self.0 + 1)
    }
}

impl fmt::Display for TxId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Command ID within a transaction (32-bit).
///
/// Tracks the order of statements within a transaction for intra-transaction visibility.
/// Each statement increments the command ID.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct CommandId(u32);

impl CommandId {
    /// Invalid command ID (indicates no command, e.g., tuple not yet deleted).
    pub const INVALID: Self = Self(u32::MAX);
    /// First command ID in a transaction.
    pub const FIRST: Self = Self(0);

    /// Create a new command ID.
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw u32 value.
    pub const fn as_u32(&self) -> u32 {
        self.0
    }

    /// Get the next command ID.
    pub const fn next(&self) -> Self {
        // TODO: Limit CommandId (potential overflow)
        Self(self.0 + 1)
    }
}

impl fmt::Display for CommandId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Transaction state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TxState {
    /// Transaction is currently in progress.
    InProgress,
    /// Transaction has committed.
    Committed,
    /// Transaction has aborted.
    Aborted,
}

impl fmt::Display for TxState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TxState::InProgress => write!(f, "InProgress"),
            TxState::Committed => write!(f, "Committed"),
            TxState::Aborted => write!(f, "Aborted"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_txid() {
        assert_eq!(TxId::INVALID.as_u64(), 0);

        let txid = TxId::new(42);
        assert_eq!(txid.as_u64(), 42);
        assert_eq!(txid.next().as_u64(), 43);
    }

    #[test]
    fn test_command_id() {
        assert_eq!(CommandId::INVALID.as_u32(), u32::MAX);
        assert_eq!(CommandId::FIRST.as_u32(), 0);

        let cid = CommandId::new(5);
        assert_eq!(cid.as_u32(), 5);
        assert_eq!(cid.next().as_u32(), 6);
    }
}
