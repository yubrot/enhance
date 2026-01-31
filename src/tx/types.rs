//! Core MVCC types: TxId, CommandId, and Infomask.

use std::fmt;

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

/// Tuple header information mask (16-bit flags).
///
/// Stores commit/abort status hints for xmin and xmax to avoid repeated
/// lookups in the transaction state table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Infomask(u16);

impl Infomask {
    const XMIN_COMMITTED: u16 = 1 << 0;
    const XMIN_ABORTED: u16 = 1 << 1;
    const XMAX_COMMITTED: u16 = 1 << 2;
    const XMAX_ABORTED: u16 = 1 << 3;

    /// Create an empty infomask with no flags set.
    pub const fn empty() -> Self {
        Self(0)
    }

    /// Check if xmin is committed.
    pub const fn xmin_committed(&self) -> bool {
        (self.0 & Self::XMIN_COMMITTED) != 0
    }

    /// Check if xmin is aborted.
    pub const fn xmin_aborted(&self) -> bool {
        (self.0 & Self::XMIN_ABORTED) != 0
    }

    /// Check if xmax is committed.
    pub const fn xmax_committed(&self) -> bool {
        (self.0 & Self::XMAX_COMMITTED) != 0
    }

    /// Check if xmax is aborted.
    pub const fn xmax_aborted(&self) -> bool {
        (self.0 & Self::XMAX_ABORTED) != 0
    }

    /// Set xmin committed flag.
    pub const fn with_xmin_committed(self) -> Self {
        Self(self.0 | Self::XMIN_COMMITTED)
    }

    /// Set xmin aborted flag.
    pub const fn with_xmin_aborted(self) -> Self {
        Self(self.0 | Self::XMIN_ABORTED)
    }

    /// Set xmax committed flag.
    pub const fn with_xmax_committed(self) -> Self {
        Self(self.0 | Self::XMAX_COMMITTED)
    }

    /// Set xmax aborted flag.
    pub const fn with_xmax_aborted(self) -> Self {
        Self(self.0 | Self::XMAX_ABORTED)
    }

    /// Get the raw u16 value.
    pub const fn as_u16(&self) -> u16 {
        self.0
    }

    /// Create an infomask from a raw u16 value (used for deserialization).
    pub const fn from_raw(value: u16) -> Self {
        Self(value)
    }
}

impl Default for Infomask {
    fn default() -> Self {
        Self::empty()
    }
}

impl fmt::Display for Infomask {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "0x{:04x}", self.0)
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

impl std::fmt::Display for TxState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

    #[test]
    fn test_infomask() {
        type FlagPair = (fn(&Infomask) -> bool, fn(Infomask) -> Infomask);
        let flags: [FlagPair; 4] = [
            (Infomask::xmin_committed, Infomask::with_xmin_committed),
            (Infomask::xmin_aborted, Infomask::with_xmin_aborted),
            (Infomask::xmax_committed, Infomask::with_xmax_committed),
            (Infomask::xmax_aborted, Infomask::with_xmax_aborted),
        ];

        // Test that each setter only affects its corresponding getter
        for (i, (_, setter)) in flags.iter().enumerate() {
            let mask = setter(Infomask::empty());
            for (j, (getter, _)) in flags.iter().enumerate() {
                assert_eq!(getter(&mask), i == j);
            }
        }
    }
}
