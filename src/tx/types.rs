//! Core MVCC types: TxId, CommandId, and Infomask.

use std::fmt;

/// Transaction ID (64-bit).
///
/// TxIds are allocated sequentially starting from 1. TxId 0 is reserved as INVALID.
///
/// NOTE: Production systems handle TxId wraparound via VACUUM FREEZE to avoid
/// exhausting the 64-bit space after ~18 quintillion transactions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TxId(u64);

impl TxId {
    /// Invalid transaction ID (0).
    pub const INVALID: Self = Self(0);

    /// Create a new transaction ID.
    pub const fn new(id: u64) -> Self {
        Self(id)
    }

    /// Get the raw u64 value.
    pub const fn as_u64(&self) -> u64 {
        self.0
    }

    /// Check if this is an invalid transaction ID.
    pub const fn is_invalid(&self) -> bool {
        self.0 == 0
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
    /// xmin transaction committed (hint bit).
    pub const XMIN_COMMITTED: u16 = 1 << 0;
    /// xmin transaction aborted (hint bit).
    pub const XMIN_ABORTED: u16 = 1 << 1;
    /// xmax transaction committed (hint bit).
    pub const XMAX_COMMITTED: u16 = 1 << 2;
    /// xmax transaction aborted (hint bit).
    pub const XMAX_ABORTED: u16 = 1 << 3;

    /// Create an empty infomask with no flags set.
    pub const fn empty() -> Self {
        Self(0)
    }

    /// Check if xmin is committed.
    pub const fn xmin_committed(&self) -> bool {
        (self.0 & Self::XMIN_COMMITTED) != 0
    }

    /// Set xmin committed flag.
    pub const fn with_xmin_committed(self) -> Self {
        Self(self.0 | Self::XMIN_COMMITTED)
    }

    /// Check if xmin is aborted.
    pub const fn xmin_aborted(&self) -> bool {
        (self.0 & Self::XMIN_ABORTED) != 0
    }

    /// Set xmin aborted flag.
    pub const fn with_xmin_aborted(self) -> Self {
        Self(self.0 | Self::XMIN_ABORTED)
    }

    /// Check if xmax is committed.
    pub const fn xmax_committed(&self) -> bool {
        (self.0 & Self::XMAX_COMMITTED) != 0
    }

    /// Set xmax committed flag.
    pub const fn with_xmax_committed(self) -> Self {
        Self(self.0 | Self::XMAX_COMMITTED)
    }

    /// Check if xmax is aborted.
    pub const fn xmax_aborted(&self) -> bool {
        (self.0 & Self::XMAX_ABORTED) != 0
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_txid() {
        assert_eq!(TxId::INVALID.as_u64(), 0);
        assert!(TxId::INVALID.is_invalid());

        let txid = TxId::new(42);
        assert_eq!(txid.as_u64(), 42);
        assert!(!txid.is_invalid());

        // Test ordering
        assert!(TxId::new(1) < TxId::new(2));
    }

    #[test]
    fn test_command_id() {
        assert_eq!(CommandId::FIRST.as_u32(), 0);

        let cid = CommandId::new(5);
        assert_eq!(cid.as_u32(), 5);
        assert_eq!(cid.next().as_u32(), 6);

        // Test ordering
        assert!(CommandId::new(1) < CommandId::new(2));
    }

    #[test]
    fn test_infomask() {
        let mask = Infomask::empty();
        assert!(!mask.xmin_committed());
        assert!(!mask.xmin_aborted());
        assert!(!mask.xmax_committed());
        assert!(!mask.xmax_aborted());

        let mask = mask.with_xmin_committed();
        assert!(mask.xmin_committed());
        assert!(!mask.xmin_aborted());

        let mask = mask.with_xmax_aborted();
        assert!(mask.xmin_committed());
        assert!(mask.xmax_aborted());
        assert!(!mask.xmax_committed());

        // Test all flags
        let mask = Infomask::empty()
            .with_xmin_committed()
            .with_xmin_aborted()
            .with_xmax_committed()
            .with_xmax_aborted();
        assert!(mask.xmin_committed());
        assert!(mask.xmin_aborted());
        assert!(mask.xmax_committed());
        assert!(mask.xmax_aborted());
    }

    #[test]
    fn test_infomask_bit_values() {
        assert_eq!(Infomask::XMIN_COMMITTED, 1 << 0);
        assert_eq!(Infomask::XMIN_ABORTED, 1 << 1);
        assert_eq!(Infomask::XMAX_COMMITTED, 1 << 2);
        assert_eq!(Infomask::XMAX_ABORTED, 1 << 3);
    }
}
