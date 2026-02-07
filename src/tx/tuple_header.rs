//! Tuple header for MVCC versioning.

use std::fmt;

use super::{CommandId, TxId};

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

/// Size of the tuple header in bytes: 8 (xmin) + 8 (xmax) + 4 (cmin) + 4 (cmax) + 2 (infomask) = 26 bytes.
pub const TUPLE_HEADER_SIZE: usize = 26;

/// Tuple header for MVCC.
///
/// Prepended to every tuple stored in a heap page. This header enables
/// multi-version concurrency control by tracking which transaction created
/// and deleted each tuple version.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TupleHeader {
    /// Transaction ID that inserted this tuple.
    pub xmin: TxId,
    /// Transaction ID that deleted this tuple (INVALID if not deleted).
    pub xmax: TxId,
    /// Command ID when this tuple was inserted (for intra-transaction visibility).
    pub cmin: CommandId,
    /// Command ID when this tuple was deleted (INVALID if not deleted).
    pub cmax: CommandId,
    /// Information mask with commit/abort hint bits.
    pub infomask: Infomask,
}

impl TupleHeader {
    /// Create a new tuple header for an INSERT operation.
    ///
    /// Sets xmin to the inserting transaction, xmax to INVALID (not deleted),
    /// cmax to INVALID (not deleted), and initializes infomask to empty.
    pub fn new(xmin: TxId, cmin: CommandId) -> Self {
        Self {
            xmin,
            xmax: TxId::INVALID,
            cmin,
            cmax: CommandId::INVALID,
            infomask: Infomask::empty(),
        }
    }

    /// Reads a tuple header from bytes.
    pub fn read(data: &[u8]) -> Self {
        Self {
            xmin: TxId::new(u64::from_le_bytes([
                data[0], data[1], data[2], data[3], data[4], data[5], data[6], data[7],
            ])),
            xmax: TxId::new(u64::from_le_bytes([
                data[8], data[9], data[10], data[11], data[12], data[13], data[14], data[15],
            ])),
            cmin: CommandId::new(u32::from_le_bytes([data[16], data[17], data[18], data[19]])),
            cmax: CommandId::new(u32::from_le_bytes([data[20], data[21], data[22], data[23]])),
            infomask: Infomask::from_raw(u16::from_le_bytes([data[24], data[25]])),
        }
    }

    /// Writes the tuple header to bytes.
    ///
    /// Layout (26 bytes):
    /// - xmin: 8 bytes (little-endian u64)
    /// - xmax: 8 bytes (little-endian u64)
    /// - cmin: 4 bytes (little-endian u32)
    /// - cmax: 4 bytes (little-endian u32)
    /// - infomask: 2 bytes (little-endian u16)
    pub fn write(&self, data: &mut [u8]) {
        data[0..8].copy_from_slice(&self.xmin.as_u64().to_le_bytes());
        data[8..16].copy_from_slice(&self.xmax.as_u64().to_le_bytes());
        data[16..20].copy_from_slice(&self.cmin.as_u32().to_le_bytes());
        data[20..24].copy_from_slice(&self.cmax.as_u32().to_le_bytes());
        data[24..26].copy_from_slice(&self.infomask.as_u16().to_le_bytes());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let header = TupleHeader::new(TxId::new(100), CommandId::new(5));
        assert_eq!(header.xmin, TxId::new(100));
        assert_eq!(header.xmax, TxId::INVALID);
        assert_eq!(header.cmin, CommandId::new(5));
        assert_eq!(header.cmax, CommandId::INVALID);
        assert_eq!(header.infomask, Infomask::empty());
    }

    #[test]
    fn test_read_write() {
        let original = TupleHeader {
            xmin: TxId::new(42),
            xmax: TxId::new(100),
            cmin: CommandId::new(7),
            cmax: CommandId::new(12),
            infomask: Infomask::empty().with_xmin_committed().with_xmax_aborted(),
        };

        let mut buf = [0u8; TUPLE_HEADER_SIZE];
        original.write(&mut buf);

        let read_back = TupleHeader::read(&buf);
        assert_eq!(read_back, original);
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
