//! Tuple header for MVCC versioning.
//!
//! Each tuple stored in a heap page includes a header that tracks:
//! - xmin: The transaction that inserted this tuple
//! - xmax: The transaction that deleted this tuple (INVALID if still live)
//! - cid: Command ID for intra-transaction visibility
//! - infomask: Status hint bits to optimize visibility checks

use super::types::{CommandId, Infomask, TxId};

/// Size of the tuple header in bytes: 8 (xmin) + 8 (xmax) + 4 (cid) + 2 (infomask) = 22 bytes.
pub const TUPLE_HEADER_SIZE: usize = 22;

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
    /// Command ID within the transaction (for intra-transaction visibility).
    pub cid: CommandId,
    /// Information mask with commit/abort hint bits.
    pub infomask: Infomask,
}

impl TupleHeader {
    /// Create a new tuple header for an INSERT operation.
    ///
    /// Sets xmin to the inserting transaction, xmax to INVALID (not deleted),
    /// and initializes infomask to empty.
    pub fn new_insert(xmin: TxId, cid: CommandId) -> Self {
        Self {
            xmin,
            xmax: TxId::INVALID,
            cid,
            infomask: Infomask::empty(),
        }
    }

    /// Serialize the tuple header to bytes.
    ///
    /// Layout (22 bytes):
    /// - xmin: 8 bytes (little-endian u64)
    /// - xmax: 8 bytes (little-endian u64)
    /// - cid: 4 bytes (little-endian u32)
    /// - infomask: 2 bytes (little-endian u16)
    ///
    /// Returns the number of bytes written (always 22).
    pub fn serialize(&self, buf: &mut [u8]) -> Result<usize, SerializationError> {
        if buf.len() < TUPLE_HEADER_SIZE {
            return Err(SerializationError::BufferTooSmall {
                required: TUPLE_HEADER_SIZE,
                available: buf.len(),
            });
        }

        buf[0..8].copy_from_slice(&self.xmin.as_u64().to_le_bytes());
        buf[8..16].copy_from_slice(&self.xmax.as_u64().to_le_bytes());
        buf[16..20].copy_from_slice(&self.cid.as_u32().to_le_bytes());
        buf[20..22].copy_from_slice(&self.infomask.as_u16().to_le_bytes());

        Ok(TUPLE_HEADER_SIZE)
    }

    /// Deserialize a tuple header from bytes.
    pub fn deserialize(buf: &[u8]) -> Result<Self, SerializationError> {
        if buf.len() < TUPLE_HEADER_SIZE {
            return Err(SerializationError::BufferTooSmall {
                required: TUPLE_HEADER_SIZE,
                available: buf.len(),
            });
        }

        let xmin = TxId::new(u64::from_le_bytes(buf[0..8].try_into().unwrap()));
        let xmax = TxId::new(u64::from_le_bytes(buf[8..16].try_into().unwrap()));
        let cid = CommandId::new(u32::from_le_bytes(buf[16..20].try_into().unwrap()));
        let infomask_raw = u16::from_le_bytes(buf[20..22].try_into().unwrap());
        let infomask = Infomask::from_raw(infomask_raw);

        Ok(Self {
            xmin,
            xmax,
            cid,
            infomask,
        })
    }
}

/// Errors that can occur during tuple header serialization/deserialization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SerializationError {
    /// Buffer is too small for the operation.
    BufferTooSmall {
        /// Required buffer size.
        required: usize,
        /// Available buffer size.
        available: usize,
    },
}

impl std::fmt::Display for SerializationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SerializationError::BufferTooSmall {
                required,
                available,
            } => write!(
                f,
                "Buffer too small: required {} bytes, available {} bytes",
                required, available
            ),
        }
    }
}

impl std::error::Error for SerializationError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tuple_header_size() {
        assert_eq!(TUPLE_HEADER_SIZE, 22);
    }

    #[test]
    fn test_new_insert() {
        let header = TupleHeader::new_insert(TxId::new(100), CommandId::new(5));
        assert_eq!(header.xmin, TxId::new(100));
        assert_eq!(header.xmax, TxId::INVALID);
        assert_eq!(header.cid, CommandId::new(5));
        assert_eq!(header.infomask, Infomask::empty());
    }

    #[test]
    fn test_serialize_deserialize() {
        let original = TupleHeader {
            xmin: TxId::new(42),
            xmax: TxId::new(100),
            cid: CommandId::new(7),
            infomask: Infomask::empty()
                .with_xmin_committed()
                .with_xmax_aborted(),
        };

        let mut buf = [0u8; TUPLE_HEADER_SIZE];
        let written = original.serialize(&mut buf).unwrap();
        assert_eq!(written, TUPLE_HEADER_SIZE);

        let deserialized = TupleHeader::deserialize(&buf).unwrap();
        assert_eq!(deserialized, original);
    }

    #[test]
    fn test_serialize_buffer_too_small() {
        let header = TupleHeader::new_insert(TxId::new(1), CommandId::FIRST);
        let mut buf = [0u8; 10]; // Too small

        let result = header.serialize(&mut buf);
        assert!(matches!(
            result,
            Err(SerializationError::BufferTooSmall { .. })
        ));
    }

    #[test]
    fn test_deserialize_buffer_too_small() {
        let buf = [0u8; 10]; // Too small
        let result = TupleHeader::deserialize(&buf);
        assert!(matches!(
            result,
            Err(SerializationError::BufferTooSmall { .. })
        ));
    }

    #[test]
    fn test_serialization_layout() {
        // Verify exact byte layout
        let header = TupleHeader {
            xmin: TxId::new(0x0102030405060708),
            xmax: TxId::new(0x090a0b0c0d0e0f10),
            cid: CommandId::new(0x11121314),
            infomask: Infomask::from_raw(0x1516),
        };

        let mut buf = [0u8; TUPLE_HEADER_SIZE];
        header.serialize(&mut buf).unwrap();

        // xmin (little-endian)
        assert_eq!(&buf[0..8], &[0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]);
        // xmax (little-endian)
        assert_eq!(&buf[8..16], &[0x10, 0x0f, 0x0e, 0x0d, 0x0c, 0x0b, 0x0a, 0x09]);
        // cid (little-endian)
        assert_eq!(&buf[16..20], &[0x14, 0x13, 0x12, 0x11]);
        // infomask (little-endian)
        assert_eq!(&buf[20..22], &[0x16, 0x15]);
    }
}
