//! Typed database value representation.
//!
//! The [`Value`] enum represents a single column value with its concrete type.
//! It supports serialization to/from a compact binary format for storage.

use super::error::SerializationError;
use crate::ensure_buf_len;
use crate::protocol::type_oid;

/// A typed database value.
///
/// This represents a single column value with its concrete type.
/// Variable-length types (Text, Bytea) are heap-allocated.
///
/// NOTE: For production, consider adding:
/// - Numeric/Decimal type for exact decimal arithmetic
/// - Date/Time types
/// - Array types
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum Value {
    /// SQL NULL (type is unknown/any).
    Null,
    /// Boolean (true/false).
    Boolean(bool),
    /// 16-bit signed integer (SMALLINT).
    Int16(i16),
    /// 32-bit signed integer (INTEGER).
    Int32(i32),
    /// 64-bit signed integer (BIGINT).
    Int64(i64),
    /// 32-bit floating point (REAL).
    Float32(f32),
    /// 64-bit floating point (DOUBLE PRECISION).
    Float64(f64),
    /// Variable-length text (TEXT, VARCHAR).
    Text(String),
    /// Variable-length binary (BYTEA).
    Bytea(Vec<u8>),
}

impl Value {
    /// Returns the PostgreSQL type OID for this value.
    ///
    /// Returns `UNKNOWN` for Null since it has no concrete type.
    pub fn type_oid(&self) -> i32 {
        match self {
            Value::Null => type_oid::UNKNOWN,
            Value::Boolean(_) => type_oid::BOOL,
            Value::Int16(_) => type_oid::INT2,
            Value::Int32(_) => type_oid::INT4,
            Value::Int64(_) => type_oid::INT8,
            Value::Float32(_) => type_oid::FLOAT4,
            Value::Float64(_) => type_oid::FLOAT8,
            Value::Text(_) => type_oid::TEXT,
            Value::Bytea(_) => type_oid::BYTEA,
        }
    }

    /// Returns true if this value is NULL.
    pub fn is_null(&self) -> bool {
        matches!(self, Value::Null)
    }

    /// Returns the serialized size in bytes.
    ///
    /// For NULL, this returns 0 (NULL values are indicated by the null bitmap).
    /// For variable-length types, this includes the 4-byte length prefix.
    pub fn serialized_size(&self) -> usize {
        match self {
            Value::Null => 0,
            Value::Boolean(_) => 1,
            Value::Int16(_) => 2,
            Value::Int32(_) => 4,
            Value::Int64(_) => 8,
            Value::Float32(_) => 4,
            Value::Float64(_) => 8,
            Value::Text(s) => 4 + s.len(),
            Value::Bytea(b) => 4 + b.len(),
        }
    }

    /// Serializes this value to a buffer.
    ///
    /// Returns the number of bytes written. NULL writes 0 bytes.
    ///
    /// # Errors
    ///
    /// Returns `SerializationError::BufferTooSmall` if the buffer is too small.
    pub fn serialize(&self, buf: &mut [u8]) -> Result<usize, SerializationError> {
        match self {
            Value::Null => Ok(0),
            Value::Boolean(b) => {
                ensure_buf_len!(buf, 1);
                buf[0] = if *b { 1 } else { 0 };
                Ok(1)
            }
            Value::Int16(n) => {
                ensure_buf_len!(buf, 2);
                buf[0..2].copy_from_slice(&n.to_le_bytes());
                Ok(2)
            }
            Value::Int32(n) => {
                ensure_buf_len!(buf, 4);
                buf[0..4].copy_from_slice(&n.to_le_bytes());
                Ok(4)
            }
            Value::Int64(n) => {
                ensure_buf_len!(buf, 8);
                buf[0..8].copy_from_slice(&n.to_le_bytes());
                Ok(8)
            }
            Value::Float32(n) => {
                ensure_buf_len!(buf, 4);
                buf[0..4].copy_from_slice(&n.to_le_bytes());
                Ok(4)
            }
            Value::Float64(n) => {
                ensure_buf_len!(buf, 8);
                buf[0..8].copy_from_slice(&n.to_le_bytes());
                Ok(8)
            }
            Value::Text(s) => {
                let data = s.as_bytes();
                let required = 4 + data.len();
                ensure_buf_len!(buf, required);
                buf[0..4].copy_from_slice(&(data.len() as u32).to_le_bytes());
                buf[4..4 + data.len()].copy_from_slice(data);
                Ok(required)
            }
            Value::Bytea(data) => {
                let required = 4 + data.len();
                ensure_buf_len!(buf, required);
                buf[0..4].copy_from_slice(&(data.len() as u32).to_le_bytes());
                buf[4..4 + data.len()].copy_from_slice(data);
                Ok(required)
            }
        }
    }

    /// Deserializes a value from a buffer given its type OID.
    ///
    /// Returns the value and the number of bytes consumed.
    ///
    /// # Errors
    ///
    /// Returns `SerializationError::BufferTooSmall` if the buffer is too small.
    /// Returns `SerializationError::InvalidFormat` for unsupported types or malformed data.
    pub fn deserialize(buf: &[u8], oid: i32) -> Result<(Self, usize), SerializationError> {
        match oid {
            type_oid::BOOL => {
                ensure_buf_len!(buf, 1);
                Ok((Value::Boolean(buf[0] != 0), 1))
            }
            type_oid::INT2 => {
                ensure_buf_len!(buf, 2);
                let n = i16::from_le_bytes([buf[0], buf[1]]);
                Ok((Value::Int16(n), 2))
            }
            type_oid::INT4 => {
                ensure_buf_len!(buf, 4);
                let n = i32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]);
                Ok((Value::Int32(n), 4))
            }
            type_oid::INT8 => {
                ensure_buf_len!(buf, 8);
                let n = i64::from_le_bytes(buf[0..8].try_into().unwrap());
                Ok((Value::Int64(n), 8))
            }
            type_oid::FLOAT4 => {
                ensure_buf_len!(buf, 4);
                let n = f32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]);
                Ok((Value::Float32(n), 4))
            }
            type_oid::FLOAT8 => {
                ensure_buf_len!(buf, 8);
                let n = f64::from_le_bytes(buf[0..8].try_into().unwrap());
                Ok((Value::Float64(n), 8))
            }
            type_oid::TEXT | type_oid::VARCHAR | type_oid::BPCHAR => {
                ensure_buf_len!(buf, 4);
                let len = u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]) as usize;
                let required = 4 + len;
                ensure_buf_len!(buf, required);
                let s = String::from_utf8(buf[4..4 + len].to_vec())
                    .map_err(|e| SerializationError::InvalidFormat(e.to_string()))?;
                Ok((Value::Text(s), required))
            }
            type_oid::BYTEA => {
                ensure_buf_len!(buf, 4);
                let len = u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]) as usize;
                let required = 4 + len;
                ensure_buf_len!(buf, required);
                Ok((Value::Bytea(buf[4..4 + len].to_vec()), required))
            }
            _ => Err(SerializationError::InvalidFormat(format!(
                "unsupported type OID: {}",
                oid
            ))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_roundtrip_all_types() {
        let values = [
            Value::Boolean(true),
            Value::Boolean(false),
            Value::Int16(0),
            Value::Int16(i16::MIN),
            Value::Int16(i16::MAX),
            Value::Int32(0),
            Value::Int32(i32::MIN),
            Value::Int32(i32::MAX),
            Value::Int64(0),
            Value::Int64(i64::MIN),
            Value::Int64(i64::MAX),
            Value::Float32(0.0),
            Value::Float32(std::f32::consts::PI),
            Value::Float64(0.0),
            Value::Float64(std::f64::consts::E),
            Value::Text(String::new()),
            Value::Text("hello 日本語 🎉".into()),
            Value::Bytea(vec![]),
            Value::Bytea(vec![0, 255, 128]),
        ];
        for value in values {
            let oid = value.type_oid();
            let mut buf = vec![0u8; value.serialized_size().max(1)];
            let written = value.serialize(&mut buf).unwrap();
            let (parsed, consumed) = Value::deserialize(&buf, oid).unwrap();
            assert_eq!(parsed, value);
            assert_eq!(consumed, written);
        }
    }

    #[test]
    fn test_null() {
        assert!(Value::Null.is_null());
        assert!(!Value::Int32(0).is_null());
        assert_eq!(Value::Null.serialized_size(), 0);
        assert_eq!(Value::Null.type_oid(), type_oid::UNKNOWN);
        assert_eq!(Value::Null.serialize(&mut [0u8; 1]).unwrap(), 0);
    }

    #[test]
    fn test_text_type_aliases() {
        let mut buf = vec![0u8; 8];
        Value::Text("test".into()).serialize(&mut buf).unwrap();
        for oid in [type_oid::TEXT, type_oid::VARCHAR, type_oid::BPCHAR] {
            assert!(matches!(
                Value::deserialize(&buf, oid),
                Ok((Value::Text(_), _))
            ));
        }
    }

    #[test]
    fn test_buffer_too_small() {
        let mut buf = [0u8; 2];
        assert!(matches!(
            Value::Int32(42).serialize(&mut buf),
            Err(SerializationError::BufferTooSmall {
                required: 4,
                available: 2
            })
        ));
    }

    #[test]
    fn test_deserialize_unsupported_type() {
        assert!(matches!(
            Value::deserialize(&[0u8; 8], 9999),
            Err(SerializationError::InvalidFormat(_))
        ));
    }

    #[test]
    fn test_invalid_utf8() {
        let mut buf = [0u8; 8];
        buf[..4].copy_from_slice(&3u32.to_le_bytes());
        buf[4..7].copy_from_slice(&[0xFF, 0xFE, 0xFF]);
        assert!(matches!(
            Value::deserialize(&buf, type_oid::TEXT),
            Err(SerializationError::InvalidFormat(_))
        ));
    }
}
