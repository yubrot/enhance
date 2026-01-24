//! Typed database value representation.
//!
//! The [`Value`] enum represents a single column value with its concrete type.
//! It supports serialization to/from a compact binary format for storage.

use super::error::SerdeError;
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
#[derive(Debug, Clone, PartialEq)]
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
    /// Returns `SerdeError::BufferTooSmall` if the buffer is too small.
    pub fn serialize(&self, buf: &mut [u8]) -> Result<usize, SerdeError> {
        match self {
            Value::Null => Ok(0),
            Value::Boolean(b) => {
                if buf.is_empty() {
                    return Err(SerdeError::BufferTooSmall {
                        required: 1,
                        available: 0,
                    });
                }
                buf[0] = if *b { 1 } else { 0 };
                Ok(1)
            }
            Value::Int16(n) => {
                if buf.len() < 2 {
                    return Err(SerdeError::BufferTooSmall {
                        required: 2,
                        available: buf.len(),
                    });
                }
                buf[0..2].copy_from_slice(&n.to_le_bytes());
                Ok(2)
            }
            Value::Int32(n) => {
                if buf.len() < 4 {
                    return Err(SerdeError::BufferTooSmall {
                        required: 4,
                        available: buf.len(),
                    });
                }
                buf[0..4].copy_from_slice(&n.to_le_bytes());
                Ok(4)
            }
            Value::Int64(n) => {
                if buf.len() < 8 {
                    return Err(SerdeError::BufferTooSmall {
                        required: 8,
                        available: buf.len(),
                    });
                }
                buf[0..8].copy_from_slice(&n.to_le_bytes());
                Ok(8)
            }
            Value::Float32(n) => {
                if buf.len() < 4 {
                    return Err(SerdeError::BufferTooSmall {
                        required: 4,
                        available: buf.len(),
                    });
                }
                buf[0..4].copy_from_slice(&n.to_le_bytes());
                Ok(4)
            }
            Value::Float64(n) => {
                if buf.len() < 8 {
                    return Err(SerdeError::BufferTooSmall {
                        required: 8,
                        available: buf.len(),
                    });
                }
                buf[0..8].copy_from_slice(&n.to_le_bytes());
                Ok(8)
            }
            Value::Text(s) => {
                let data = s.as_bytes();
                let required = 4 + data.len();
                if buf.len() < required {
                    return Err(SerdeError::BufferTooSmall {
                        required,
                        available: buf.len(),
                    });
                }
                buf[0..4].copy_from_slice(&(data.len() as u32).to_le_bytes());
                buf[4..4 + data.len()].copy_from_slice(data);
                Ok(required)
            }
            Value::Bytea(data) => {
                let required = 4 + data.len();
                if buf.len() < required {
                    return Err(SerdeError::BufferTooSmall {
                        required,
                        available: buf.len(),
                    });
                }
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
    /// Returns `SerdeError::BufferTooSmall` if the buffer is too small.
    /// Returns `SerdeError::InvalidFormat` for unsupported types or malformed data.
    pub fn deserialize(buf: &[u8], oid: i32) -> Result<(Self, usize), SerdeError> {
        match oid {
            type_oid::BOOL => {
                if buf.is_empty() {
                    return Err(SerdeError::BufferTooSmall {
                        required: 1,
                        available: 0,
                    });
                }
                Ok((Value::Boolean(buf[0] != 0), 1))
            }
            type_oid::INT2 => {
                if buf.len() < 2 {
                    return Err(SerdeError::BufferTooSmall {
                        required: 2,
                        available: buf.len(),
                    });
                }
                let n = i16::from_le_bytes([buf[0], buf[1]]);
                Ok((Value::Int16(n), 2))
            }
            type_oid::INT4 => {
                if buf.len() < 4 {
                    return Err(SerdeError::BufferTooSmall {
                        required: 4,
                        available: buf.len(),
                    });
                }
                let n = i32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]);
                Ok((Value::Int32(n), 4))
            }
            type_oid::INT8 => {
                if buf.len() < 8 {
                    return Err(SerdeError::BufferTooSmall {
                        required: 8,
                        available: buf.len(),
                    });
                }
                let n = i64::from_le_bytes(buf[0..8].try_into().unwrap());
                Ok((Value::Int64(n), 8))
            }
            type_oid::FLOAT4 => {
                if buf.len() < 4 {
                    return Err(SerdeError::BufferTooSmall {
                        required: 4,
                        available: buf.len(),
                    });
                }
                let n = f32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]);
                Ok((Value::Float32(n), 4))
            }
            type_oid::FLOAT8 => {
                if buf.len() < 8 {
                    return Err(SerdeError::BufferTooSmall {
                        required: 8,
                        available: buf.len(),
                    });
                }
                let n = f64::from_le_bytes(buf[0..8].try_into().unwrap());
                Ok((Value::Float64(n), 8))
            }
            type_oid::TEXT | type_oid::VARCHAR | type_oid::BPCHAR => {
                if buf.len() < 4 {
                    return Err(SerdeError::BufferTooSmall {
                        required: 4,
                        available: buf.len(),
                    });
                }
                let len = u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]) as usize;
                let required = 4 + len;
                if buf.len() < required {
                    return Err(SerdeError::BufferTooSmall {
                        required,
                        available: buf.len(),
                    });
                }
                let s = String::from_utf8(buf[4..4 + len].to_vec())
                    .map_err(|e| SerdeError::InvalidFormat(e.to_string()))?;
                Ok((Value::Text(s), required))
            }
            type_oid::BYTEA => {
                if buf.len() < 4 {
                    return Err(SerdeError::BufferTooSmall {
                        required: 4,
                        available: buf.len(),
                    });
                }
                let len = u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]) as usize;
                let required = 4 + len;
                if buf.len() < required {
                    return Err(SerdeError::BufferTooSmall {
                        required,
                        available: buf.len(),
                    });
                }
                Ok((Value::Bytea(buf[4..4 + len].to_vec()), required))
            }
            _ => Err(SerdeError::InvalidFormat(format!(
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
    fn test_type_oid() {
        assert_eq!(Value::Null.type_oid(), type_oid::UNKNOWN);
        assert_eq!(Value::Boolean(true).type_oid(), type_oid::BOOL);
        assert_eq!(Value::Int16(0).type_oid(), type_oid::INT2);
        assert_eq!(Value::Int32(0).type_oid(), type_oid::INT4);
        assert_eq!(Value::Int64(0).type_oid(), type_oid::INT8);
        assert_eq!(Value::Float32(0.0).type_oid(), type_oid::FLOAT4);
        assert_eq!(Value::Float64(0.0).type_oid(), type_oid::FLOAT8);
        assert_eq!(Value::Text(String::new()).type_oid(), type_oid::TEXT);
        assert_eq!(Value::Bytea(Vec::new()).type_oid(), type_oid::BYTEA);
    }

    #[test]
    fn test_is_null() {
        assert!(Value::Null.is_null());
        assert!(!Value::Boolean(false).is_null());
        assert!(!Value::Int32(0).is_null());
    }

    #[test]
    fn test_serialized_size() {
        assert_eq!(Value::Null.serialized_size(), 0);
        assert_eq!(Value::Boolean(true).serialized_size(), 1);
        assert_eq!(Value::Int16(0).serialized_size(), 2);
        assert_eq!(Value::Int32(0).serialized_size(), 4);
        assert_eq!(Value::Int64(0).serialized_size(), 8);
        assert_eq!(Value::Float32(0.0).serialized_size(), 4);
        assert_eq!(Value::Float64(0.0).serialized_size(), 8);
        assert_eq!(Value::Text("hello".to_string()).serialized_size(), 4 + 5);
        assert_eq!(Value::Bytea(vec![1, 2, 3]).serialized_size(), 4 + 3);
    }

    #[test]
    fn test_boolean_roundtrip() {
        for b in [true, false] {
            let original = Value::Boolean(b);
            let mut buf = vec![0u8; 1];
            let written = original.serialize(&mut buf).unwrap();
            assert_eq!(written, 1);
            let (parsed, consumed) = Value::deserialize(&buf, type_oid::BOOL).unwrap();
            assert_eq!(parsed, original);
            assert_eq!(consumed, written);
        }
    }

    #[test]
    fn test_int16_roundtrip() {
        for n in [0i16, 1, -1, i16::MIN, i16::MAX] {
            let original = Value::Int16(n);
            let mut buf = vec![0u8; 2];
            let written = original.serialize(&mut buf).unwrap();
            let (parsed, consumed) = Value::deserialize(&buf, type_oid::INT2).unwrap();
            assert_eq!(parsed, original);
            assert_eq!(consumed, written);
        }
    }

    #[test]
    fn test_int32_roundtrip() {
        for n in [0i32, 1, -1, i32::MIN, i32::MAX, 12345678] {
            let original = Value::Int32(n);
            let mut buf = vec![0u8; 4];
            let written = original.serialize(&mut buf).unwrap();
            let (parsed, consumed) = Value::deserialize(&buf, type_oid::INT4).unwrap();
            assert_eq!(parsed, original);
            assert_eq!(consumed, written);
        }
    }

    #[test]
    fn test_int64_roundtrip() {
        for n in [0i64, 1, -1, i64::MIN, i64::MAX, 123456789012345] {
            let original = Value::Int64(n);
            let mut buf = vec![0u8; 8];
            let written = original.serialize(&mut buf).unwrap();
            let (parsed, consumed) = Value::deserialize(&buf, type_oid::INT8).unwrap();
            assert_eq!(parsed, original);
            assert_eq!(consumed, written);
        }
    }

    #[test]
    fn test_float32_roundtrip() {
        for n in [0.0f32, 1.0, -1.0, 3.14159, f32::MIN, f32::MAX] {
            let original = Value::Float32(n);
            let mut buf = vec![0u8; 4];
            let written = original.serialize(&mut buf).unwrap();
            let (parsed, consumed) = Value::deserialize(&buf, type_oid::FLOAT4).unwrap();
            assert_eq!(parsed, original);
            assert_eq!(consumed, written);
        }
    }

    #[test]
    fn test_float64_roundtrip() {
        for n in [
            0.0f64,
            1.0,
            -1.0,
            std::f64::consts::PI,
            f64::MIN,
            f64::MAX,
        ] {
            let original = Value::Float64(n);
            let mut buf = vec![0u8; 8];
            let written = original.serialize(&mut buf).unwrap();
            let (parsed, consumed) = Value::deserialize(&buf, type_oid::FLOAT8).unwrap();
            assert_eq!(parsed, original);
            assert_eq!(consumed, written);
        }
    }

    #[test]
    fn test_text_roundtrip() {
        for s in ["", "hello", "hello world", "日本語", "🎉"] {
            let original = Value::Text(s.to_string());
            let mut buf = vec![0u8; original.serialized_size()];
            let written = original.serialize(&mut buf).unwrap();
            let (parsed, consumed) = Value::deserialize(&buf, type_oid::TEXT).unwrap();
            assert_eq!(parsed, original);
            assert_eq!(consumed, written);
        }
    }

    #[test]
    fn test_bytea_roundtrip() {
        for data in [
            vec![],
            vec![0],
            vec![1, 2, 3, 4, 5],
            vec![0, 255, 128, 64],
        ] {
            let original = Value::Bytea(data);
            let mut buf = vec![0u8; original.serialized_size()];
            let written = original.serialize(&mut buf).unwrap();
            let (parsed, consumed) = Value::deserialize(&buf, type_oid::BYTEA).unwrap();
            assert_eq!(parsed, original);
            assert_eq!(consumed, written);
        }
    }

    #[test]
    fn test_null_serialize() {
        let null = Value::Null;
        let mut buf = vec![0u8; 10];
        let written = null.serialize(&mut buf).unwrap();
        assert_eq!(written, 0);
    }

    #[test]
    fn test_buffer_too_small() {
        let value = Value::Int32(42);
        let mut buf = vec![0u8; 2]; // Need 4 bytes

        let result = value.serialize(&mut buf);
        assert!(matches!(
            result,
            Err(SerdeError::BufferTooSmall {
                required: 4,
                available: 2
            })
        ));
    }

    #[test]
    fn test_deserialize_unsupported_type() {
        let buf = vec![0u8; 8];
        let result = Value::deserialize(&buf, 9999);
        assert!(matches!(result, Err(SerdeError::InvalidFormat(_))));
    }

    #[test]
    fn test_text_varchar_bpchar_compatibility() {
        let s = "test";
        let original = Value::Text(s.to_string());
        let mut buf = vec![0u8; original.serialized_size()];
        original.serialize(&mut buf).unwrap();

        // All text-like types should deserialize the same
        let (v1, _) = Value::deserialize(&buf, type_oid::TEXT).unwrap();
        let (v2, _) = Value::deserialize(&buf, type_oid::VARCHAR).unwrap();
        let (v3, _) = Value::deserialize(&buf, type_oid::BPCHAR).unwrap();

        assert_eq!(v1, original);
        assert_eq!(v2, original);
        assert_eq!(v3, original);
    }

    #[test]
    fn test_invalid_utf8() {
        // Create a buffer with invalid UTF-8
        let mut buf = vec![0u8; 8];
        buf[0..4].copy_from_slice(&3u32.to_le_bytes()); // length = 3
        buf[4] = 0xFF; // Invalid UTF-8
        buf[5] = 0xFE;
        buf[6] = 0xFF;

        let result = Value::deserialize(&buf, type_oid::TEXT);
        assert!(matches!(result, Err(SerdeError::InvalidFormat(_))));
    }
}
