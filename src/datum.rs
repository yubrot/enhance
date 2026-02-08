//! Database data types and values.
//!
//! This module defines the canonical type system and value representation
//! for the RDBMS. [`Type`] provides type-safe handling of data types, and
//! [`Value`] represents a single typed column value with serialization support.

use std::fmt;

use crate::protocol::types::type_oid;

/// Errors from data serialization/deserialization.
#[derive(Debug)]
pub enum SerializationError {
    /// Buffer too small for the operation.
    BufferTooSmall {
        /// Bytes required.
        required: usize,
        /// Bytes available.
        available: usize,
    },
    /// Invalid data format.
    InvalidFormat(String),
}

impl fmt::Display for SerializationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SerializationError::BufferTooSmall {
                required,
                available,
            } => {
                write!(
                    f,
                    "buffer too small: need {} bytes, have {}",
                    required, available
                )
            }
            SerializationError::InvalidFormat(msg) => {
                write!(f, "invalid format: {}", msg)
            }
        }
    }
}

impl std::error::Error for SerializationError {}

/// Returns `SerializationError::BufferTooSmall` if the buffer is too small.
#[macro_export]
macro_rules! ensure_buf_len {
    ($buf:expr, $required:expr) => {
        if $buf.len() < $required {
            return Err($crate::datum::SerializationError::BufferTooSmall {
                required: $required,
                available: $buf.len(),
            });
        }
    };
}

/// Database data type identifier.
///
/// Each variant maps to a PostgreSQL type OID defined in
/// [`protocol::types::type_oid`](crate::protocol::types::type_oid).
/// The OID mapping is provided by [`oid()`](Type::oid) and
/// [`TryFrom<i32>`](Type#impl-TryFrom<i32>-for-Type).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Type {
    /// Boolean type.
    Bool,
    /// Variable-length binary string.
    Bytea,
    /// 2-byte integer.
    Int2,
    /// 4-byte integer.
    Int4,
    /// 8-byte integer.
    Int8,
    /// Single-precision floating-point.
    Float4,
    /// Double-precision floating-point.
    Float8,
    /// Variable-length string.
    Text,
    /// Variable-length string with limit.
    Varchar,
    /// Fixed-length string.
    Bpchar,
}

impl Type {
    /// Returns the SQL display name for this type (e.g., `"BOOLEAN"`, `"INTEGER"`).
    pub const fn display_name(self) -> &'static str {
        match self {
            Type::Bool => "BOOLEAN",
            Type::Bytea => "BYTEA",
            Type::Int2 => "SMALLINT",
            Type::Int4 => "INTEGER",
            Type::Int8 => "BIGINT",
            Type::Float4 => "REAL",
            Type::Float8 => "DOUBLE PRECISION",
            Type::Text => "TEXT",
            Type::Varchar => "VARCHAR",
            Type::Bpchar => "CHAR",
        }
    }

    /// Returns the fixed byte size for fixed-length types, or `None` for variable-length types.
    pub const fn fixed_size(self) -> Option<usize> {
        match self {
            Type::Bool => Some(1),
            Type::Int2 => Some(2),
            Type::Int4 => Some(4),
            Type::Int8 => Some(8),
            Type::Float4 => Some(4),
            Type::Float8 => Some(8),
            Type::Text | Type::Varchar | Type::Bpchar | Type::Bytea => None,
        }
    }

    /// Returns the wire-protocol OID value.
    pub const fn oid(self) -> i32 {
        match self {
            Type::Bool => type_oid::BOOL,
            Type::Bytea => type_oid::BYTEA,
            Type::Int2 => type_oid::INT2,
            Type::Int4 => type_oid::INT4,
            Type::Int8 => type_oid::INT8,
            Type::Float4 => type_oid::FLOAT4,
            Type::Float8 => type_oid::FLOAT8,
            Type::Text => type_oid::TEXT,
            Type::Varchar => type_oid::VARCHAR,
            Type::Bpchar => type_oid::BPCHAR,
        }
    }

    /// Converts a wire-protocol OID value into a [`Type`].
    ///
    /// Returns `None` if the OID does not correspond to a known type.
    pub const fn from_oid(oid: i32) -> Option<Self> {
        match oid {
            type_oid::BOOL => Some(Type::Bool),
            type_oid::BYTEA => Some(Type::Bytea),
            type_oid::INT8 => Some(Type::Int8),
            type_oid::INT2 => Some(Type::Int2),
            type_oid::INT4 => Some(Type::Int4),
            type_oid::TEXT => Some(Type::Text),
            type_oid::FLOAT4 => Some(Type::Float4),
            type_oid::FLOAT8 => Some(Type::Float8),
            type_oid::BPCHAR => Some(Type::Bpchar),
            type_oid::VARCHAR => Some(Type::Varchar),
            _ => None,
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Type::Bool => "boolean",
            Type::Bytea => "bytea",
            Type::Int2 => "smallint",
            Type::Int4 => "integer",
            Type::Int8 => "bigint",
            Type::Float4 => "real",
            Type::Float8 => "double precision",
            Type::Text => "text",
            Type::Varchar => "character varying",
            Type::Bpchar => "character",
        };
        write!(f, "{}", name)
    }
}

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
    /// Returns the data type for this value, or `None` for Null.
    pub fn data_type(&self) -> Option<Type> {
        match self {
            Value::Null => None,
            Value::Boolean(_) => Some(Type::Bool),
            Value::Int16(_) => Some(Type::Int2),
            Value::Int32(_) => Some(Type::Int4),
            Value::Int64(_) => Some(Type::Int8),
            Value::Float32(_) => Some(Type::Float4),
            Value::Float64(_) => Some(Type::Float8),
            Value::Text(_) => Some(Type::Text),
            Value::Bytea(_) => Some(Type::Bytea),
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

    /// Deserializes a value from a buffer given its data type.
    ///
    /// Returns the value and the number of bytes consumed.
    ///
    /// # Errors
    ///
    /// Returns `SerializationError::BufferTooSmall` if the buffer is too small.
    /// Returns `SerializationError::InvalidFormat` for malformed data.
    pub fn deserialize(buf: &[u8], ty: Type) -> Result<(Self, usize), SerializationError> {
        match ty {
            Type::Bool => {
                ensure_buf_len!(buf, 1);
                Ok((Value::Boolean(buf[0] != 0), 1))
            }
            Type::Int2 => {
                ensure_buf_len!(buf, 2);
                let n = i16::from_le_bytes([buf[0], buf[1]]);
                Ok((Value::Int16(n), 2))
            }
            Type::Int4 => {
                ensure_buf_len!(buf, 4);
                let n = i32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]);
                Ok((Value::Int32(n), 4))
            }
            Type::Int8 => {
                ensure_buf_len!(buf, 8);
                let n = i64::from_le_bytes(buf[0..8].try_into().unwrap());
                Ok((Value::Int64(n), 8))
            }
            Type::Float4 => {
                ensure_buf_len!(buf, 4);
                let n = f32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]);
                Ok((Value::Float32(n), 4))
            }
            Type::Float8 => {
                ensure_buf_len!(buf, 8);
                let n = f64::from_le_bytes(buf[0..8].try_into().unwrap());
                Ok((Value::Float64(n), 8))
            }
            Type::Text | Type::Varchar | Type::Bpchar => {
                ensure_buf_len!(buf, 4);
                let len = u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]) as usize;
                let required = 4 + len;
                ensure_buf_len!(buf, required);
                let s = String::from_utf8(buf[4..4 + len].to_vec())
                    .map_err(|e| SerializationError::InvalidFormat(e.to_string()))?;
                Ok((Value::Text(s), required))
            }
            Type::Bytea => {
                ensure_buf_len!(buf, 4);
                let len = u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]) as usize;
                let required = 4 + len;
                ensure_buf_len!(buf, required);
                Ok((Value::Bytea(buf[4..4 + len].to_vec()), required))
            }
        }
    }

    /// Converts this value to its text representation.
    ///
    /// The output follows PostgreSQL text format conventions for wire protocol
    /// compatibility: booleans as `"t"`/`"f"`, bytea as hex with `"\\x"` prefix,
    /// and floats via [`format_float()`].
    pub fn to_text(&self) -> String {
        match self {
            Value::Null => String::new(),
            Value::Boolean(b) => (if *b { "t" } else { "f" }).to_string(),
            Value::Int16(n) => n.to_string(),
            Value::Int32(n) => n.to_string(),
            Value::Int64(n) => n.to_string(),
            Value::Float32(n) => format_float(*n as f64),
            Value::Float64(n) => format_float(*n),
            Value::Text(s) => s.clone(),
            Value::Bytea(b) => {
                let hex: String = b.iter().map(|byte| format!("{:02x}", byte)).collect();
                format!("\\x{}", hex)
            }
        }
    }
}

/// Formats a float value matching PostgreSQL output conventions.
///
/// Special values (`Infinity`, `-Infinity`, `NaN`) use PostgreSQL's
/// canonical text representation for wire protocol compatibility.
fn format_float(n: f64) -> String {
    if n.is_infinite() {
        if n.is_sign_positive() {
            "Infinity".to_string()
        } else {
            "-Infinity".to_string()
        }
    } else if n.is_nan() {
        "NaN".to_string()
    } else {
        // Use default Rust formatting which is close to PostgreSQL's output
        format!("{}", n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_oid_roundtrip() {
        let types = [
            Type::Bool,
            Type::Bytea,
            Type::Int2,
            Type::Int4,
            Type::Int8,
            Type::Float4,
            Type::Float8,
            Type::Text,
            Type::Varchar,
            Type::Bpchar,
        ];
        for ty in types {
            let oid = ty.oid();
            let parsed = Type::from_oid(oid).unwrap();
            assert_eq!(parsed, ty);
        }
    }

    #[test]
    fn test_type_from_oid_invalid() {
        assert_eq!(Type::from_oid(9999), None);
        assert_eq!(Type::from_oid(0), None);
    }

    #[test]
    fn test_type_fixed_size() {
        assert_eq!(Type::Bool.fixed_size(), Some(1));
        assert_eq!(Type::Int2.fixed_size(), Some(2));
        assert_eq!(Type::Int4.fixed_size(), Some(4));
        assert_eq!(Type::Int8.fixed_size(), Some(8));
        assert_eq!(Type::Float4.fixed_size(), Some(4));
        assert_eq!(Type::Float8.fixed_size(), Some(8));
        assert_eq!(Type::Text.fixed_size(), None);
        assert_eq!(Type::Varchar.fixed_size(), None);
        assert_eq!(Type::Bpchar.fixed_size(), None);
        assert_eq!(Type::Bytea.fixed_size(), None);
    }

    #[test]
    fn test_type_display() {
        assert_eq!(Type::Bool.to_string(), "boolean");
        assert_eq!(Type::Int4.to_string(), "integer");
        assert_eq!(Type::Text.to_string(), "text");
        assert_eq!(Type::Float8.to_string(), "double precision");
    }

    #[test]
    fn test_value_data_type() {
        assert_eq!(Value::Null.data_type(), None);
        assert_eq!(Value::Boolean(true).data_type(), Some(Type::Bool));
        assert_eq!(Value::Int16(0).data_type(), Some(Type::Int2));
        assert_eq!(Value::Int32(0).data_type(), Some(Type::Int4));
        assert_eq!(Value::Int64(0).data_type(), Some(Type::Int8));
        assert_eq!(Value::Float32(0.0).data_type(), Some(Type::Float4));
        assert_eq!(Value::Float64(0.0).data_type(), Some(Type::Float8));
        assert_eq!(Value::Text(String::new()).data_type(), Some(Type::Text));
        assert_eq!(Value::Bytea(vec![]).data_type(), Some(Type::Bytea));
    }

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
            let ty = value.data_type().unwrap();
            let mut buf = vec![0u8; value.serialized_size().max(1)];
            let written = value.serialize(&mut buf).unwrap();
            let (parsed, consumed) = Value::deserialize(&buf, ty).unwrap();
            assert_eq!(parsed, value);
            assert_eq!(consumed, written);
        }
    }

    #[test]
    fn test_null() {
        assert!(Value::Null.is_null());
        assert!(!Value::Int32(0).is_null());
        assert_eq!(Value::Null.serialized_size(), 0);
        assert_eq!(Value::Null.data_type(), None);
        assert_eq!(Value::Null.serialize(&mut [0u8; 1]).unwrap(), 0);
    }

    #[test]
    fn test_text_type_aliases() {
        let mut buf = vec![0u8; 8];
        Value::Text("test".into()).serialize(&mut buf).unwrap();
        for ty in [Type::Text, Type::Varchar, Type::Bpchar] {
            assert!(matches!(
                Value::deserialize(&buf, ty),
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
    fn test_invalid_utf8() {
        let mut buf = [0u8; 8];
        buf[..4].copy_from_slice(&3u32.to_le_bytes());
        buf[4..7].copy_from_slice(&[0xFF, 0xFE, 0xFF]);
        assert!(matches!(
            Value::deserialize(&buf, Type::Text),
            Err(SerializationError::InvalidFormat(_))
        ));
    }

    #[test]
    fn test_to_text() {
        assert_eq!(Value::Boolean(true).to_text(), "t");
        assert_eq!(Value::Boolean(false).to_text(), "f");
        assert_eq!(Value::Int32(42).to_text(), "42");
        assert_eq!(Value::Int64(100).to_text(), "100");
        assert_eq!(Value::Text("hello".into()).to_text(), "hello");
        assert_eq!(Value::Bytea(vec![0xDE, 0xAD]).to_text(), "\\xdead");
    }
}
