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

/// Reason for a failed [`Value::cast`] operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CastError {
    /// The value type cannot be cast to the target type.
    Invalid,
    /// The numeric value is out of range for the target type.
    NumericOutOfRange,
}

impl fmt::Display for CastError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CastError::Invalid => write!(f, "invalid cast"),
            CastError::NumericOutOfRange => write!(f, "numeric value out of range"),
        }
    }
}

impl std::error::Error for CastError {}

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
/// Each variant maps to a PostgreSQL type OID. See `oid` and `from_oid`.
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
#[derive(Debug, Clone)]
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

    /// Interprets this value as a nullable boolean.
    ///
    /// Returns `Ok(None)` for NULL, `Ok(Some(b))` for Boolean, and `Err(())`
    /// for any other type. The unit error signals a type mismatch without
    /// prescribing an error representation; callers map it to their own error.
    #[allow(clippy::result_unit_err)]
    pub fn to_bool_nullable(&self) -> Result<Option<bool>, ()> {
        match self {
            Value::Null => Ok(None),
            Value::Boolean(b) => Ok(Some(*b)),
            _ => Err(()),
        }
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

    /// Casts this value to the specified type.
    ///
    /// NULL passes through unchanged. On success, returns the converted value.
    /// On failure, returns the original value along with a [`CastError`]
    /// describing why the cast failed.
    ///
    /// Float-to-integer casts round to the nearest integer (ties away from
    /// zero) and return [`CastError::NumericOutOfRange`] for NaN, infinity,
    /// or values outside the target range.
    pub fn cast(self, target: &Type) -> Result<Value, (Value, CastError)> {
        if self.is_null() {
            return Ok(Value::Null);
        }
        match target {
            Type::Bool => match self {
                Value::Boolean(_) => Ok(self),
                Value::Text(s) => match s.to_lowercase().as_str() {
                    "true" | "t" | "yes" | "y" | "1" | "on" => Ok(Value::Boolean(true)),
                    "false" | "f" | "no" | "n" | "0" | "off" => Ok(Value::Boolean(false)),
                    _ => Err((Value::Text(s), CastError::Invalid)),
                },
                Value::Int16(n) => Ok(Value::Boolean(n != 0)),
                Value::Int32(n) => Ok(Value::Boolean(n != 0)),
                Value::Int64(n) => Ok(Value::Boolean(n != 0)),
                other => Err((other, CastError::Invalid)),
            },
            Type::Int2 => match self {
                Value::Int16(_) => Ok(self),
                Value::Int32(n) => i16::try_from(n)
                    .map(Value::Int16)
                    .map_err(|_| (Value::Int32(n), CastError::NumericOutOfRange)),
                Value::Int64(n) => i16::try_from(n)
                    .map(Value::Int16)
                    .map_err(|_| (Value::Int64(n), CastError::NumericOutOfRange)),
                Value::Float32(n) => cast_float_to_int(n as f64, i16::MIN as i64, i16::MAX as i64)
                    .map(|i| Value::Int16(i as i16))
                    .map_err(|e| (Value::Float32(n), e)),
                Value::Float64(n) => cast_float_to_int(n, i16::MIN as i64, i16::MAX as i64)
                    .map(|i| Value::Int16(i as i16))
                    .map_err(|e| (Value::Float64(n), e)),
                Value::Text(s) => match s.trim().parse::<i16>() {
                    Ok(n) => Ok(Value::Int16(n)),
                    Err(_) => Err((Value::Text(s), CastError::Invalid)),
                },
                Value::Boolean(b) => Ok(Value::Int16(if b { 1 } else { 0 })),
                other => Err((other, CastError::Invalid)),
            },
            Type::Int4 => match self {
                Value::Int32(_) => Ok(self),
                Value::Int16(n) => Ok(Value::Int32(n as i32)),
                Value::Int64(n) => i32::try_from(n)
                    .map(Value::Int32)
                    .map_err(|_| (Value::Int64(n), CastError::NumericOutOfRange)),
                Value::Float32(n) => cast_float_to_int(n as f64, i32::MIN as i64, i32::MAX as i64)
                    .map(|i| Value::Int32(i as i32))
                    .map_err(|e| (Value::Float32(n), e)),
                Value::Float64(n) => cast_float_to_int(n, i32::MIN as i64, i32::MAX as i64)
                    .map(|i| Value::Int32(i as i32))
                    .map_err(|e| (Value::Float64(n), e)),
                Value::Text(s) => match s.trim().parse::<i32>() {
                    Ok(n) => Ok(Value::Int32(n)),
                    Err(_) => Err((Value::Text(s), CastError::Invalid)),
                },
                Value::Boolean(b) => Ok(Value::Int32(if b { 1 } else { 0 })),
                other => Err((other, CastError::Invalid)),
            },
            Type::Int8 => match self {
                Value::Int64(_) => Ok(self),
                Value::Int16(n) => Ok(Value::Int64(n as i64)),
                Value::Int32(n) => Ok(Value::Int64(n as i64)),
                Value::Float32(n) => cast_float_to_int(n as f64, i64::MIN, i64::MAX)
                    .map(Value::Int64)
                    .map_err(|e| (Value::Float32(n), e)),
                Value::Float64(n) => cast_float_to_int(n, i64::MIN, i64::MAX)
                    .map(Value::Int64)
                    .map_err(|e| (Value::Float64(n), e)),
                Value::Text(s) => match s.trim().parse::<i64>() {
                    Ok(n) => Ok(Value::Int64(n)),
                    Err(_) => Err((Value::Text(s), CastError::Invalid)),
                },
                Value::Boolean(b) => Ok(Value::Int64(if b { 1 } else { 0 })),
                other => Err((other, CastError::Invalid)),
            },
            Type::Float4 => match self {
                Value::Float32(_) => Ok(self),
                Value::Float64(n) => {
                    let result = n as f32;
                    if result.is_infinite() && !n.is_infinite() {
                        Err((Value::Float64(n), CastError::NumericOutOfRange))
                    } else {
                        Ok(Value::Float32(result))
                    }
                }
                Value::Int16(n) => Ok(Value::Float32(n as f32)),
                Value::Int32(n) => Ok(Value::Float32(n as f32)),
                Value::Int64(n) => Ok(Value::Float32(n as f32)),
                Value::Text(s) => match s.trim().parse::<f32>() {
                    Ok(n) => Ok(Value::Float32(n)),
                    Err(_) => Err((Value::Text(s), CastError::Invalid)),
                },
                other => Err((other, CastError::Invalid)),
            },
            Type::Float8 => match self {
                Value::Float64(_) => Ok(self),
                Value::Float32(n) => Ok(Value::Float64(n as f64)),
                Value::Int16(n) => Ok(Value::Float64(n as f64)),
                Value::Int32(n) => Ok(Value::Float64(n as f64)),
                Value::Int64(n) => Ok(Value::Float64(n as f64)),
                Value::Text(s) => match s.trim().parse::<f64>() {
                    Ok(n) => Ok(Value::Float64(n)),
                    Err(_) => Err((Value::Text(s), CastError::Invalid)),
                },
                other => Err((other, CastError::Invalid)),
            },
            Type::Text | Type::Varchar | Type::Bpchar => match self {
                Value::Text(_) => Ok(self),
                other => Ok(Value::Text(other.to_text())),
            },
            Type::Bytea => match self {
                Value::Bytea(_) => Ok(self),
                Value::Text(s) => Ok(Value::Bytea(s.into_bytes())),
                other => Err((other, CastError::Invalid)),
            },
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

/// Casts a float to an integer value with rounding and range checking.
///
/// Rounds to the nearest integer (ties away from zero), then verifies the
/// result fits within `[min, max]`. Returns [`CastError::NumericOutOfRange`]
/// for NaN, infinity, or out-of-range values.
fn cast_float_to_int(n: f64, min: i64, max: i64) -> Result<i64, CastError> {
    if !n.is_finite() {
        return Err(CastError::NumericOutOfRange);
    }
    let rounded = n.round();
    // Use i128 for the range comparison to avoid f64 precision loss at i64
    // boundaries (i64::MAX is not exactly representable in f64).
    let wide = rounded as i128;
    if wide < min as i128 || wide > max as i128 {
        return Err(CastError::NumericOutOfRange);
    }
    Ok(wide as i64)
}

/// Widened numeric representation for cross-type numeric operations.
pub(crate) enum WideNumeric {
    /// 64-bit integer (widened from Int16, Int32, or Int64).
    Int64(i64),
    /// 64-bit float (widened from Float32 or Float64).
    Float64(f64),
}

/// Widens a numeric [`Value`] for cross-type operations.
///
/// Returns `None` for non-numeric types (Boolean, Text, Bytea, Null).
pub(crate) fn to_wide_numeric(v: &Value) -> Option<WideNumeric> {
    match v {
        Value::Int16(n) => Some(WideNumeric::Int64(*n as i64)),
        Value::Int32(n) => Some(WideNumeric::Int64(*n as i64)),
        Value::Int64(n) => Some(WideNumeric::Int64(*n)),
        Value::Float32(n) => Some(WideNumeric::Float64(*n as f64)),
        Value::Float64(n) => Some(WideNumeric::Float64(*n)),
        _ => None,
    }
}

/// Compares two f64 values with NaN-aware total ordering.
///
/// NaN is treated as greater than all non-NaN values, and NaN == NaN.
fn compare_f64(a: f64, b: f64) -> std::cmp::Ordering {
    match a.partial_cmp(&b) {
        Some(ord) => ord,
        None => match (a.is_nan(), b.is_nan()) {
            (true, true) => std::cmp::Ordering::Equal,
            (true, false) => std::cmp::Ordering::Greater,
            (false, true) => std::cmp::Ordering::Less,
            (false, false) => unreachable!(),
        },
    }
}

impl PartialEq for Value {
    /// Returns true when [`partial_cmp`](Self::partial_cmp) yields
    /// [`Ordering::Equal`](std::cmp::Ordering::Equal).
    ///
    /// This is intentionally consistent with `PartialOrd`: NULL is not equal
    /// to anything (including itself), and cross-type numeric promotion applies.
    fn eq(&self, other: &Self) -> bool {
        self.partial_cmp(other) == Some(std::cmp::Ordering::Equal)
    }
}

impl PartialOrd for Value {
    /// Compares two values with numeric type promotion.
    ///
    /// Returns `None` for incomparable types (e.g., Text vs Integer) and any
    /// comparison involving NULL.
    ///
    /// Numeric types are promoted to a common wide type before comparison:
    /// Int16/Int32 → Int64, Float32 → Float64, and if either operand is float
    /// both are compared as Float64.
    ///
    /// Float ordering follows NaN-aware total ordering: NaN is greater than all
    /// non-NaN values, and NaN == NaN.
    ///
    /// Boolean ordering: false < true.
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Value::Null, _) | (_, Value::Null) => None,
            (Value::Boolean(a), Value::Boolean(b)) => Some(a.cmp(b)),
            (Value::Text(a), Value::Text(b)) => Some(a.cmp(b)),
            (Value::Bytea(a), Value::Bytea(b)) => Some(a.cmp(b)),
            _ => {
                let l = to_wide_numeric(self)?;
                let r = to_wide_numeric(other)?;
                Some(match (l, r) {
                    (WideNumeric::Int64(a), WideNumeric::Int64(b)) => a.cmp(&b),
                    (WideNumeric::Float64(a), WideNumeric::Float64(b)) => compare_f64(a, b),
                    (WideNumeric::Float64(a), WideNumeric::Int64(b)) => compare_f64(a, b as f64),
                    (WideNumeric::Int64(a), WideNumeric::Float64(b)) => compare_f64(a as f64, b),
                })
            }
        }
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

    // ========================================================================
    // PartialOrd – cross-type comparison & numeric promotion
    // ========================================================================

    #[test]
    fn test_ordering_same_type_integers() {
        use std::cmp::Ordering;
        assert_eq!(
            Value::Int64(5).partial_cmp(&Value::Int64(5)),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Value::Int64(3).partial_cmp(&Value::Int64(5)),
            Some(Ordering::Less)
        );
        assert_eq!(
            Value::Int64(5).partial_cmp(&Value::Int64(3)),
            Some(Ordering::Greater)
        );
    }

    #[test]
    fn test_ordering_strings() {
        use std::cmp::Ordering;
        assert_eq!(
            Value::Text("abc".into()).partial_cmp(&Value::Text("abd".into())),
            Some(Ordering::Less)
        );
        assert_eq!(
            Value::Text("abc".into()).partial_cmp(&Value::Text("abc".into())),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Value::Text("b".into()).partial_cmp(&Value::Text("a".into())),
            Some(Ordering::Greater)
        );
    }

    #[test]
    fn test_ordering_booleans() {
        use std::cmp::Ordering;
        // false < true
        assert_eq!(
            Value::Boolean(false).partial_cmp(&Value::Boolean(true)),
            Some(Ordering::Less)
        );
        assert_eq!(
            Value::Boolean(true).partial_cmp(&Value::Boolean(true)),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Value::Boolean(false).partial_cmp(&Value::Boolean(false)),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Value::Boolean(true).partial_cmp(&Value::Boolean(false)),
            Some(Ordering::Greater)
        );
    }

    #[test]
    fn test_ordering_mixed_int_float() {
        use std::cmp::Ordering;
        assert_eq!(
            Value::Int64(5).partial_cmp(&Value::Float64(5.0)),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Value::Int64(5).partial_cmp(&Value::Float64(5.5)),
            Some(Ordering::Less)
        );
        assert_eq!(
            Value::Float64(5.5).partial_cmp(&Value::Int64(5)),
            Some(Ordering::Greater)
        );
    }

    #[test]
    fn test_ordering_cross_int_widths() {
        use std::cmp::Ordering;
        assert_eq!(
            Value::Int16(5).partial_cmp(&Value::Int64(5)),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Value::Int32(3).partial_cmp(&Value::Int64(5)),
            Some(Ordering::Less)
        );
    }

    #[test]
    fn test_ordering_nan() {
        use std::cmp::Ordering;
        let nan = Value::Float64(f64::NAN);
        let inf = Value::Float64(f64::INFINITY);
        let neg_inf = Value::Float64(f64::NEG_INFINITY);
        let zero = Value::Float64(0.0);

        // NaN > any non-NaN value
        assert_eq!(nan.partial_cmp(&zero), Some(Ordering::Greater));
        assert_eq!(nan.partial_cmp(&inf), Some(Ordering::Greater));
        assert_eq!(nan.partial_cmp(&neg_inf), Some(Ordering::Greater));

        // any non-NaN value < NaN
        assert_eq!(zero.partial_cmp(&nan), Some(Ordering::Less));
        assert_eq!(inf.partial_cmp(&nan), Some(Ordering::Less));
        assert_eq!(neg_inf.partial_cmp(&nan), Some(Ordering::Less));

        // NaN == NaN
        assert_eq!(nan.partial_cmp(&nan), Some(Ordering::Equal));

        // Cross-type: NaN > integer (promotion)
        assert_eq!(nan.partial_cmp(&Value::Int64(100)), Some(Ordering::Greater));
        assert_eq!(Value::Int64(100).partial_cmp(&nan), Some(Ordering::Less));
    }

    #[test]
    fn test_ordering_null() {
        // NULL is not comparable to anything
        assert_eq!(Value::Null.partial_cmp(&Value::Null), None);
        assert_eq!(Value::Null.partial_cmp(&Value::Int64(1)), None);
        assert_eq!(Value::Int64(1).partial_cmp(&Value::Null), None);
    }

    #[test]
    fn test_ordering_incompatible_types() {
        // Different type families are not comparable
        assert_eq!(
            Value::Text("abc".into()).partial_cmp(&Value::Int64(1)),
            None
        );
        assert_eq!(
            Value::Boolean(true).partial_cmp(&Value::Int64(1)),
            None
        );
        assert_eq!(
            Value::Boolean(true).partial_cmp(&Value::Text("true".into())),
            None
        );
    }

    // ========================================================================
    // Value::cast
    // ========================================================================

    #[test]
    fn test_cast_null_passthrough() {
        for ty in [
            Type::Bool,
            Type::Int2,
            Type::Int4,
            Type::Int8,
            Type::Float4,
            Type::Float8,
            Type::Text,
        ] {
            assert!(Value::Null.cast(&ty).unwrap().is_null(), "CAST(NULL AS {ty})");
        }
    }

    #[test]
    fn test_cast_bool_from_text() {
        for (input, expected) in [
            ("true", true),
            ("t", true),
            ("yes", true),
            ("1", true),
            ("on", true),
            ("false", false),
            ("f", false),
            ("no", false),
            ("0", false),
            ("off", false),
        ] {
            assert_eq!(
                Value::Text(input.into()).cast(&Type::Bool).unwrap(),
                Value::Boolean(expected),
                "CAST('{}' AS BOOLEAN)",
                input
            );
        }
    }

    #[test]
    fn test_cast_int_narrowing_overflow() {
        // Int64 → Int16: out of range
        assert!(matches!(
            Value::Int64(70000).cast(&Type::Int2),
            Err((_, CastError::NumericOutOfRange))
        ));
        assert!(matches!(
            Value::Int64(-70000).cast(&Type::Int2),
            Err((_, CastError::NumericOutOfRange))
        ));
        // Int32 → Int16: out of range
        assert!(matches!(
            Value::Int32(70000).cast(&Type::Int2),
            Err((_, CastError::NumericOutOfRange))
        ));
        // Int64 → Int32: out of range
        assert!(matches!(
            Value::Int64(3_000_000_000).cast(&Type::Int4),
            Err((_, CastError::NumericOutOfRange))
        ));

        // Boundary values should succeed
        assert_eq!(
            Value::Int64(i16::MAX as i64).cast(&Type::Int2).unwrap(),
            Value::Int16(i16::MAX)
        );
        assert_eq!(
            Value::Int64(i16::MIN as i64).cast(&Type::Int2).unwrap(),
            Value::Int16(i16::MIN)
        );
        assert_eq!(
            Value::Int64(i32::MAX as i64).cast(&Type::Int4).unwrap(),
            Value::Int32(i32::MAX)
        );
        assert_eq!(
            Value::Int64(i32::MIN as i64).cast(&Type::Int4).unwrap(),
            Value::Int32(i32::MIN)
        );
    }

    #[test]
    fn test_cast_float_to_int_rounds() {
        // Float rounds to nearest integer (ties away from zero)
        assert_eq!(
            Value::Float64(3.9).cast(&Type::Int8).unwrap(),
            Value::Int64(4)
        );
        assert_eq!(
            Value::Float64(-3.9).cast(&Type::Int8).unwrap(),
            Value::Int64(-4)
        );
        assert_eq!(
            Value::Float64(0.5).cast(&Type::Int8).unwrap(),
            Value::Int64(1)
        );
        assert_eq!(
            Value::Float64(-0.5).cast(&Type::Int8).unwrap(),
            Value::Int64(-1)
        );
        assert_eq!(
            Value::Float64(2.4).cast(&Type::Int4).unwrap(),
            Value::Int32(2)
        );
    }

    #[test]
    fn test_cast_float_to_int_overflow() {
        // Float too large for integer type
        assert!(matches!(
            Value::Float64(1e100).cast(&Type::Int8),
            Err((_, CastError::NumericOutOfRange))
        ));
        assert!(matches!(
            Value::Float64(f64::INFINITY).cast(&Type::Int8),
            Err((_, CastError::NumericOutOfRange))
        ));
        assert!(matches!(
            Value::Float64(f64::NAN).cast(&Type::Int4),
            Err((_, CastError::NumericOutOfRange))
        ));
        assert!(matches!(
            Value::Float64(40000.0).cast(&Type::Int2),
            Err((_, CastError::NumericOutOfRange))
        ));
    }

    #[test]
    fn test_cast_float64_to_float32_overflow() {
        // Float64 value too large for Float32
        assert!(matches!(
            Value::Float64(1.7976931348623157e308).cast(&Type::Float4),
            Err((_, CastError::NumericOutOfRange))
        ));
        // Infinity is preserved (not an overflow)
        assert_eq!(
            Value::Float64(f64::INFINITY).cast(&Type::Float4).unwrap(),
            Value::Float32(f32::INFINITY)
        );
        // NaN is preserved
        let result = Value::Float64(f64::NAN).cast(&Type::Float4).unwrap();
        assert!(matches!(result, Value::Float32(n) if n.is_nan()));
    }

    #[test]
    fn test_cast_text_to_numeric() {
        assert_eq!(
            Value::Text("42".into()).cast(&Type::Int4).unwrap(),
            Value::Int32(42)
        );
        assert_eq!(
            Value::Text(" -7 ".into()).cast(&Type::Int8).unwrap(),
            Value::Int64(-7)
        );
        assert_eq!(
            Value::Text("3.14".into()).cast(&Type::Float8).unwrap(),
            Value::Float64(3.14)
        );
    }

    #[test]
    fn test_cast_text_to_numeric_invalid() {
        assert!(matches!(
            Value::Text("abc".into()).cast(&Type::Int4),
            Err((_, CastError::Invalid))
        ));
        assert!(matches!(
            Value::Text("".into()).cast(&Type::Int8),
            Err((_, CastError::Invalid))
        ));
    }

    #[test]
    fn test_cast_to_text() {
        assert_eq!(
            Value::Int64(42).cast(&Type::Text).unwrap(),
            Value::Text("42".into())
        );
        assert_eq!(
            Value::Boolean(true).cast(&Type::Text).unwrap(),
            Value::Text("t".into())
        );
        assert_eq!(
            Value::Float64(3.14).cast(&Type::Text).unwrap(),
            Value::Text("3.14".into())
        );
    }

    #[test]
    fn test_cast_to_varchar() {
        assert_eq!(
            Value::Int64(42).cast(&Type::Varchar).unwrap(),
            Value::Text("42".into())
        );
    }

    #[test]
    fn test_cast_returns_original_value_on_error() {
        let Err((original, err)) = Value::Text("not_a_number".into()).cast(&Type::Int4) else {
            panic!("expected error");
        };
        assert_eq!(original, Value::Text("not_a_number".into()));
        assert_eq!(err, CastError::Invalid);
    }
}
