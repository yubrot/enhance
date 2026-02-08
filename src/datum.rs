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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Type {
    /// Boolean type.
    Bool,
    /// Variable-length binary string.
    Bytea,
    /// 2-byte integer.
    Smallint,
    /// 4-byte integer.
    Integer,
    /// 8-byte integer.
    Bigint,
    /// Single-precision floating-point.
    Real,
    /// Double-precision floating-point.
    DoublePrecision,
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
            Type::Smallint => "SMALLINT",
            Type::Integer => "INTEGER",
            Type::Bigint => "BIGINT",
            Type::Real => "REAL",
            Type::DoublePrecision => "DOUBLE PRECISION",
            Type::Text => "TEXT",
            Type::Varchar => "VARCHAR",
            Type::Bpchar => "CHAR",
        }
    }

    /// Returns the widened numeric [`Type`] that [`Value::to_wide_numeric`] would produce,
    /// or `None` for non-numeric types.
    ///
    /// This is the type-level counterpart of [`Value::to_wide_numeric`]: integer types
    /// widen to [`Bigint`](Type::Bigint) and floating-point types widen to
    /// [`Double`](Type::Double).
    pub const fn to_wide_numeric(self) -> Option<Type> {
        match self {
            Type::Smallint | Type::Integer | Type::Bigint => Some(Type::Bigint),
            Type::Real | Type::DoublePrecision => Some(Type::DoublePrecision),
            _ => None,
        }
    }

    /// Returns the fixed byte size for fixed-length types, or `None` for variable-length types.
    pub const fn fixed_size(self) -> Option<usize> {
        match self {
            Type::Bool => Some(1),
            Type::Smallint => Some(2),
            Type::Integer => Some(4),
            Type::Bigint => Some(8),
            Type::Real => Some(4),
            Type::DoublePrecision => Some(8),
            Type::Text | Type::Varchar | Type::Bpchar | Type::Bytea => None,
        }
    }

    /// Returns the wire-protocol OID value.
    pub const fn oid(self) -> i32 {
        match self {
            Type::Bool => type_oid::BOOL,
            Type::Bytea => type_oid::BYTEA,
            Type::Smallint => type_oid::INT2,
            Type::Integer => type_oid::INT4,
            Type::Bigint => type_oid::INT8,
            Type::Real => type_oid::FLOAT4,
            Type::DoublePrecision => type_oid::FLOAT8,
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
            type_oid::INT8 => Some(Type::Bigint),
            type_oid::INT2 => Some(Type::Smallint),
            type_oid::INT4 => Some(Type::Integer),
            type_oid::TEXT => Some(Type::Text),
            type_oid::FLOAT4 => Some(Type::Real),
            type_oid::FLOAT8 => Some(Type::DoublePrecision),
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
            Type::Smallint => "smallint",
            Type::Integer => "integer",
            Type::Bigint => "bigint",
            Type::Real => "real",
            Type::DoublePrecision => "double precision",
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
    Smallint(i16),
    /// 32-bit signed integer (INTEGER).
    Integer(i32),
    /// 64-bit signed integer (BIGINT).
    Bigint(i64),
    /// 32-bit floating point (REAL).
    Real(f32),
    /// 64-bit floating point (DOUBLE PRECISION).
    DoublePrecision(f64),
    /// Variable-length text (TEXT, VARCHAR).
    Text(String),
    /// Variable-length binary (BYTEA).
    Bytea(Vec<u8>),
}

impl Value {
    /// Returns true if this value is NULL.
    pub fn is_null(&self) -> bool {
        matches!(self, Value::Null)
    }

    /// Returns the type for this value, or `None` for Null.
    pub fn ty(&self) -> Option<Type> {
        match self {
            Value::Null => None,
            Value::Boolean(_) => Some(Type::Bool),
            Value::Smallint(_) => Some(Type::Smallint),
            Value::Integer(_) => Some(Type::Integer),
            Value::Bigint(_) => Some(Type::Bigint),
            Value::Real(_) => Some(Type::Real),
            Value::DoublePrecision(_) => Some(Type::DoublePrecision),
            Value::Text(_) => Some(Type::Text),
            Value::Bytea(_) => Some(Type::Bytea),
        }
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
            Value::Smallint(_) => 2,
            Value::Integer(_) => 4,
            Value::Bigint(_) => 8,
            Value::Real(_) => 4,
            Value::DoublePrecision(_) => 8,
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
            Value::Smallint(n) => {
                ensure_buf_len!(buf, 2);
                buf[0..2].copy_from_slice(&n.to_le_bytes());
                Ok(2)
            }
            Value::Integer(n) => {
                ensure_buf_len!(buf, 4);
                buf[0..4].copy_from_slice(&n.to_le_bytes());
                Ok(4)
            }
            Value::Bigint(n) => {
                ensure_buf_len!(buf, 8);
                buf[0..8].copy_from_slice(&n.to_le_bytes());
                Ok(8)
            }
            Value::Real(n) => {
                ensure_buf_len!(buf, 4);
                buf[0..4].copy_from_slice(&n.to_le_bytes());
                Ok(4)
            }
            Value::DoublePrecision(n) => {
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
            Type::Smallint => {
                ensure_buf_len!(buf, 2);
                let n = i16::from_le_bytes([buf[0], buf[1]]);
                Ok((Value::Smallint(n), 2))
            }
            Type::Integer => {
                ensure_buf_len!(buf, 4);
                let n = i32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]);
                Ok((Value::Integer(n), 4))
            }
            Type::Bigint => {
                ensure_buf_len!(buf, 8);
                let n = i64::from_le_bytes(buf[0..8].try_into().unwrap());
                Ok((Value::Bigint(n), 8))
            }
            Type::Real => {
                ensure_buf_len!(buf, 4);
                let n = f32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]);
                Ok((Value::Real(n), 4))
            }
            Type::DoublePrecision => {
                ensure_buf_len!(buf, 8);
                let n = f64::from_le_bytes(buf[0..8].try_into().unwrap());
                Ok((Value::DoublePrecision(n), 8))
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
            Value::Smallint(n) => n.to_string(),
            Value::Integer(n) => n.to_string(),
            Value::Bigint(n) => n.to_string(),
            Value::Real(n) => format_float(*n as f64),
            Value::DoublePrecision(n) => format_float(*n),
            Value::Text(s) => s.clone(),
            Value::Bytea(b) => {
                let hex: String = b.iter().map(|byte| format!("{:02x}", byte)).collect();
                format!("\\x{}", hex)
            }
        }
    }

    /// Widens a numeric value to [`Bigint`](Value::Bigint) or
    /// [`Double`](Value::Double) for cross-type operations.
    ///
    /// Integer types widen to `Bigint`, floating-point types widen to
    /// `Double`. Returns `None` for non-numeric types.
    /// [`Type::to_wide_numeric`] is the type-level counterpart.
    pub fn to_wide_numeric(&self) -> Option<Value> {
        match self {
            Value::Smallint(n) => Some(Value::Bigint(*n as i64)),
            Value::Integer(n) => Some(Value::Bigint(*n as i64)),
            Value::Bigint(n) => Some(Value::Bigint(*n)),
            Value::Real(n) => Some(Value::DoublePrecision(*n as f64)),
            Value::DoublePrecision(n) => Some(Value::DoublePrecision(*n)),
            _ => None,
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
                Value::Smallint(n) => Ok(Value::Boolean(n != 0)),
                Value::Integer(n) => Ok(Value::Boolean(n != 0)),
                Value::Bigint(n) => Ok(Value::Boolean(n != 0)),
                other => Err((other, CastError::Invalid)),
            },
            Type::Smallint => match self {
                Value::Smallint(_) => Ok(self),
                Value::Integer(n) => i16::try_from(n)
                    .map(Value::Smallint)
                    .map_err(|_| (Value::Integer(n), CastError::NumericOutOfRange)),
                Value::Bigint(n) => i16::try_from(n)
                    .map(Value::Smallint)
                    .map_err(|_| (Value::Bigint(n), CastError::NumericOutOfRange)),
                Value::Real(n) => cast_float_to_int(n as f64, i16::MIN as i64, i16::MAX as i64)
                    .map(|i| Value::Smallint(i as i16))
                    .map_err(|e| (Value::Real(n), e)),
                Value::DoublePrecision(n) => cast_float_to_int(n, i16::MIN as i64, i16::MAX as i64)
                    .map(|i| Value::Smallint(i as i16))
                    .map_err(|e| (Value::DoublePrecision(n), e)),
                Value::Text(s) => match s.trim().parse::<i16>() {
                    Ok(n) => Ok(Value::Smallint(n)),
                    Err(_) => Err((Value::Text(s), CastError::Invalid)),
                },
                Value::Boolean(b) => Ok(Value::Smallint(if b { 1 } else { 0 })),
                other => Err((other, CastError::Invalid)),
            },
            Type::Integer => match self {
                Value::Integer(_) => Ok(self),
                Value::Smallint(n) => Ok(Value::Integer(n as i32)),
                Value::Bigint(n) => i32::try_from(n)
                    .map(Value::Integer)
                    .map_err(|_| (Value::Bigint(n), CastError::NumericOutOfRange)),
                Value::Real(n) => cast_float_to_int(n as f64, i32::MIN as i64, i32::MAX as i64)
                    .map(|i| Value::Integer(i as i32))
                    .map_err(|e| (Value::Real(n), e)),
                Value::DoublePrecision(n) => cast_float_to_int(n, i32::MIN as i64, i32::MAX as i64)
                    .map(|i| Value::Integer(i as i32))
                    .map_err(|e| (Value::DoublePrecision(n), e)),
                Value::Text(s) => match s.trim().parse::<i32>() {
                    Ok(n) => Ok(Value::Integer(n)),
                    Err(_) => Err((Value::Text(s), CastError::Invalid)),
                },
                Value::Boolean(b) => Ok(Value::Integer(if b { 1 } else { 0 })),
                other => Err((other, CastError::Invalid)),
            },
            Type::Bigint => match self {
                Value::Bigint(_) => Ok(self),
                Value::Smallint(n) => Ok(Value::Bigint(n as i64)),
                Value::Integer(n) => Ok(Value::Bigint(n as i64)),
                Value::Real(n) => cast_float_to_int(n as f64, i64::MIN, i64::MAX)
                    .map(Value::Bigint)
                    .map_err(|e| (Value::Real(n), e)),
                Value::DoublePrecision(n) => cast_float_to_int(n, i64::MIN, i64::MAX)
                    .map(Value::Bigint)
                    .map_err(|e| (Value::DoublePrecision(n), e)),
                Value::Text(s) => match s.trim().parse::<i64>() {
                    Ok(n) => Ok(Value::Bigint(n)),
                    Err(_) => Err((Value::Text(s), CastError::Invalid)),
                },
                Value::Boolean(b) => Ok(Value::Bigint(if b { 1 } else { 0 })),
                other => Err((other, CastError::Invalid)),
            },
            Type::Real => match self {
                Value::Real(_) => Ok(self),
                Value::DoublePrecision(n) => {
                    let result = n as f32;
                    if result.is_infinite() && !n.is_infinite() {
                        Err((Value::DoublePrecision(n), CastError::NumericOutOfRange))
                    } else {
                        Ok(Value::Real(result))
                    }
                }
                Value::Smallint(n) => Ok(Value::Real(n as f32)),
                Value::Integer(n) => Ok(Value::Real(n as f32)),
                Value::Bigint(n) => Ok(Value::Real(n as f32)),
                Value::Text(s) => match s.trim().parse::<f32>() {
                    Ok(n) => Ok(Value::Real(n)),
                    Err(_) => Err((Value::Text(s), CastError::Invalid)),
                },
                other => Err((other, CastError::Invalid)),
            },
            Type::DoublePrecision => match self {
                Value::DoublePrecision(_) => Ok(self),
                Value::Real(n) => Ok(Value::DoublePrecision(n as f64)),
                Value::Smallint(n) => Ok(Value::DoublePrecision(n as f64)),
                Value::Integer(n) => Ok(Value::DoublePrecision(n as f64)),
                Value::Bigint(n) => Ok(Value::DoublePrecision(n as f64)),
                Value::Text(s) => match s.trim().parse::<f64>() {
                    Ok(n) => Ok(Value::DoublePrecision(n)),
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
    /// Smallint/Integer → Bigint, Real → Double, and if either operand
    /// s float both are compared as Double.
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
                let l = self.to_wide_numeric()?;
                let r = other.to_wide_numeric()?;
                match (l, r) {
                    (Value::Bigint(a), Value::Bigint(b)) => Some(a.cmp(&b)),
                    (Value::DoublePrecision(a), Value::DoublePrecision(b)) => {
                        Some(compare_f64(a, b))
                    }
                    (Value::DoublePrecision(a), Value::Bigint(b)) => Some(compare_f64(a, b as f64)),
                    (Value::Bigint(a), Value::DoublePrecision(b)) => Some(compare_f64(a as f64, b)),
                    _ => None,
                }
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
            Type::Smallint,
            Type::Integer,
            Type::Bigint,
            Type::Real,
            Type::DoublePrecision,
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
        assert_eq!(Type::Smallint.fixed_size(), Some(2));
        assert_eq!(Type::Integer.fixed_size(), Some(4));
        assert_eq!(Type::Bigint.fixed_size(), Some(8));
        assert_eq!(Type::Real.fixed_size(), Some(4));
        assert_eq!(Type::DoublePrecision.fixed_size(), Some(8));
        assert_eq!(Type::Text.fixed_size(), None);
        assert_eq!(Type::Varchar.fixed_size(), None);
        assert_eq!(Type::Bpchar.fixed_size(), None);
        assert_eq!(Type::Bytea.fixed_size(), None);
    }

    #[test]
    fn test_type_display() {
        assert_eq!(Type::Bool.to_string(), "boolean");
        assert_eq!(Type::Integer.to_string(), "integer");
        assert_eq!(Type::Text.to_string(), "text");
        assert_eq!(Type::DoublePrecision.to_string(), "double precision");
    }

    #[test]
    fn test_value_data_type() {
        assert_eq!(Value::Null.ty(), None);
        assert_eq!(Value::Boolean(true).ty(), Some(Type::Bool));
        assert_eq!(Value::Smallint(0).ty(), Some(Type::Smallint));
        assert_eq!(Value::Integer(0).ty(), Some(Type::Integer));
        assert_eq!(Value::Bigint(0).ty(), Some(Type::Bigint));
        assert_eq!(Value::Real(0.0).ty(), Some(Type::Real));
        assert_eq!(
            Value::DoublePrecision(0.0).ty(),
            Some(Type::DoublePrecision)
        );
        assert_eq!(Value::Text(String::new()).ty(), Some(Type::Text));
        assert_eq!(Value::Bytea(vec![]).ty(), Some(Type::Bytea));
    }

    #[test]
    fn test_roundtrip_all_types() {
        let values = [
            Value::Boolean(true),
            Value::Boolean(false),
            Value::Smallint(0),
            Value::Smallint(i16::MIN),
            Value::Smallint(i16::MAX),
            Value::Integer(0),
            Value::Integer(i32::MIN),
            Value::Integer(i32::MAX),
            Value::Bigint(0),
            Value::Bigint(i64::MIN),
            Value::Bigint(i64::MAX),
            Value::Real(0.0),
            Value::Real(std::f32::consts::PI),
            Value::DoublePrecision(0.0),
            Value::DoublePrecision(std::f64::consts::E),
            Value::Text(String::new()),
            Value::Text("hello 日本語 🎉".into()),
            Value::Bytea(vec![]),
            Value::Bytea(vec![0, 255, 128]),
        ];
        for value in values {
            let ty = value.ty().unwrap();
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
        assert!(!Value::Integer(0).is_null());
        assert_eq!(Value::Null.serialized_size(), 0);
        assert_eq!(Value::Null.ty(), None);
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
            Value::Integer(42).serialize(&mut buf),
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
        assert_eq!(Value::Integer(42).to_text(), "42");
        assert_eq!(Value::Bigint(100).to_text(), "100");
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
            Value::Bigint(5).partial_cmp(&Value::Bigint(5)),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Value::Bigint(3).partial_cmp(&Value::Bigint(5)),
            Some(Ordering::Less)
        );
        assert_eq!(
            Value::Bigint(5).partial_cmp(&Value::Bigint(3)),
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
            Value::Bigint(5).partial_cmp(&Value::DoublePrecision(5.0)),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Value::Bigint(5).partial_cmp(&Value::DoublePrecision(5.5)),
            Some(Ordering::Less)
        );
        assert_eq!(
            Value::DoublePrecision(5.5).partial_cmp(&Value::Bigint(5)),
            Some(Ordering::Greater)
        );
    }

    #[test]
    fn test_ordering_cross_int_widths() {
        use std::cmp::Ordering;
        assert_eq!(
            Value::Smallint(5).partial_cmp(&Value::Bigint(5)),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Value::Integer(3).partial_cmp(&Value::Bigint(5)),
            Some(Ordering::Less)
        );
    }

    #[test]
    fn test_ordering_nan() {
        use std::cmp::Ordering;
        let nan = Value::DoublePrecision(f64::NAN);
        let inf = Value::DoublePrecision(f64::INFINITY);
        let neg_inf = Value::DoublePrecision(f64::NEG_INFINITY);
        let zero = Value::DoublePrecision(0.0);

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
        assert_eq!(
            nan.partial_cmp(&Value::Bigint(100)),
            Some(Ordering::Greater)
        );
        assert_eq!(Value::Bigint(100).partial_cmp(&nan), Some(Ordering::Less));
    }

    #[test]
    fn test_ordering_null() {
        // NULL is not comparable to anything
        assert_eq!(Value::Null.partial_cmp(&Value::Null), None);
        assert_eq!(Value::Null.partial_cmp(&Value::Bigint(1)), None);
        assert_eq!(Value::Bigint(1).partial_cmp(&Value::Null), None);
    }

    #[test]
    fn test_ordering_incompatible_types() {
        // Different type families are not comparable
        assert_eq!(
            Value::Text("abc".into()).partial_cmp(&Value::Bigint(1)),
            None
        );
        assert_eq!(Value::Boolean(true).partial_cmp(&Value::Bigint(1)), None);
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
            Type::Smallint,
            Type::Integer,
            Type::Bigint,
            Type::Real,
            Type::DoublePrecision,
            Type::Text,
        ] {
            assert!(
                Value::Null.cast(&ty).unwrap().is_null(),
                "CAST(NULL AS {ty})"
            );
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
        // Bigint → Smallint: out of range
        assert!(matches!(
            Value::Bigint(70000).cast(&Type::Smallint),
            Err((_, CastError::NumericOutOfRange))
        ));
        assert!(matches!(
            Value::Bigint(-70000).cast(&Type::Smallint),
            Err((_, CastError::NumericOutOfRange))
        ));
        // Integer → Smallint: out of range
        assert!(matches!(
            Value::Integer(70000).cast(&Type::Smallint),
            Err((_, CastError::NumericOutOfRange))
        ));
        // Bigint → Integer: out of range
        assert!(matches!(
            Value::Bigint(3_000_000_000).cast(&Type::Integer),
            Err((_, CastError::NumericOutOfRange))
        ));

        // Boundary values should succeed
        assert_eq!(
            Value::Bigint(i16::MAX as i64)
                .cast(&Type::Smallint)
                .unwrap(),
            Value::Smallint(i16::MAX)
        );
        assert_eq!(
            Value::Bigint(i16::MIN as i64)
                .cast(&Type::Smallint)
                .unwrap(),
            Value::Smallint(i16::MIN)
        );
        assert_eq!(
            Value::Bigint(i32::MAX as i64).cast(&Type::Integer).unwrap(),
            Value::Integer(i32::MAX)
        );
        assert_eq!(
            Value::Bigint(i32::MIN as i64).cast(&Type::Integer).unwrap(),
            Value::Integer(i32::MIN)
        );
    }

    #[test]
    fn test_cast_float_to_int_rounds() {
        // Float rounds to nearest integer (ties away from zero)
        assert_eq!(
            Value::DoublePrecision(3.9).cast(&Type::Bigint).unwrap(),
            Value::Bigint(4)
        );
        assert_eq!(
            Value::DoublePrecision(-3.9).cast(&Type::Bigint).unwrap(),
            Value::Bigint(-4)
        );
        assert_eq!(
            Value::DoublePrecision(0.5).cast(&Type::Bigint).unwrap(),
            Value::Bigint(1)
        );
        assert_eq!(
            Value::DoublePrecision(-0.5).cast(&Type::Bigint).unwrap(),
            Value::Bigint(-1)
        );
        assert_eq!(
            Value::DoublePrecision(2.4).cast(&Type::Integer).unwrap(),
            Value::Integer(2)
        );
    }

    #[test]
    fn test_cast_float_to_int_overflow() {
        // Float too large for integer type
        assert!(matches!(
            Value::DoublePrecision(1e100).cast(&Type::Bigint),
            Err((_, CastError::NumericOutOfRange))
        ));
        assert!(matches!(
            Value::DoublePrecision(f64::INFINITY).cast(&Type::Bigint),
            Err((_, CastError::NumericOutOfRange))
        ));
        assert!(matches!(
            Value::DoublePrecision(f64::NAN).cast(&Type::Integer),
            Err((_, CastError::NumericOutOfRange))
        ));
        assert!(matches!(
            Value::DoublePrecision(40000.0).cast(&Type::Smallint),
            Err((_, CastError::NumericOutOfRange))
        ));
    }

    #[test]
    fn test_cast_double_to_real_overflow() {
        // Double value too large for Real
        assert!(matches!(
            Value::DoublePrecision(1.7976931348623157e308).cast(&Type::Real),
            Err((_, CastError::NumericOutOfRange))
        ));
        // Infinity is preserved (not an overflow)
        assert_eq!(
            Value::DoublePrecision(f64::INFINITY)
                .cast(&Type::Real)
                .unwrap(),
            Value::Real(f32::INFINITY)
        );
        // NaN is preserved
        let result = Value::DoublePrecision(f64::NAN).cast(&Type::Real).unwrap();
        assert!(matches!(result, Value::Real(n) if n.is_nan()));
    }

    #[test]
    fn test_cast_text_to_numeric() {
        assert_eq!(
            Value::Text("42".into()).cast(&Type::Integer).unwrap(),
            Value::Integer(42)
        );
        assert_eq!(
            Value::Text(" -7 ".into()).cast(&Type::Bigint).unwrap(),
            Value::Bigint(-7)
        );
        assert_eq!(
            Value::Text("3.14".into())
                .cast(&Type::DoublePrecision)
                .unwrap(),
            Value::DoublePrecision(3.14)
        );
    }

    #[test]
    fn test_cast_text_to_numeric_invalid() {
        assert!(matches!(
            Value::Text("abc".into()).cast(&Type::Integer),
            Err((_, CastError::Invalid))
        ));
        assert!(matches!(
            Value::Text("".into()).cast(&Type::Bigint),
            Err((_, CastError::Invalid))
        ));
    }

    #[test]
    fn test_cast_to_text() {
        assert_eq!(
            Value::Bigint(42).cast(&Type::Text).unwrap(),
            Value::Text("42".into())
        );
        assert_eq!(
            Value::Boolean(true).cast(&Type::Text).unwrap(),
            Value::Text("t".into())
        );
        assert_eq!(
            Value::DoublePrecision(3.14).cast(&Type::Text).unwrap(),
            Value::Text("3.14".into())
        );
    }

    #[test]
    fn test_cast_to_varchar() {
        assert_eq!(
            Value::Bigint(42).cast(&Type::Varchar).unwrap(),
            Value::Text("42".into())
        );
    }

    #[test]
    fn test_cast_returns_original_value_on_error() {
        let Err((original, err)) = Value::Text("not_a_number".into()).cast(&Type::Integer) else {
            panic!("expected error");
        };
        assert_eq!(original, Value::Text("not_a_number".into()));
        assert_eq!(err, CastError::Invalid);
    }
}
