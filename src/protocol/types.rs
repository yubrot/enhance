//! Wire protocol type definitions.
//!
//! This module defines types and constants used by the PostgreSQL wire protocol
//! implementation. It serves as the canonical source for protocol-level constants
//! that other modules (e.g., `datum`, `executor`) reference.

/// PostgreSQL type OID constants for the wire protocol.
///
/// These OIDs identify data types in protocol messages such as `RowDescription`
/// and `ParameterDescription`.
///
/// References:
/// - <https://github.com/postgres/postgres/blob/master/src/include/catalog/pg_type.dat>
pub mod type_oid {
    /// `boolean` — logical boolean (true/false)
    pub const BOOL: i32 = 16;
    /// `bytea` — variable-length binary string
    pub const BYTEA: i32 = 17;
    /// `int8` — 8-byte signed integer
    pub const INT8: i32 = 20;
    /// `int2` — 2-byte signed integer
    pub const INT2: i32 = 21;
    /// `int4` — 4-byte signed integer
    pub const INT4: i32 = 23;
    /// `text` — variable-length string
    pub const TEXT: i32 = 25;
    /// `float4` — single-precision floating-point number
    pub const FLOAT4: i32 = 700;
    /// `float8` — double-precision floating-point number
    pub const FLOAT8: i32 = 701;
    /// `bpchar` — fixed-length blank-padded string (CHAR)
    pub const BPCHAR: i32 = 1042;
    /// `varchar` — variable-length string with limit
    pub const VARCHAR: i32 = 1043;
}

/// Format code for parameter and result values in the PostgreSQL protocol.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[repr(i16)]
pub enum FormatCode {
    /// Text format (0)
    #[default]
    Text = 0,
    /// Binary format (1)
    Binary = 1,
}

impl TryFrom<i16> for FormatCode {
    type Error = i16;

    fn try_from(value: i16) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(FormatCode::Text),
            1 => Ok(FormatCode::Binary),
            _ => Err(value),
        }
    }
}

impl FormatCode {
    /// Converts the FormatCode to an i16 value.
    pub fn as_i16(self) -> i16 {
        self as i16
    }
}

/// Error and notice message field type codes.
/// See: https://www.postgresql.org/docs/current/protocol-error-fields.html
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum ErrorFieldCode {
    /// Severity: ERROR, FATAL, PANIC, WARNING, NOTICE, DEBUG, INFO, LOG
    Severity = b'S',
    /// Severity (non-localized): Same as Severity but never localized
    SeverityNonLocalized = b'V',
    /// SQLSTATE code
    SqlState = b'C',
    /// Primary human-readable error message
    Message = b'M',
    /// Optional detail message
    Detail = b'D',
    /// Optional hint message
    Hint = b'H',
    /// Error cursor position in the original query string
    Position = b'P',
    /// Internal position (for internally generated queries)
    InternalPosition = b'p',
    /// Internal query
    InternalQuery = b'q',
    /// Context in which the error occurred
    Where = b'W',
    /// Schema name
    Schema = b's',
    /// Table name
    Table = b't',
    /// Column name
    Column = b'c',
    /// Data type name
    DataType = b'd',
    /// Constraint name
    Constraint = b'n',
    /// Source code file name
    File = b'F',
    /// Source code line number
    Line = b'L',
    /// Source code routine name
    Routine = b'R',
}

impl TryFrom<u8> for ErrorFieldCode {
    type Error = u8;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            b'S' => Ok(ErrorFieldCode::Severity),
            b'V' => Ok(ErrorFieldCode::SeverityNonLocalized),
            b'C' => Ok(ErrorFieldCode::SqlState),
            b'M' => Ok(ErrorFieldCode::Message),
            b'D' => Ok(ErrorFieldCode::Detail),
            b'H' => Ok(ErrorFieldCode::Hint),
            b'P' => Ok(ErrorFieldCode::Position),
            b'p' => Ok(ErrorFieldCode::InternalPosition),
            b'q' => Ok(ErrorFieldCode::InternalQuery),
            b'W' => Ok(ErrorFieldCode::Where),
            b's' => Ok(ErrorFieldCode::Schema),
            b't' => Ok(ErrorFieldCode::Table),
            b'c' => Ok(ErrorFieldCode::Column),
            b'd' => Ok(ErrorFieldCode::DataType),
            b'n' => Ok(ErrorFieldCode::Constraint),
            b'F' => Ok(ErrorFieldCode::File),
            b'L' => Ok(ErrorFieldCode::Line),
            b'R' => Ok(ErrorFieldCode::Routine),
            _ => Err(value),
        }
    }
}

impl ErrorFieldCode {
    /// Converts the ErrorFieldCode to a u8 value.
    pub fn as_u8(self) -> u8 {
        self as u8
    }
}
