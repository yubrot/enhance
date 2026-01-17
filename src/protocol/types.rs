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

impl FormatCode {
    /// Creates a FormatCode from an i16 value.
    /// Returns None if the value is invalid.
    pub fn from_i16(value: i16) -> Option<Self> {
        match value {
            0 => Some(FormatCode::Text),
            1 => Some(FormatCode::Binary),
            _ => None,
        }
    }

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

impl ErrorFieldCode {
    /// Creates an ErrorFieldCode from a u8 value.
    /// Returns None if the value doesn't match any known field code.
    pub fn from_u8(value: u8) -> Option<Self> {
        match value {
            b'S' => Some(ErrorFieldCode::Severity),
            b'V' => Some(ErrorFieldCode::SeverityNonLocalized),
            b'C' => Some(ErrorFieldCode::SqlState),
            b'M' => Some(ErrorFieldCode::Message),
            b'D' => Some(ErrorFieldCode::Detail),
            b'H' => Some(ErrorFieldCode::Hint),
            b'P' => Some(ErrorFieldCode::Position),
            b'p' => Some(ErrorFieldCode::InternalPosition),
            b'q' => Some(ErrorFieldCode::InternalQuery),
            b'W' => Some(ErrorFieldCode::Where),
            b's' => Some(ErrorFieldCode::Schema),
            b't' => Some(ErrorFieldCode::Table),
            b'c' => Some(ErrorFieldCode::Column),
            b'd' => Some(ErrorFieldCode::DataType),
            b'n' => Some(ErrorFieldCode::Constraint),
            b'F' => Some(ErrorFieldCode::File),
            b'L' => Some(ErrorFieldCode::Line),
            b'R' => Some(ErrorFieldCode::Routine),
            _ => None,
        }
    }

    /// Converts the ErrorFieldCode to a u8 value.
    pub fn as_u8(self) -> u8 {
        self as u8
    }
}

/// PostgreSQL type OIDs for common data types.
///
/// NOTE: This is not an exhaustive list. PostgreSQL has hundreds of built-in types
/// plus user-defined types. These constants cover the most commonly used types.
/// See: https://github.com/postgres/postgres/blob/master/src/include/catalog/pg_type.dat
pub mod type_oid {
    /// Unknown type (used for type inference)
    pub const UNKNOWN: i32 = 0;

    // Boolean
    /// Boolean type
    pub const BOOL: i32 = 16;

    // Binary data
    /// Variable-length binary string
    pub const BYTEA: i32 = 17;

    // Character types
    /// Single character
    pub const CHAR: i32 = 18;
    /// Variable-length string
    pub const TEXT: i32 = 25;
    /// Variable-length string with limit
    pub const VARCHAR: i32 = 1043;
    /// Fixed-length string
    pub const BPCHAR: i32 = 1042;

    // Integer types
    /// 2-byte integer
    pub const INT2: i32 = 21;
    /// 4-byte integer
    pub const INT4: i32 = 23;
    /// 8-byte integer
    pub const INT8: i32 = 20;

    // Floating-point types
    /// Single-precision floating-point
    pub const FLOAT4: i32 = 700;
    /// Double-precision floating-point
    pub const FLOAT8: i32 = 701;

    // Numeric type
    /// Arbitrary precision numeric
    pub const NUMERIC: i32 = 1700;

    // Date/Time types
    /// Date (no time)
    pub const DATE: i32 = 1082;
    /// Time of day (no date)
    pub const TIME: i32 = 1083;
    /// Timestamp without timezone
    pub const TIMESTAMP: i32 = 1114;
    /// Timestamp with timezone
    pub const TIMESTAMPTZ: i32 = 1184;
    /// Time interval
    pub const INTERVAL: i32 = 1186;

    // JSON types
    /// JSON data
    pub const JSON: i32 = 114;
    /// Binary JSON data
    pub const JSONB: i32 = 3802;

    // UUID
    /// UUID type
    pub const UUID: i32 = 2950;

    // Network types
    /// IPv4 or IPv6 host address
    pub const INET: i32 = 869;
    /// IPv4 or IPv6 network
    pub const CIDR: i32 = 650;

    // Array types (base type OID + array flag, but commonly referenced)
    /// Array of INT4
    pub const INT4_ARRAY: i32 = 1007;
    /// Array of TEXT
    pub const TEXT_ARRAY: i32 = 1009;
}
