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

/// Type OIDs for common data types.
///
/// These values intentionally match PostgreSQL's type OIDs so that psql can correctly
/// interpret query results.
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
