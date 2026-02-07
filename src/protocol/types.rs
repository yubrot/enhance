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
