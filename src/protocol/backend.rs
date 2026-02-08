use bytes::{BufMut, BytesMut};
use std::io;
use tokio_util::codec::Encoder;

use crate::protocol::codec::{PostgresCodec, StartupCodec, put_cstring};
use crate::protocol::types::{ErrorFieldCode, FormatCode};

/// SQL State codes for error responses.
///
/// References:
/// - <https://www.postgresql.org/docs/current/errcodes-appendix.html>
pub mod sql_state {
    // Class 08 - Connection Exception
    /// Connection exception (generic)
    pub const CONNECTION_EXCEPTION: &str = "08000";

    // Class 26 - Invalid SQL Statement Name
    /// Invalid SQL statement name (e.g., prepared statement does not exist)
    pub const INVALID_SQL_STATEMENT_NAME: &str = "26000";

    // Class 34 - Invalid Cursor Name
    /// Invalid cursor name (e.g., portal/cursor does not exist)
    pub const INVALID_CURSOR_NAME: &str = "34000";

    // Class 25 - Invalid Transaction State
    /// Current transaction is aborted, commands ignored until end of transaction block
    pub const IN_FAILED_SQL_TRANSACTION: &str = "25P02";

    // Class 42 - Syntax Error or Access Rule Violation
    /// Syntax error
    pub const SYNTAX_ERROR: &str = "42601";
    /// Undefined table
    pub const UNDEFINED_TABLE: &str = "42P01";
    /// Undefined column
    pub const UNDEFINED_COLUMN: &str = "42703";
    /// Undefined function
    pub const UNDEFINED_FUNCTION: &str = "42883";

    // Class XX - Internal Error
    /// Internal error
    pub const INTERNAL_ERROR: &str = "XX000";
}

/// Messages sent by the backend (server) to the client.
#[derive(Debug)]
pub enum BackendMessage {
    /// 'R' - Authentication response (AuthenticationOk)
    AuthenticationOk,
    /// 'K' - Backend key data for cancel requests
    BackendKeyData { process_id: i32, secret_key: i32 },
    /// 'S' - Parameter status notification
    ParameterStatus { name: String, value: String },
    /// 'Z' - Ready for query
    ReadyForQuery { status: TransactionStatus },
    /// 'E' - Error response
    ErrorResponse { fields: Vec<ErrorField> },
    /// 'T' - Row description (column metadata)
    RowDescription { fields: Vec<FieldDescription> },
    /// 'D' - Data row
    DataRow { values: Vec<DataValue> },
    /// 'C' - Command complete
    CommandComplete { tag: String },
    /// 'I' - Empty query response
    EmptyQueryResponse,
    /// '1' - Parse complete
    ParseComplete,
    /// '2' - Bind complete
    BindComplete,
    /// '3' - Close complete
    CloseComplete,
    /// 'n' - No data
    NoData,
    /// 's' - Portal suspended
    PortalSuspended,
    /// 't' - Parameter description
    ParameterDescription { param_types: Vec<i32> },
}

impl BackendMessage {
    /// Returns the message type byte.
    fn ty(&self) -> u8 {
        match self {
            BackendMessage::AuthenticationOk => b'R',
            BackendMessage::BackendKeyData { .. } => b'K',
            BackendMessage::ParameterStatus { .. } => b'S',
            BackendMessage::ReadyForQuery { .. } => b'Z',
            BackendMessage::ErrorResponse { .. } => b'E',
            BackendMessage::RowDescription { .. } => b'T',
            BackendMessage::DataRow { .. } => b'D',
            BackendMessage::CommandComplete { .. } => b'C',
            BackendMessage::EmptyQueryResponse => b'I',
            BackendMessage::ParseComplete => b'1',
            BackendMessage::BindComplete => b'2',
            BackendMessage::CloseComplete => b'3',
            BackendMessage::NoData => b'n',
            BackendMessage::PortalSuspended => b's',
            BackendMessage::ParameterDescription { .. } => b't',
        }
    }

    /// Encodes this message into the given BytesMut buffer.
    pub fn encode(&self, dst: &mut BytesMut) {
        dst.put_u8(self.ty());

        let len_pos = dst.len();
        dst.put_i32(0); // placeholder

        self.encode_body(dst);

        let total_len = (dst.len() - len_pos) as i32;
        dst[len_pos..][..4].copy_from_slice(&total_len.to_be_bytes());
    }

    /// Encodes the body of this message into the given BytesMut buffer.
    fn encode_body(&self, dst: &mut BytesMut) {
        match self {
            BackendMessage::AuthenticationOk => {
                dst.put_i32(0); // auth type 0 = Ok
            }
            BackendMessage::BackendKeyData {
                process_id,
                secret_key,
            } => {
                dst.put_i32(*process_id);
                dst.put_i32(*secret_key);
            }
            BackendMessage::ParameterStatus { name, value } => {
                put_cstring(dst, name);
                put_cstring(dst, value);
            }
            BackendMessage::ReadyForQuery { status } => {
                dst.put_u8(status.as_byte());
            }
            BackendMessage::ErrorResponse { fields } => {
                for field in fields {
                    field.encode(dst);
                }
                dst.put_u8(0); // terminator
            }
            BackendMessage::RowDescription { fields } => {
                dst.put_i16(fields.len() as i16);
                for field in fields {
                    field.encode(dst);
                }
            }
            BackendMessage::DataRow { values } => {
                dst.put_i16(values.len() as i16);
                for value in values {
                    value.encode(dst);
                }
            }
            BackendMessage::CommandComplete { tag } => {
                put_cstring(dst, tag);
            }
            BackendMessage::EmptyQueryResponse
            | BackendMessage::ParseComplete
            | BackendMessage::BindComplete
            | BackendMessage::CloseComplete
            | BackendMessage::NoData
            | BackendMessage::PortalSuspended => {
                // No body for these messages
            }
            BackendMessage::ParameterDescription { param_types } => {
                dst.put_i16(param_types.len() as i16);
                for oid in param_types {
                    dst.put_i32(*oid);
                }
            }
        }
    }
}

impl Encoder<BackendMessage> for StartupCodec {
    type Error = io::Error;

    fn encode(&mut self, msg: BackendMessage, dst: &mut BytesMut) -> Result<(), Self::Error> {
        msg.encode(dst);
        Ok(())
    }
}

impl Encoder<BackendMessage> for PostgresCodec {
    type Error = io::Error;

    fn encode(&mut self, msg: BackendMessage, dst: &mut BytesMut) -> Result<(), Self::Error> {
        msg.encode(dst);
        Ok(())
    }
}

/// Transaction status indicator for ReadyForQuery message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransactionStatus {
    /// 'I' - Idle (not in a transaction block)
    Idle,
    /// 'T' - In a transaction block
    InTransaction,
    /// 'E' - In a failed transaction block
    Failed,
}

impl TransactionStatus {
    fn as_byte(self) -> u8 {
        match self {
            TransactionStatus::Idle => b'I',
            TransactionStatus::InTransaction => b'T',
            TransactionStatus::Failed => b'E',
        }
    }
}

/// Error/Notice field.
#[derive(Debug)]
pub struct ErrorField {
    pub code: ErrorFieldCode,
    pub value: String,
}

impl ErrorField {
    /// Creates a new error field.
    pub fn new(code: ErrorFieldCode, value: impl Into<String>) -> Self {
        Self {
            code,
            value: value.into(),
        }
    }

    /// Encodes this error field into the given BytesMut buffer.
    fn encode(&self, dst: &mut BytesMut) {
        dst.put_u8(self.code.as_u8());
        put_cstring(dst, &self.value);
    }
}

/// Structured error information for PostgreSQL error responses.
///
/// PostgreSQL error responses have required fields (severity, SQL state, message)
/// and optional fields (position, detail, hint, etc.). This struct provides a
/// builder-style API for constructing well-formed error responses.
///
/// # Examples
///
/// ```rust
/// use enhance::protocol::{ErrorInfo, sql_state};
///
/// // Simple error (severity defaults to "ERROR")
/// let err = ErrorInfo::new(sql_state::UNDEFINED_TABLE, "table does not exist");
///
/// // Error with position (for syntax errors)
/// let err = ErrorInfo::new(sql_state::SYNTAX_ERROR, "unexpected token")
///     .with_position(15);
///
/// // Fatal error
/// let err = ErrorInfo::new(sql_state::CONNECTION_EXCEPTION, "connection lost")
///     .with_severity("FATAL");
/// ```
#[derive(Debug, Clone)]
pub struct ErrorInfo {
    /// Severity level (ERROR, FATAL, PANIC, WARNING, NOTICE, DEBUG, INFO, LOG)
    pub severity: &'static str,
    /// SQLSTATE code (e.g., "42P01" for undefined table)
    pub code: &'static str,
    /// Primary human-readable error message
    pub message: String,
    /// Error cursor position in the original query string (1-indexed)
    pub position: Option<usize>,
}

impl ErrorInfo {
    /// Creates a new error with the required fields.
    ///
    /// Severity defaults to "ERROR".
    pub fn new(code: &'static str, message: impl Into<String>) -> Self {
        Self {
            severity: "ERROR",
            code,
            message: message.into(),
            position: None,
        }
    }

    /// Sets the severity level.
    ///
    /// Common values: "ERROR", "FATAL", "PANIC", "WARNING", "NOTICE", "DEBUG", "INFO", "LOG"
    pub fn with_severity(mut self, severity: &'static str) -> Self {
        self.severity = severity;
        self
    }

    /// Adds position information to this error.
    ///
    /// The position is 1-indexed, indicating the character position in the
    /// original query string where the error occurred.
    pub fn with_position(mut self, position: usize) -> Self {
        self.position = Some(position);
        self
    }
}

impl From<ErrorInfo> for BackendMessage {
    fn from(info: ErrorInfo) -> Self {
        let mut fields = vec![
            ErrorField::new(ErrorFieldCode::Severity, info.severity),
            ErrorField::new(ErrorFieldCode::SeverityNonLocalized, info.severity),
            ErrorField::new(ErrorFieldCode::SqlState, info.code),
            ErrorField::new(ErrorFieldCode::Message, info.message),
        ];

        if let Some(pos) = info.position {
            fields.push(ErrorField::new(ErrorFieldCode::Position, pos.to_string()));
        }

        BackendMessage::ErrorResponse { fields }
    }
}

/// A single column value in a data row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DataValue {
    /// SQL NULL value (encoded as length -1)
    Null,
    /// Non-NULL value (encoded as length + data bytes)
    Data(Vec<u8>),
}

impl DataValue {
    /// Encodes this data value into the given BytesMut buffer.
    fn encode(&self, dst: &mut BytesMut) {
        match self {
            DataValue::Null => dst.put_i32(-1),
            DataValue::Data(bytes) => {
                dst.put_i32(bytes.len() as i32);
                dst.put_slice(bytes);
            }
        }
    }
}

/// Field description for RowDescription message.
#[derive(Debug, Clone)]
pub struct FieldDescription {
    /// Column name
    pub name: String,
    /// Table OID (0 if not from a table)
    pub table_oid: i32,
    /// Column attribute number (0 if not from a table)
    pub column_id: i16,
    /// Data type OID
    pub type_oid: i32,
    /// Data type size (-1 for variable length)
    pub type_size: i16,
    /// Type modifier (-1 if not applicable)
    pub type_modifier: i32,
    /// Format code
    pub format_code: FormatCode,
}

impl FieldDescription {
    /// Encodes this field description into the given BytesMut buffer.
    fn encode(&self, dst: &mut BytesMut) {
        put_cstring(dst, &self.name);
        dst.put_i32(self.table_oid);
        dst.put_i16(self.column_id);
        dst.put_i32(self.type_oid);
        dst.put_i16(self.type_size);
        dst.put_i32(self.type_modifier);
        dst.put_i16(self.format_code.as_i16());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bytes::BytesMut;
    use tokio_util::codec::Encoder;

    use crate::datum::Type;

    /// Helper to encode a message and return the buffer.
    fn encode_message(msg: BackendMessage) -> Vec<u8> {
        let mut codec = PostgresCodec::new();
        let mut buf = BytesMut::new();
        codec.encode(msg, &mut buf).unwrap();
        buf.to_vec()
    }

    /// Helper to read i32 from buffer at offset.
    fn read_i32(buf: &[u8], offset: usize) -> i32 {
        i32::from_be_bytes([
            buf[offset],
            buf[offset + 1],
            buf[offset + 2],
            buf[offset + 3],
        ])
    }

    /// Helper to read i16 from buffer at offset.
    fn read_i16(buf: &[u8], offset: usize) -> i16 {
        i16::from_be_bytes([buf[offset], buf[offset + 1]])
    }

    #[test]
    fn test_write_authentication_ok() {
        let msg = BackendMessage::AuthenticationOk;
        let buf = encode_message(msg);
        assert_eq!(buf, vec![b'R', 0, 0, 0, 8, 0, 0, 0, 0]);
    }

    #[test]
    fn test_write_backend_key_data() {
        let msg = BackendMessage::BackendKeyData {
            process_id: 12345,
            secret_key: 67890,
        };
        let buf = encode_message(msg);

        assert_eq!(buf[0], b'K');
        assert_eq!(read_i32(&buf, 1), 12); // length = 4 + 8 = 12
        assert_eq!(read_i32(&buf, 5), 12345); // process_id
        assert_eq!(read_i32(&buf, 9), 67890); // secret_key
    }

    #[test]
    fn test_write_parameter_status() {
        let msg = BackendMessage::ParameterStatus {
            name: "server_version".to_string(),
            value: "16.0".to_string(),
        };
        let buf = encode_message(msg);

        assert_eq!(buf[0], b'S');
        assert_eq!(read_i32(&buf, 1), 24); // length = 4 + 15 + 5 = 24
        assert_eq!(&buf[5..], b"server_version\x0016.0\x00");
    }

    #[test]
    fn test_write_ready_for_query() {
        let msg = BackendMessage::ReadyForQuery {
            status: TransactionStatus::Idle,
        };
        let buf = encode_message(msg);
        assert_eq!(buf, vec![b'Z', 0, 0, 0, 5, b'I']);
    }

    #[test]
    fn test_write_error_response() {
        let error = ErrorInfo::new(sql_state::UNDEFINED_TABLE, "table does not exist");
        let msg: BackendMessage = error.into();
        let buf = encode_message(msg);

        assert_eq!(buf[0], b'E');
        assert_eq!(read_i32(&buf, 1), 48); // 4 + (7 + 7 + 7 + 22 + 1)

        // Verify fields
        assert_eq!(buf[5], b'S'); // Severity
        assert_eq!(&buf[6..12], b"ERROR\x00");
        assert_eq!(buf[12], b'V'); // SeverityNonLocalized
        assert_eq!(&buf[13..19], b"ERROR\x00");
        assert_eq!(buf[19], b'C'); // SqlState
        assert_eq!(&buf[20..26], b"42P01\x00");
        assert_eq!(buf[26], b'M'); // Message
        assert_eq!(&buf[27..48], b"table does not exist\x00");
        assert_eq!(buf[48], 0); // terminator
    }

    #[test]
    fn test_write_error_response_with_position() {
        let error = ErrorInfo::new(sql_state::SYNTAX_ERROR, "unexpected token").with_position(15);
        let msg: BackendMessage = error.into();
        let buf = encode_message(msg);

        assert_eq!(buf[0], b'E');
        // Verify position field is included
        // Fields: S=ERROR(7), V=ERROR(7), C=42601(7), M=unexpected token(18), P=15(4)
        // Total: 4 + 7 + 7 + 7 + 18 + 4 + 1 = 48
        assert_eq!(read_i32(&buf, 1), 48);
    }

    #[test]
    fn test_write_row_description() {
        let msg = BackendMessage::RowDescription {
            fields: vec![
                FieldDescription {
                    name: "col".to_string(),
                    table_oid: 0,
                    column_id: 0,
                    type_oid: Type::Integer.oid(),
                    type_size: 4,
                    type_modifier: -1,
                    format_code: FormatCode::Text,
                },
                FieldDescription {
                    name: "text_col".to_string(),
                    table_oid: 16384,
                    column_id: 2,
                    type_oid: Type::Text.oid(),
                    type_size: -1,
                    type_modifier: -1,
                    format_code: FormatCode::Text,
                },
                FieldDescription {
                    name: "binary_col".to_string(),
                    table_oid: 16384,
                    column_id: 3,
                    type_oid: Type::Bytea.oid(),
                    type_size: -1,
                    type_modifier: -1,
                    format_code: FormatCode::Binary,
                },
            ],
        };
        let buf = encode_message(msg);

        assert_eq!(buf[0], b'T');
        assert_eq!(read_i16(&buf, 5), 3); // field count
    }

    #[test]
    fn test_write_data_row() {
        let msg = BackendMessage::DataRow {
            values: vec![
                DataValue::Data(b"hello".to_vec()), // non-empty value
                DataValue::Data(vec![]),            // empty value
                DataValue::Null,                    // NULL
            ],
        };
        let buf = encode_message(msg);

        assert_eq!(buf[0], b'D');
        assert_eq!(read_i16(&buf, 5), 3); // column count

        // Verify values
        assert_eq!(read_i32(&buf, 7), 5); // length of "hello"
        assert_eq!(&buf[11..16], b"hello");
        assert_eq!(read_i32(&buf, 16), 0); // empty value
        assert_eq!(read_i32(&buf, 20), -1); // NULL
    }

    #[test]
    fn test_write_command_complete() {
        let msg = BackendMessage::CommandComplete {
            tag: "SELECT 1".to_string(),
        };
        let buf = encode_message(msg);

        assert_eq!(buf[0], b'C');
        assert_eq!(read_i32(&buf, 1), 13); // 4 + 9
        assert_eq!(&buf[5..], b"SELECT 1\x00");
    }

    #[test]
    fn test_write_empty_query_response() {
        let msg = BackendMessage::EmptyQueryResponse;
        let buf = encode_message(msg);
        assert_eq!(buf, vec![b'I', 0, 0, 0, 4]);
    }

    #[test]
    fn test_write_parse_complete() {
        let msg = BackendMessage::ParseComplete;
        let buf = encode_message(msg);
        assert_eq!(buf, vec![b'1', 0, 0, 0, 4]);
    }

    #[test]
    fn test_write_bind_complete() {
        let msg = BackendMessage::BindComplete;
        let buf = encode_message(msg);
        assert_eq!(buf, vec![b'2', 0, 0, 0, 4]);
    }

    #[test]
    fn test_write_close_complete() {
        let msg = BackendMessage::CloseComplete;
        let buf = encode_message(msg);
        assert_eq!(buf, vec![b'3', 0, 0, 0, 4]);
    }

    #[test]
    fn test_write_no_data() {
        let msg = BackendMessage::NoData;
        let buf = encode_message(msg);
        assert_eq!(buf, vec![b'n', 0, 0, 0, 4]);
    }

    #[test]
    fn test_write_portal_suspended() {
        let msg = BackendMessage::PortalSuspended;
        let buf = encode_message(msg);
        assert_eq!(buf, vec![b's', 0, 0, 0, 4]);
    }

    #[test]
    fn test_write_parameter_description() {
        let msg = BackendMessage::ParameterDescription {
            param_types: vec![Type::Integer.oid(), Type::Text.oid(), Type::Varchar.oid()],
        };
        let buf = encode_message(msg);

        assert_eq!(buf[0], b't');
        assert_eq!(read_i32(&buf, 1), 18); // 4 + 2 + 3*4
        assert_eq!(read_i16(&buf, 5), 3); // param count
        assert_eq!(read_i32(&buf, 7), Type::Integer.oid());
        assert_eq!(read_i32(&buf, 11), Type::Text.oid());
        assert_eq!(read_i32(&buf, 15), Type::Varchar.oid());
    }
}
