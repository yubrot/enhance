use bytes::{Buf, BytesMut};
use std::collections::HashMap;
use tokio_util::codec::Decoder;

use crate::protocol::codec::{PostgresCodec, StartupCodec, get_cstring, get_nullable_bytes};
use crate::protocol::error::ProtocolError;
use crate::protocol::types::FormatCode;

/// Ensures that the buffer has at least `n` bytes remaining.
/// Returns `ProtocolError::InvalidMessage` if not enough bytes are available.
macro_rules! ensure_remaining {
    ($buf:expr, $n:expr) => {
        if $buf.len() < $n {
            return Err(ProtocolError::InvalidMessage);
        }
    };
}

/// SSLRequest magic number
const SSL_REQUEST_CODE: i32 = (1234 << 16) | 5679; // 80877103

/// GSSENCRequest magic number
const GSSENC_REQUEST_CODE: i32 = (1234 << 16) | 5680; // 80877104

/// CancelRequest magic number
const CANCEL_REQUEST_CODE: i32 = (1234 << 16) | 5678; // 80877102

const MAX_PARAMS: usize = 10000;
const MAX_FORMAT_CODES: usize = 10000;
const MAX_RESULT_FORMATS: usize = 10000;

/// Messages sent by the frontend (client) during startup phase.
#[derive(Debug)]
pub enum StartupMessage {
    /// SSLRequest - client wants to negotiate SSL
    SslRequest,
    /// GSSENCRequest - client wants GSSAPI encryption
    GssEncRequest,
    /// CancelRequest - client wants to cancel a query
    CancelRequest { process_id: i32, secret_key: i32 },
    /// StartupMessage - normal connection startup
    Startup {
        protocol_version: i32,
        parameters: StartupParameters,
    },
}

impl StartupMessage {
    /// Decodes a startup message from the buffer.
    /// The buffer should contain a complete message (length and code already validated).
    fn decode(src: &mut BytesMut) -> Result<Self, ProtocolError> {
        // Read length and code
        let _len = src.get_i32();
        let code = src.get_i32();

        match code {
            SSL_REQUEST_CODE => Ok(StartupMessage::SslRequest),
            GSSENC_REQUEST_CODE => Ok(StartupMessage::GssEncRequest),
            CANCEL_REQUEST_CODE => {
                ensure_remaining!(src, 8);
                let process_id = src.get_i32();
                let secret_key = src.get_i32();
                Ok(StartupMessage::CancelRequest {
                    process_id,
                    secret_key,
                })
            }
            version if (version >> 16) == 3 => {
                let parameters = StartupParameters::decode(src)?;
                Ok(StartupMessage::Startup {
                    protocol_version: version,
                    parameters,
                })
            }
            _ => Err(ProtocolError::UnsupportedProtocolVersion(code)),
        }
    }
}

/// Startup parameters from the client
#[derive(Debug, Clone, Default)]
pub struct StartupParameters {
    pub user: String,
    pub database: Option<String>,
    pub application_name: Option<String>,
    pub client_encoding: Option<String>,
    pub other: HashMap<String, String>,
}

impl StartupParameters {
    /// Decodes startup parameters from the message buffer.
    fn decode(src: &mut BytesMut) -> Result<Self, ProtocolError> {
        let mut params = StartupParameters::default();

        loop {
            // Check if we have more data
            if src.is_empty() {
                break;
            }

            // Read parameter name
            let name = get_cstring(src)?;

            // Empty name signals end of parameters
            if name.is_empty() {
                break;
            }

            // Read parameter value
            let value = get_cstring(src)?;

            match name.as_str() {
                "user" => params.user = value,
                "database" => params.database = Some(value),
                "application_name" => params.application_name = Some(value),
                "client_encoding" => params.client_encoding = Some(value),
                _ => {
                    params.other.insert(name, value);
                }
            }
        }

        if params.user.is_empty() {
            return Err(ProtocolError::MissingParameter("user"));
        }

        Ok(params)
    }
}

impl Decoder for StartupCodec {
    type Item = StartupMessage;
    type Error = ProtocolError;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        // Need at least 8 bytes (length + code)
        if src.len() < 8 {
            return Ok(None);
        }

        // Peek at the length (don't consume yet)
        let len = i32::from_be_bytes([src[0], src[1], src[2], src[3]]) as usize;
        if len < 8 || len > self.max_message_size {
            return Err(ProtocolError::InvalidMessage);
        }

        // Wait for complete message
        if src.len() < len {
            return Ok(None);
        }

        // Ready to decode - consume the message and decode it
        let mut msg_buf = src.split_to(len);
        let msg = StartupMessage::decode(&mut msg_buf)?;
        Ok(Some(msg))
    }
}

/// Messages sent by the frontend (client) during query phase.
///
/// NOTE: Production improvements needed:
/// - Add maximum query length limit (PostgreSQL uses 1GB max)
/// - Consider query sanitization/logging (redact sensitive data)
#[derive(Debug)]
pub enum FrontendMessage {
    /// 'Q' - Simple query
    Query(String),
    /// 'X' - Termination
    Terminate,
    /// 'P' - Parse (create prepared statement)
    Parse(ParseMessage),
    /// 'B' - Bind (bind parameters to create portal)
    Bind(BindMessage),
    /// 'D' - Describe (get statement/portal metadata)
    Describe(DescribeMessage),
    /// 'E' - Execute (execute a portal)
    Execute(ExecuteMessage),
    /// 'C' - Close (close statement/portal)
    Close(CloseMessage),
    /// 'S' - Sync (end implicit transaction)
    Sync,
    /// 'H' - Flush (flush output)
    Flush,
}

impl FrontendMessage {
    /// Decodes a frontend message from the buffer.
    /// The buffer should contain the message body (type and length already consumed).
    fn decode(src: &mut BytesMut) -> Result<Self, ProtocolError> {
        let msg_type = src.get_u8();
        let _length = src.get_i32();
        match msg_type {
            b'Q' => {
                let query = get_cstring(src)?;
                Ok(FrontendMessage::Query(query))
            }
            b'X' => Ok(FrontendMessage::Terminate),
            b'P' => Ok(FrontendMessage::Parse(ParseMessage::decode(src)?)),
            b'B' => Ok(FrontendMessage::Bind(BindMessage::decode(src)?)),
            b'D' => Ok(FrontendMessage::Describe(DescribeMessage::decode(src)?)),
            b'E' => Ok(FrontendMessage::Execute(ExecuteMessage::decode(src)?)),
            b'C' => Ok(FrontendMessage::Close(CloseMessage::decode(src)?)),
            b'S' => Ok(FrontendMessage::Sync),
            b'H' => Ok(FrontendMessage::Flush),
            _ => Err(ProtocolError::UnknownMessageType(msg_type)),
        }
    }
}

/// Parse message - creates a prepared statement
#[derive(Debug, Clone)]
pub struct ParseMessage {
    /// Name of the prepared statement (empty string = unnamed)
    pub statement_name: String,
    /// SQL query string
    pub query: String,
    /// Parameter type OIDs (may be empty, server infers types)
    pub param_types: Vec<i32>,
}

impl ParseMessage {
    /// Decodes a Parse message from the buffer.
    fn decode(src: &mut BytesMut) -> Result<Self, ProtocolError> {
        let statement_name = get_cstring(src)?;
        let query = get_cstring(src)?;

        ensure_remaining!(src, 2);
        let param_count = src.get_i16() as usize;
        if param_count > MAX_PARAMS {
            return Err(ProtocolError::InvalidMessage);
        }

        ensure_remaining!(src, param_count * 4);
        let mut param_types = Vec::with_capacity(param_count);
        for _ in 0..param_count {
            param_types.push(src.get_i32());
        }

        Ok(ParseMessage {
            statement_name,
            query,
            param_types,
        })
    }
}

/// Bind message - binds parameters to create a portal
#[derive(Debug, Clone)]
pub struct BindMessage {
    /// Destination portal name (empty = unnamed)
    pub portal_name: String,
    /// Source prepared statement name
    pub statement_name: String,
    /// Parameter format codes
    pub param_format_codes: Vec<FormatCode>,
    /// Parameter values (None = NULL)
    pub param_values: Vec<Option<Vec<u8>>>,
    /// Result column format codes
    pub result_format_codes: Vec<FormatCode>,
}

impl BindMessage {
    /// Decodes a Bind message from the buffer.
    fn decode(src: &mut BytesMut) -> Result<Self, ProtocolError> {
        let portal_name = get_cstring(src)?;
        let statement_name = get_cstring(src)?;

        // Parameter format codes
        ensure_remaining!(src, 2);
        let format_count = src.get_i16() as usize;
        if format_count > MAX_FORMAT_CODES {
            return Err(ProtocolError::InvalidMessage);
        }

        ensure_remaining!(src, format_count * 2);
        let mut param_format_codes = Vec::with_capacity(format_count);
        for _ in 0..format_count {
            let code = src.get_i16();
            let format = FormatCode::try_from(code).map_err(|_| ProtocolError::InvalidMessage)?;
            param_format_codes.push(format);
        }

        // Parameter values
        ensure_remaining!(src, 2);
        let param_count = src.get_i16() as usize;
        if param_count > MAX_PARAMS {
            return Err(ProtocolError::InvalidMessage);
        }

        let mut param_values = Vec::with_capacity(param_count);
        for _ in 0..param_count {
            let value = get_nullable_bytes(src)?;
            param_values.push(value);
        }

        // Result format codes
        ensure_remaining!(src, 2);
        let result_format_count = src.get_i16() as usize;
        if result_format_count > MAX_RESULT_FORMATS {
            return Err(ProtocolError::InvalidMessage);
        }

        ensure_remaining!(src, result_format_count * 2);
        let mut result_format_codes = Vec::with_capacity(result_format_count);
        for _ in 0..result_format_count {
            let code = src.get_i16();
            let format = FormatCode::try_from(code).map_err(|_| ProtocolError::InvalidMessage)?;
            result_format_codes.push(format);
        }

        Ok(BindMessage {
            portal_name,
            statement_name,
            param_format_codes,
            param_values,
            result_format_codes,
        })
    }
}

/// Describe message - request metadata about statement or portal
#[derive(Debug, Clone)]
pub struct DescribeMessage {
    /// Target type: Statement or Portal
    pub target_type: DescribeTarget,
    /// Name of the statement or portal
    pub name: String,
}

impl DescribeMessage {
    /// Decodes a Describe message from the buffer.
    fn decode(src: &mut BytesMut) -> Result<Self, ProtocolError> {
        ensure_remaining!(src, 1);
        let target_byte = src.get_u8();
        let target_type = match target_byte {
            b'S' => DescribeTarget::Statement,
            b'P' => DescribeTarget::Portal,
            _ => return Err(ProtocolError::InvalidMessage),
        };
        let name = get_cstring(src)?;
        Ok(DescribeMessage { target_type, name })
    }
}

/// Describe message target type
#[derive(Debug, Clone, Copy)]
pub enum DescribeTarget {
    /// 'S' - Describe a prepared statement
    Statement,
    /// 'P' - Describe a portal
    Portal,
}

/// Execute message - execute a portal
#[derive(Debug, Clone)]
pub struct ExecuteMessage {
    /// Portal name (empty = unnamed)
    pub portal_name: String,
    /// Maximum rows to return (0 = unlimited)
    pub max_rows: i32,
}

impl ExecuteMessage {
    /// Decodes an Execute message from the buffer.
    fn decode(src: &mut BytesMut) -> Result<Self, ProtocolError> {
        let portal_name = get_cstring(src)?;
        ensure_remaining!(src, 4);
        let max_rows = src.get_i32();
        Ok(ExecuteMessage {
            portal_name,
            max_rows,
        })
    }
}

/// Close message - close a statement or portal
#[derive(Debug, Clone)]
pub struct CloseMessage {
    /// Target type: Statement or Portal
    pub target_type: CloseTarget,
    /// Name of the statement or portal
    pub name: String,
}

impl CloseMessage {
    /// Decodes a Close message from the buffer.
    fn decode(src: &mut BytesMut) -> Result<Self, ProtocolError> {
        ensure_remaining!(src, 1);
        let target_byte = src.get_u8();
        let target_type = match target_byte {
            b'S' => CloseTarget::Statement,
            b'P' => CloseTarget::Portal,
            _ => return Err(ProtocolError::InvalidMessage),
        };
        let name = get_cstring(src)?;
        Ok(CloseMessage { target_type, name })
    }
}

/// Close message target type
#[derive(Debug, Clone, Copy)]
pub enum CloseTarget {
    /// 'S' - Close a prepared statement
    Statement,
    /// 'P' - Close a portal
    Portal,
}

impl Decoder for PostgresCodec {
    type Item = FrontendMessage;
    type Error = ProtocolError;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        // Need at least 5 bytes (type + length)
        if src.len() < 5 {
            return Ok(None);
        }

        // Peek at the length (bytes 1-4, don't consume yet)
        let len = i32::from_be_bytes([src[1], src[2], src[3], src[4]]) as usize;
        if len < 4 || len > self.max_message_size {
            return Err(ProtocolError::InvalidMessage);
        }

        // Total message size = 1 (type byte) + length
        let len = 1 + len;

        // Wait for complete message
        if src.len() < len {
            return Ok(None);
        }

        // Ready to decode - consume the message and decode it
        let mut msg_buf = src.split_to(len);
        let msg = FrontendMessage::decode(&mut msg_buf)?;
        Ok(Some(msg))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bytes::{BufMut, BytesMut};
    use tokio_util::codec::Decoder;

    use crate::protocol::type_oid;

    /// Helper to create a startup message with given code and body
    fn make_startup_message(code: i32, body: &[u8]) -> Vec<u8> {
        let mut buf = Vec::new();
        let len = 4 + 4 + body.len(); // length + code + body
        buf.put_i32(len as i32);
        buf.put_i32(code);
        buf.extend_from_slice(body);
        buf
    }

    /// Helper to create a frontend message with given type and body
    fn make_frontend_message(msg_type: u8, body: &[u8]) -> Vec<u8> {
        let mut buf = Vec::new();
        buf.push(msg_type);
        let len = 4 + body.len(); // length includes self (4 bytes) + body
        buf.put_i32(len as i32);
        buf.extend_from_slice(body);
        buf
    }

    /// Helper to decode a StartupMessage from bytes
    fn decode_startup_message(buf: &[u8]) -> Result<Option<StartupMessage>, ProtocolError> {
        let mut codec = StartupCodec::new();
        let mut bytes = BytesMut::from(buf);
        codec.decode(&mut bytes)
    }

    /// Helper to decode a FrontendMessage from bytes
    fn decode_frontend_message(buf: &[u8]) -> Result<Option<FrontendMessage>, ProtocolError> {
        let mut codec = PostgresCodec::new();
        let mut bytes = BytesMut::from(buf);
        codec.decode(&mut bytes)
    }

    #[test]
    fn test_read_ssl_request() {
        let buf = make_startup_message(SSL_REQUEST_CODE, &[]);
        let msg = decode_startup_message(&buf).unwrap();
        assert!(matches!(msg, Some(StartupMessage::SslRequest)));
    }

    #[test]
    fn test_read_startup_message() {
        let mut body = Vec::new();
        body.extend_from_slice(b"user\0postgres\0");
        body.extend_from_slice(b"database\0testdb\0");
        body.push(0); // terminator

        let buf = make_startup_message(3 << 16, &body);
        let msg = decode_startup_message(&buf).unwrap();

        let Some(StartupMessage::Startup {
            protocol_version,
            parameters,
        }) = msg
        else {
            panic!("expected Startup message, got {msg:?}")
        };

        assert_eq!(protocol_version, 3 << 16);
        assert_eq!(parameters.user, "postgres");
        assert_eq!(parameters.database, Some("testdb".to_string()));
    }

    #[test]
    fn test_read_startup_message_missing_user() {
        let mut body = Vec::new();
        body.extend_from_slice(b"database\0testdb\0");
        body.push(0); // terminator

        let buf = make_startup_message(3 << 16, &body);
        let result = decode_startup_message(&buf);

        assert!(matches!(
            result,
            Err(ProtocolError::MissingParameter("user"))
        ));
    }

    #[test]
    fn test_read_gssenc_request() {
        let buf = make_startup_message(GSSENC_REQUEST_CODE, &[]);
        let msg = decode_startup_message(&buf).unwrap();
        assert!(matches!(msg, Some(StartupMessage::GssEncRequest)));
    }

    #[test]
    fn test_read_cancel_request() {
        let mut body = Vec::new();
        body.put_i32(12345); // process_id
        body.put_i32(67890); // secret_key

        let buf = make_startup_message(CANCEL_REQUEST_CODE, &body);
        let msg = decode_startup_message(&buf).unwrap();

        let Some(StartupMessage::CancelRequest {
            process_id,
            secret_key,
        }) = msg
        else {
            panic!("expected CancelRequest message, got {msg:?}")
        };

        assert_eq!(process_id, 12345);
        assert_eq!(secret_key, 67890);
    }

    #[test]
    fn test_read_eof() {
        let buf = Vec::new();
        let msg = decode_frontend_message(&buf).unwrap();
        assert!(msg.is_none());
    }

    #[test]
    fn test_read_unknown_message_type() {
        let mut buf = Vec::new();
        buf.push(b'Z'); // Unknown type
        buf.put_i32(4);

        let result = decode_frontend_message(&buf);
        assert!(matches!(
            result,
            Err(ProtocolError::UnknownMessageType(b'Z'))
        ));
    }

    #[test]
    fn test_read_query_message() {
        let buf = make_frontend_message(b'Q', b"SELECT 1\0");
        let msg = decode_frontend_message(&buf).unwrap().unwrap();

        let FrontendMessage::Query(q) = msg else {
            panic!("expected Query message, got {msg:?}")
        };

        assert_eq!(q, "SELECT 1");
    }

    #[test]
    fn test_read_terminate_message() {
        let buf = make_frontend_message(b'X', &[]);
        let msg = decode_frontend_message(&buf).unwrap().unwrap();
        assert!(matches!(msg, FrontendMessage::Terminate));
    }

    #[test]
    fn test_read_parse_message() {
        let mut body = Vec::new();
        body.push(0); // empty (unnamed) statement - commonly used in PostgreSQL
        body.extend_from_slice(b"SELECT $1, $2\0");
        body.put_i16(2); // 2 parameters
        body.put_i32(type_oid::INT4);
        body.put_i32(type_oid::TEXT);

        let buf = make_frontend_message(b'P', &body);
        let msg = decode_frontend_message(&buf).unwrap().unwrap();

        let FrontendMessage::Parse(parse) = msg else {
            panic!("expected Parse message, got {msg:?}")
        };

        assert_eq!(parse.statement_name, ""); // unnamed statement
        assert_eq!(parse.query, "SELECT $1, $2");
        assert_eq!(parse.param_types, vec![type_oid::INT4, type_oid::TEXT]);
    }

    #[test]
    fn test_read_parse_message_named() {
        let mut body = Vec::new();
        body.extend_from_slice(b"portal\0");
        body.extend_from_slice(b"SELECT $1\0");
        body.put_i16(1);
        body.put_i32(type_oid::INT4);

        let buf = make_frontend_message(b'P', &body);
        let msg = decode_frontend_message(&buf).unwrap().unwrap();

        let FrontendMessage::Parse(parse) = msg else {
            panic!("expected Parse message, got {msg:?}")
        };

        assert_eq!(parse.statement_name, "portal");
        assert_eq!(parse.query, "SELECT $1");
        assert_eq!(parse.param_types, vec![type_oid::INT4]);
    }

    #[test]
    fn test_read_bind_message() {
        let mut body = Vec::new();
        body.extend_from_slice(b"portal\0"); // portal_name
        body.extend_from_slice(b"stmt\0"); // statement_name
        body.put_i16(1); // format_count
        body.put_i16(0); // format code (text)
        body.put_i16(3); // param_count: 3 params (non-NULL, NULL, non-NULL)
        body.put_i32(2); // first param length
        body.extend_from_slice(b"42"); // first param value
        body.put_i32(-1); // second param is NULL (-1)
        body.put_i32(5); // third param length
        body.extend_from_slice(b"hello"); // third param value
        body.put_i16(1); // result_format_count
        body.put_i16(0); // result format code

        let buf = make_frontend_message(b'B', &body);
        let msg = decode_frontend_message(&buf).unwrap().unwrap();

        let FrontendMessage::Bind(bind) = msg else {
            panic!("expected Bind message, got {msg:?}")
        };

        assert_eq!(bind.portal_name, "portal");
        assert_eq!(bind.statement_name, "stmt");
        assert_eq!(bind.param_format_codes, vec![FormatCode::Text]);
        assert_eq!(bind.param_values.len(), 3);
        assert_eq!(bind.param_values[0], Some(b"42".to_vec()));
        assert_eq!(bind.param_values[1], None); // NULL parameter
        assert_eq!(bind.param_values[2], Some(b"hello".to_vec()));
        assert_eq!(bind.result_format_codes, vec![FormatCode::Text]);
    }

    #[test]
    fn test_read_describe_statement() {
        let body = vec![b'S', 0]; // Statement, empty (unnamed) statement

        let buf = make_frontend_message(b'D', &body);
        let msg = decode_frontend_message(&buf).unwrap().unwrap();

        let FrontendMessage::Describe(desc) = msg else {
            panic!("expected Describe message, got {msg:?}")
        };

        assert!(matches!(desc.target_type, DescribeTarget::Statement));
        assert_eq!(desc.name, ""); // unnamed statement
    }

    #[test]
    fn test_read_describe_portal() {
        let mut body = Vec::new();
        body.push(b'P'); // Portal
        body.extend_from_slice(b"portal\0");

        let buf = make_frontend_message(b'D', &body);
        let msg = decode_frontend_message(&buf).unwrap().unwrap();

        let FrontendMessage::Describe(desc) = msg else {
            panic!("expected Describe message, got {msg:?}")
        };

        assert!(matches!(desc.target_type, DescribeTarget::Portal));
        assert_eq!(desc.name, "portal");
    }

    #[test]
    fn test_read_execute_message() {
        let mut body = Vec::new();
        body.push(0); // empty (unnamed) portal - commonly used in PostgreSQL
        body.put_i32(100); // max_rows

        let buf = make_frontend_message(b'E', &body);
        let msg = decode_frontend_message(&buf).unwrap().unwrap();

        let FrontendMessage::Execute(exec) = msg else {
            panic!("expected Execute message, got {msg:?}")
        };

        assert_eq!(exec.portal_name, ""); // unnamed portal
        assert_eq!(exec.max_rows, 100);
    }

    #[test]
    fn test_read_close_statement() {
        let body = vec![b'S', 0]; // Statement, empty (unnamed) statement

        let buf = make_frontend_message(b'C', &body);
        let msg = decode_frontend_message(&buf).unwrap().unwrap();

        let FrontendMessage::Close(close) = msg else {
            panic!("expected Close message, got {msg:?}")
        };

        assert!(matches!(close.target_type, CloseTarget::Statement));
        assert_eq!(close.name, ""); // unnamed statement
    }

    #[test]
    fn test_read_close_portal() {
        let body = vec![b'P', 0]; // Portal, empty (unnamed) portal

        let buf = make_frontend_message(b'C', &body);
        let msg = decode_frontend_message(&buf).unwrap().unwrap();

        let FrontendMessage::Close(close) = msg else {
            panic!("expected Close message, got {msg:?}")
        };

        assert!(matches!(close.target_type, CloseTarget::Portal));
        assert_eq!(close.name, ""); // unnamed portal
    }

    #[test]
    fn test_read_sync_message() {
        let buf = make_frontend_message(b'S', &[]);
        let msg = decode_frontend_message(&buf).unwrap().unwrap();
        assert!(matches!(msg, FrontendMessage::Sync));
    }

    #[test]
    fn test_read_flush_message() {
        let buf = make_frontend_message(b'H', &[]);
        let msg = decode_frontend_message(&buf).unwrap().unwrap();
        assert!(matches!(msg, FrontendMessage::Flush));
    }
}
