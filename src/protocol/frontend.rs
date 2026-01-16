use std::collections::HashMap;
use tokio::io::{AsyncRead, AsyncReadExt};

use crate::protocol::ProtocolError;
use crate::protocol::codec::{read_cstring, read_nullable_bytes};

/// SSLRequest magic number
pub const SSL_REQUEST_CODE: i32 = (1234 << 16) | 5679; // 80877103

/// GSSENCRequest magic number
pub const GSSENC_REQUEST_CODE: i32 = (1234 << 16) | 5680; // 80877104

/// CancelRequest magic number
pub const CANCEL_REQUEST_CODE: i32 = (1234 << 16) | 5678; // 80877102

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

/// Startup parameters from the client
#[derive(Debug, Clone, Default)]
pub struct StartupParameters {
    pub user: String,
    pub database: Option<String>,
    pub application_name: Option<String>,
    pub client_encoding: Option<String>,
    pub other: HashMap<String, String>,
}

impl StartupMessage {
    /// Parse a startup message from a byte buffer.
    pub async fn from_bytes(buf: &[u8]) -> Result<Self, ProtocolError> {
        use std::io::Cursor;
        let mut cursor = Cursor::new(buf);
        Self::read(&mut cursor).await
    }

    /// Read a startup-phase message from the stream (including length prefix).
    ///
    /// NOTE: Production improvements needed:
    /// - Add maximum message size limit (PostgreSQL uses 1GB max)
    /// - Implement read timeout to prevent slow-loris attacks
    /// - Consider using a pre-allocated buffer pool for parsing
    pub async fn read<R: AsyncRead + Unpin>(r: &mut R) -> Result<Self, ProtocolError> {
        let len = r.read_i32().await?;

        // Minimum length is 8 (length + code)
        // NOTE: Production should also enforce maximum length (e.g., 10KB for startup)
        if len < 8 {
            return Err(ProtocolError::InvalidMessage);
        }

        let code = r.read_i32().await?;

        // Remaining bytes after length and code
        let remaining = (len - 8) as usize;

        match code {
            SSL_REQUEST_CODE if remaining == 0 => Ok(StartupMessage::SslRequest),
            GSSENC_REQUEST_CODE if remaining == 0 => Ok(StartupMessage::GssEncRequest),
            CANCEL_REQUEST_CODE if remaining == 8 => {
                let process_id = r.read_i32().await?;
                let secret_key = r.read_i32().await?;
                Ok(StartupMessage::CancelRequest {
                    process_id,
                    secret_key,
                })
            }
            SSL_REQUEST_CODE | GSSENC_REQUEST_CODE | CANCEL_REQUEST_CODE => {
                Err(ProtocolError::InvalidMessage)
            }
            version if (version >> 16) == 3 => {
                let parameters = Self::read_startup_parameters(r, remaining).await?;
                Ok(StartupMessage::Startup {
                    protocol_version: version,
                    parameters,
                })
            }
            _ => Err(ProtocolError::UnsupportedProtocolVersion(code)),
        }
    }

    /// NOTE: Production improvements needed:
    /// - Limit maximum parameter name/value lengths
    /// - Limit total number of parameters (prevent DoS via memory exhaustion)
    /// - Sanitize/validate parameter values (e.g., encoding names)
    async fn read_startup_parameters<R: AsyncRead + Unpin>(
        r: &mut R,
        mut remaining: usize,
    ) -> Result<StartupParameters, ProtocolError> {
        let mut params = StartupParameters::default();

        loop {
            if remaining == 0 {
                break;
            }

            let name = read_cstring(r).await?;

            // Account for name + null terminator
            remaining = remaining.saturating_sub(name.len() + 1);

            // Empty name signals end of parameters
            if name.is_empty() {
                break;
            }

            let value = read_cstring(r).await?;

            // Account for value + null terminator
            remaining = remaining.saturating_sub(value.len() + 1);

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

/// Bind message - binds parameters to create a portal
#[derive(Debug, Clone)]
pub struct BindMessage {
    /// Destination portal name (empty = unnamed)
    pub portal_name: String,
    /// Source prepared statement name
    pub statement_name: String,
    /// Parameter format codes (0=text, 1=binary)
    pub param_format_codes: Vec<i16>,
    /// Parameter values (None = NULL)
    pub param_values: Vec<Option<Vec<u8>>>,
    /// Result column format codes
    pub result_format_codes: Vec<i16>,
}

/// Describe message - request metadata about statement or portal
#[derive(Debug, Clone)]
pub struct DescribeMessage {
    /// Target type: Statement or Portal
    pub target_type: DescribeTarget,
    /// Name of the statement or portal
    pub name: String,
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

/// Close message - close a statement or portal
#[derive(Debug, Clone)]
pub struct CloseMessage {
    /// Target type: Statement or Portal
    pub target_type: CloseTarget,
    /// Name of the statement or portal
    pub name: String,
}

/// Close message target type
#[derive(Debug, Clone, Copy)]
pub enum CloseTarget {
    /// 'S' - Close a prepared statement
    Statement,
    /// 'P' - Close a portal
    Portal,
}

impl FrontendMessage {
    /// Parse a frontend message from a byte buffer.
    pub async fn from_bytes(buf: &[u8]) -> Result<Option<Self>, ProtocolError> {
        use std::io::Cursor;
        let mut cursor = Cursor::new(buf);
        Self::read(&mut cursor).await
    }

    /// Read a query-phase message from the stream.
    /// Returns None on EOF (clean disconnect).
    ///
    /// NOTE: Production improvements needed:
    /// - Add timeout to prevent slow-loris attacks
    /// - Limit query size (PostgreSQL: 1GB max)
    pub async fn read<R: AsyncRead + Unpin>(r: &mut R) -> Result<Option<Self>, ProtocolError> {
        // Read message type byte
        let msg_type = match r.read_u8().await {
            Ok(t) => t,
            Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => return Ok(None),
            Err(e) => return Err(e.into()),
        };

        // Read length (includes self but not type byte)
        // TODO: this should be passed to read_cstring or else
        let length = r.read_i32().await?;
        if length < 4 {
            return Err(ProtocolError::InvalidMessage);
        }

        match msg_type {
            b'Q' => {
                // Query: read null-terminated string
                let query = read_cstring(r).await?;
                Ok(Some(FrontendMessage::Query(query)))
            }
            b'X' => {
                // Terminate: no body (just length=4)
                Ok(Some(FrontendMessage::Terminate))
            }
            b'P' => {
                // Parse: statement_name, query, param_count, param_types[]
                let statement_name = read_cstring(r).await?;
                let query = read_cstring(r).await?;
                let param_count = r.read_i16().await? as usize;
                let mut param_types = Vec::with_capacity(param_count);
                for _ in 0..param_count {
                    param_types.push(r.read_i32().await?);
                }
                Ok(Some(FrontendMessage::Parse(ParseMessage {
                    statement_name,
                    query,
                    param_types,
                })))
            }
            b'B' => {
                // Bind: portal_name, statement_name, format_codes, params, result_formats
                let portal_name = read_cstring(r).await?;
                let statement_name = read_cstring(r).await?;

                // Parameter format codes
                let format_count = r.read_i16().await? as usize;
                let mut param_format_codes = Vec::with_capacity(format_count);
                for _ in 0..format_count {
                    param_format_codes.push(r.read_i16().await?);
                }

                // Parameter values
                let param_count = r.read_i16().await? as usize;
                let mut param_values = Vec::with_capacity(param_count);
                for _ in 0..param_count {
                    param_values.push(read_nullable_bytes(r).await?);
                }

                // Result format codes
                let result_format_count = r.read_i16().await? as usize;
                let mut result_format_codes = Vec::with_capacity(result_format_count);
                for _ in 0..result_format_count {
                    result_format_codes.push(r.read_i16().await?);
                }

                Ok(Some(FrontendMessage::Bind(BindMessage {
                    portal_name,
                    statement_name,
                    param_format_codes,
                    param_values,
                    result_format_codes,
                })))
            }
            b'D' => {
                // Describe: type ('S' or 'P'), name
                let target_byte = r.read_u8().await?;
                let target_type = match target_byte {
                    b'S' => DescribeTarget::Statement,
                    b'P' => DescribeTarget::Portal,
                    _ => return Err(ProtocolError::InvalidMessage),
                };
                let name = read_cstring(r).await?;
                Ok(Some(FrontendMessage::Describe(DescribeMessage {
                    target_type,
                    name,
                })))
            }
            b'E' => {
                // Execute: portal_name, max_rows
                let portal_name = read_cstring(r).await?;
                let max_rows = r.read_i32().await?;
                Ok(Some(FrontendMessage::Execute(ExecuteMessage {
                    portal_name,
                    max_rows,
                })))
            }
            b'C' => {
                // Close: type ('S' or 'P'), name
                let target_byte = r.read_u8().await?;
                let target_type = match target_byte {
                    b'S' => CloseTarget::Statement,
                    b'P' => CloseTarget::Portal,
                    _ => return Err(ProtocolError::InvalidMessage),
                };
                let name = read_cstring(r).await?;
                Ok(Some(FrontendMessage::Close(CloseMessage {
                    target_type,
                    name,
                })))
            }
            b'S' => {
                // Sync: no body (just length=4)
                Ok(Some(FrontendMessage::Sync))
            }
            b'H' => {
                // Flush: no body (just length=4)
                Ok(Some(FrontendMessage::Flush))
            }
            _ => Err(ProtocolError::UnknownMessageType(msg_type)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::io::AsyncWriteExt;

    /// Helper to create a startup message with given code and body
    async fn make_startup_message(code: i32, body: &[u8]) -> Vec<u8> {
        let mut buf = Vec::new();
        let len = 4 + 4 + body.len(); // length + code + body
        buf.write_i32(len as i32).await.unwrap();
        buf.write_i32(code).await.unwrap();
        buf.extend_from_slice(body);
        buf
    }

    /// Helper to create a frontend message with given type and body
    async fn make_frontend_message(msg_type: u8, body: &[u8]) -> Vec<u8> {
        let mut buf = Vec::new();
        buf.push(msg_type);
        let len = 4 + body.len(); // length includes self (4 bytes) + body
        buf.write_i32(len as i32).await.unwrap();
        buf.extend_from_slice(body);
        buf
    }

    #[tokio::test]
    async fn test_read_ssl_request() {
        let buf = make_startup_message(SSL_REQUEST_CODE, &[]).await;
        let msg = StartupMessage::from_bytes(&buf).await.unwrap();
        assert!(matches!(msg, StartupMessage::SslRequest));
    }

    #[tokio::test]
    async fn test_read_startup_message() {
        let mut body = Vec::new();
        body.extend_from_slice(b"user\0postgres\0");
        body.extend_from_slice(b"database\0testdb\0");
        body.push(0); // terminator

        let buf = make_startup_message(3 << 16, &body).await;
        let msg = StartupMessage::from_bytes(&buf).await.unwrap();

        let StartupMessage::Startup {
            protocol_version,
            parameters,
        } = msg
        else {
            panic!("expected Startup message, got {msg:?}")
        };

        assert_eq!(protocol_version, 3 << 16);
        assert_eq!(parameters.user, "postgres");
        assert_eq!(parameters.database, Some("testdb".to_string()));
    }

    #[tokio::test]
    async fn test_read_startup_message_missing_user() {
        let mut body = Vec::new();
        body.extend_from_slice(b"database\0testdb\0");
        body.push(0); // terminator

        let buf = make_startup_message(3 << 16, &body).await;
        let result = StartupMessage::from_bytes(&buf).await;

        assert!(matches!(
            result,
            Err(ProtocolError::MissingParameter("user"))
        ));
    }

    #[tokio::test]
    async fn test_read_gssenc_request() {
        let buf = make_startup_message(GSSENC_REQUEST_CODE, &[]).await;
        let msg = StartupMessage::from_bytes(&buf).await.unwrap();
        assert!(matches!(msg, StartupMessage::GssEncRequest));
    }

    #[tokio::test]
    async fn test_read_cancel_request() {
        let mut body = Vec::new();
        body.write_i32(12345).await.unwrap(); // process_id
        body.write_i32(67890).await.unwrap(); // secret_key

        let buf = make_startup_message(CANCEL_REQUEST_CODE, &body).await;
        let msg = StartupMessage::from_bytes(&buf).await.unwrap();

        let StartupMessage::CancelRequest {
            process_id,
            secret_key,
        } = msg
        else {
            panic!("expected CancelRequest message, got {msg:?}")
        };

        assert_eq!(process_id, 12345);
        assert_eq!(secret_key, 67890);
    }

    #[tokio::test]
    async fn test_read_eof() {
        let buf = Vec::new();
        let msg = FrontendMessage::from_bytes(&buf).await.unwrap();
        assert!(msg.is_none());
    }

    #[tokio::test]
    async fn test_read_unknown_message_type() {
        let mut buf = Vec::new();
        buf.push(b'Z'); // Unknown type
        buf.write_i32(4).await.unwrap();

        let result = FrontendMessage::from_bytes(&buf).await;
        assert!(matches!(
            result,
            Err(ProtocolError::UnknownMessageType(b'Z'))
        ));
    }

    #[tokio::test]
    async fn test_read_query_message() {
        let buf = make_frontend_message(b'Q', b"SELECT 1\0").await;
        let msg = FrontendMessage::from_bytes(&buf).await.unwrap().unwrap();

        let FrontendMessage::Query(q) = msg else {
            panic!("expected Query message, got {msg:?}")
        };

        assert_eq!(q, "SELECT 1");
    }

    #[tokio::test]
    async fn test_read_terminate_message() {
        let buf = make_frontend_message(b'X', &[]).await;
        let msg = FrontendMessage::from_bytes(&buf).await.unwrap().unwrap();
        assert!(matches!(msg, FrontendMessage::Terminate));
    }

    #[tokio::test]
    async fn test_read_parse_message() {
        let mut body = Vec::new();
        body.push(0); // empty (unnamed) statement - commonly used in PostgreSQL
        body.extend_from_slice(b"SELECT $1, $2\0");
        body.write_i16(2).await.unwrap(); // 2 parameters
        body.write_i32(23).await.unwrap(); // INT4 OID
        body.write_i32(25).await.unwrap(); // TEXT OID

        let buf = make_frontend_message(b'P', &body).await;
        let msg = FrontendMessage::from_bytes(&buf).await.unwrap().unwrap();

        let FrontendMessage::Parse(parse) = msg else {
            panic!("expected Parse message, got {msg:?}")
        };

        assert_eq!(parse.statement_name, ""); // unnamed statement
        assert_eq!(parse.query, "SELECT $1, $2");
        assert_eq!(parse.param_types, vec![23, 25]);
    }

    #[tokio::test]
    async fn test_read_parse_message_named() {
        let mut body = Vec::new();
        body.extend_from_slice(b"portal\0");
        body.extend_from_slice(b"SELECT $1\0");
        body.write_i16(1).await.unwrap();
        body.write_i32(23).await.unwrap();

        let buf = make_frontend_message(b'P', &body).await;
        let msg = FrontendMessage::from_bytes(&buf).await.unwrap().unwrap();

        let FrontendMessage::Parse(parse) = msg else {
            panic!("expected Parse message, got {msg:?}")
        };

        assert_eq!(parse.statement_name, "portal");
        assert_eq!(parse.query, "SELECT $1");
        assert_eq!(parse.param_types, vec![23]);
    }

    #[tokio::test]
    async fn test_read_bind_message() {
        let mut body = Vec::new();
        body.extend_from_slice(b"portal\0"); // portal_name
        body.extend_from_slice(b"stmt\0"); // statement_name
        body.write_i16(1).await.unwrap(); // format_count
        body.write_i16(0).await.unwrap(); // format code (text)
        body.write_i16(3).await.unwrap(); // param_count: 3 params (non-NULL, NULL, non-NULL)
        body.write_i32(2).await.unwrap(); // first param length
        body.extend_from_slice(b"42"); // first param value
        body.write_i32(-1).await.unwrap(); // second param is NULL (-1)
        body.write_i32(5).await.unwrap(); // third param length
        body.extend_from_slice(b"hello"); // third param value
        body.write_i16(1).await.unwrap(); // result_format_count
        body.write_i16(0).await.unwrap(); // result format code

        let buf = make_frontend_message(b'B', &body).await;
        let msg = FrontendMessage::from_bytes(&buf).await.unwrap().unwrap();

        let FrontendMessage::Bind(bind) = msg else {
            panic!("expected Bind message, got {msg:?}")
        };

        assert_eq!(bind.portal_name, "portal");
        assert_eq!(bind.statement_name, "stmt");
        assert_eq!(bind.param_format_codes, vec![0]);
        assert_eq!(bind.param_values.len(), 3);
        assert_eq!(bind.param_values[0], Some(b"42".to_vec()));
        assert_eq!(bind.param_values[1], None); // NULL parameter
        assert_eq!(bind.param_values[2], Some(b"hello".to_vec()));
        assert_eq!(bind.result_format_codes, vec![0]);
    }

    #[tokio::test]
    async fn test_read_describe_statement() {
        let mut body = Vec::new();
        body.push(b'S'); // Statement
        body.push(0); // empty (unnamed) statement

        let buf = make_frontend_message(b'D', &body).await;
        let msg = FrontendMessage::from_bytes(&buf).await.unwrap().unwrap();

        let FrontendMessage::Describe(desc) = msg else {
            panic!("expected Describe message, got {msg:?}")
        };

        assert!(matches!(desc.target_type, DescribeTarget::Statement));
        assert_eq!(desc.name, ""); // unnamed statement
    }

    #[tokio::test]
    async fn test_read_describe_portal() {
        let mut body = Vec::new();
        body.push(b'P'); // Portal
        body.extend_from_slice(b"portal\0");

        let buf = make_frontend_message(b'D', &body).await;
        let msg = FrontendMessage::from_bytes(&buf).await.unwrap().unwrap();

        let FrontendMessage::Describe(desc) = msg else {
            panic!("expected Describe message, got {msg:?}")
        };

        assert!(matches!(desc.target_type, DescribeTarget::Portal));
        assert_eq!(desc.name, "portal");
    }

    #[tokio::test]
    async fn test_read_execute_message() {
        let mut body = Vec::new();
        body.push(0); // empty (unnamed) portal - commonly used in PostgreSQL
        body.write_i32(100).await.unwrap(); // max_rows

        let buf = make_frontend_message(b'E', &body).await;
        let msg = FrontendMessage::from_bytes(&buf).await.unwrap().unwrap();

        let FrontendMessage::Execute(exec) = msg else {
            panic!("expected Execute message, got {msg:?}")
        };

        assert_eq!(exec.portal_name, ""); // unnamed portal
        assert_eq!(exec.max_rows, 100);
    }

    #[tokio::test]
    async fn test_read_close_statement() {
        let mut body = Vec::new();
        body.push(b'S'); // Statement
        body.push(0); // empty (unnamed) statement

        let buf = make_frontend_message(b'C', &body).await;
        let msg = FrontendMessage::from_bytes(&buf).await.unwrap().unwrap();

        let FrontendMessage::Close(close) = msg else {
            panic!("expected Close message, got {msg:?}")
        };

        assert!(matches!(close.target_type, CloseTarget::Statement));
        assert_eq!(close.name, ""); // unnamed statement
    }

    #[tokio::test]
    async fn test_read_close_portal() {
        let mut body = Vec::new();
        body.push(b'P'); // Portal
        body.push(0); // empty (unnamed) portal

        let buf = make_frontend_message(b'C', &body).await;
        let msg = FrontendMessage::from_bytes(&buf).await.unwrap().unwrap();

        let FrontendMessage::Close(close) = msg else {
            panic!("expected Close message, got {msg:?}")
        };

        assert!(matches!(close.target_type, CloseTarget::Portal));
        assert_eq!(close.name, ""); // unnamed portal
    }

    #[tokio::test]
    async fn test_read_sync_message() {
        let buf = make_frontend_message(b'S', &[]).await;
        let msg = FrontendMessage::from_bytes(&buf).await.unwrap().unwrap();
        assert!(matches!(msg, FrontendMessage::Sync));
    }

    #[tokio::test]
    async fn test_read_flush_message() {
        let buf = make_frontend_message(b'H', &[]).await;
        let msg = FrontendMessage::from_bytes(&buf).await.unwrap().unwrap();
        assert!(matches!(msg, FrontendMessage::Flush));
    }
}
