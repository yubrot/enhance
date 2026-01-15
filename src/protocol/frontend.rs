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

            let name = read_cstring(r).await.map_err(|e| {
                if e.kind() == std::io::ErrorKind::UnexpectedEof {
                    ProtocolError::InsufficientData
                } else {
                    ProtocolError::InvalidUtf8
                }
            })?;

            // Account for name + null terminator
            remaining = remaining.saturating_sub(name.len() + 1);

            // Empty name signals end of parameters
            if name.is_empty() {
                break;
            }

            let value = read_cstring(r)
                .await
                .map_err(|_| ProtocolError::InvalidUtf8)?;

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

/// Describe message target type
#[derive(Debug, Clone, Copy)]
pub enum DescribeTarget {
    /// 'S' - Describe a prepared statement
    Statement,
    /// 'P' - Describe a portal
    Portal,
}

/// Describe message - request metadata about statement or portal
#[derive(Debug, Clone)]
pub struct DescribeMessage {
    /// Target type: Statement or Portal
    pub target_type: DescribeTarget,
    /// Name of the statement or portal
    pub name: String,
}

/// Execute message - execute a portal
#[derive(Debug, Clone)]
pub struct ExecuteMessage {
    /// Portal name (empty = unnamed)
    pub portal_name: String,
    /// Maximum rows to return (0 = unlimited)
    pub max_rows: i32,
}

/// Close message target type
#[derive(Debug, Clone, Copy)]
pub enum CloseTarget {
    /// 'S' - Close a prepared statement
    Statement,
    /// 'P' - Close a portal
    Portal,
}

/// Close message - close a statement or portal
#[derive(Debug, Clone)]
pub struct CloseMessage {
    /// Target type: Statement or Portal
    pub target_type: CloseTarget,
    /// Name of the statement or portal
    pub name: String,
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
                let query = read_cstring(r)
                    .await
                    .map_err(|_| ProtocolError::InvalidUtf8)?;
                Ok(Some(FrontendMessage::Query(query)))
            }
            b'X' => {
                // Terminate: no body (just length=4)
                Ok(Some(FrontendMessage::Terminate))
            }
            b'P' => {
                // Parse: statement_name, query, param_count, param_types[]
                let statement_name = read_cstring(r)
                    .await
                    .map_err(|_| ProtocolError::InvalidUtf8)?;
                let query = read_cstring(r)
                    .await
                    .map_err(|_| ProtocolError::InvalidUtf8)?;
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
                let portal_name = read_cstring(r)
                    .await
                    .map_err(|_| ProtocolError::InvalidUtf8)?;
                let statement_name = read_cstring(r)
                    .await
                    .map_err(|_| ProtocolError::InvalidUtf8)?;

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
                let name = read_cstring(r)
                    .await
                    .map_err(|_| ProtocolError::InvalidUtf8)?;
                Ok(Some(FrontendMessage::Describe(DescribeMessage {
                    target_type,
                    name,
                })))
            }
            b'E' => {
                // Execute: portal_name, max_rows
                let portal_name = read_cstring(r)
                    .await
                    .map_err(|_| ProtocolError::InvalidUtf8)?;
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
                let name = read_cstring(r)
                    .await
                    .map_err(|_| ProtocolError::InvalidUtf8)?;
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
    use std::io::Cursor;
    use tokio::io::AsyncWriteExt;

    async fn make_startup_message(code: i32, body: &[u8]) -> Vec<u8> {
        let mut buf = Vec::new();
        let len = 4 + 4 + body.len(); // length + code + body
        buf.write_i32(len as i32).await.unwrap();
        buf.write_i32(code).await.unwrap();
        buf.extend_from_slice(body);
        buf
    }

    #[tokio::test]
    async fn test_read_ssl_request() {
        let buf = make_startup_message(SSL_REQUEST_CODE, &[]).await;
        let mut cursor = Cursor::new(buf);
        let msg = StartupMessage::read(&mut cursor).await.unwrap();
        assert!(matches!(msg, StartupMessage::SslRequest));
    }

    #[tokio::test]
    async fn test_read_startup_message() {
        let mut body = Vec::new();
        body.extend_from_slice(b"user\0postgres\0");
        body.extend_from_slice(b"database\0testdb\0");
        body.push(0); // terminator

        let buf = make_startup_message(3 << 16, &body).await;
        let mut cursor = Cursor::new(buf);
        let msg = StartupMessage::read(&mut cursor).await.unwrap();

        match msg {
            StartupMessage::Startup {
                protocol_version,
                parameters,
            } => {
                assert_eq!(protocol_version, 3 << 16);
                assert_eq!(parameters.user, "postgres");
                assert_eq!(parameters.database, Some("testdb".to_string()));
            }
            _ => panic!("expected Startup message"),
        }
    }

    #[tokio::test]
    async fn test_read_query_message() {
        let mut buf = Vec::new();
        buf.push(b'Q');
        buf.write_i32(13).await.unwrap(); // length = 4 + 9 ("SELECT 1\0")
        buf.extend_from_slice(b"SELECT 1\0");

        let mut cursor = Cursor::new(buf);
        let msg = FrontendMessage::read(&mut cursor).await.unwrap().unwrap();

        match msg {
            FrontendMessage::Query(q) => assert_eq!(q, "SELECT 1"),
            _ => panic!("expected Query message"),
        }
    }

    #[tokio::test]
    async fn test_read_terminate_message() {
        let mut buf = Vec::new();
        buf.push(b'X');
        buf.write_i32(4).await.unwrap(); // length (no body)

        let mut cursor = Cursor::new(buf);
        let msg = FrontendMessage::read(&mut cursor).await.unwrap().unwrap();

        assert!(matches!(msg, FrontendMessage::Terminate));
    }

    #[tokio::test]
    async fn test_read_eof() {
        let buf = Vec::new();
        let mut cursor = Cursor::new(buf);
        let msg = FrontendMessage::read(&mut cursor).await.unwrap();

        assert!(msg.is_none());
    }

    #[tokio::test]
    async fn test_read_unknown_message_type() {
        let mut buf = Vec::new();
        buf.push(b'Z'); // Unknown type
        buf.write_i32(4).await.unwrap();

        let mut cursor = Cursor::new(buf);
        let result = FrontendMessage::read(&mut cursor).await;

        assert!(matches!(
            result,
            Err(ProtocolError::UnknownMessageType(b'Z'))
        ));
    }
}
