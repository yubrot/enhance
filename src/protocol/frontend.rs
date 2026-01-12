use std::collections::HashMap;
use tokio::io::{AsyncRead, AsyncReadExt};

use crate::protocol::ProtocolError;
use crate::protocol::codec::read_cstring;

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
}
