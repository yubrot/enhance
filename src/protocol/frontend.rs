use std::collections::HashMap;
use std::io::Read;

use crate::protocol::ProtocolError;
use crate::protocol::codec::ReadPgExt;

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
    /// Parse a startup-phase message from raw bytes.
    /// The `buf` should contain the complete startup message body (after the length field).
    pub fn parse(mut buf: &[u8]) -> Result<Self, ProtocolError> {
        let code = buf.read_i32()?;

        match code {
            SSL_REQUEST_CODE if buf.is_empty() => Ok(StartupMessage::SslRequest),
            GSSENC_REQUEST_CODE if buf.is_empty() => Ok(StartupMessage::GssEncRequest),
            CANCEL_REQUEST_CODE if buf.len() == 8 => {
                let process_id = buf.read_i32()?;
                let secret_key = buf.read_i32()?;
                Ok(StartupMessage::CancelRequest {
                    process_id,
                    secret_key,
                })
            }
            SSL_REQUEST_CODE | GSSENC_REQUEST_CODE | CANCEL_REQUEST_CODE => {
                Err(ProtocolError::InvalidMessage)
            }
            version if (version >> 16) == 3 => Ok(StartupMessage::Startup {
                protocol_version: version,
                parameters: Self::parse_startup_parameters(&mut buf)?,
            }),
            _ => Err(ProtocolError::UnsupportedProtocolVersion(code)),
        }
    }

    fn parse_startup_parameters<R: Read>(buf: &mut R) -> Result<StartupParameters, ProtocolError> {
        let mut params = StartupParameters::default();

        loop {
            let name = match buf.read_cstring() {
                Ok(s) if s.is_empty() => break,
                Ok(s) => s,
                Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => break,
                Err(_) => return Err(ProtocolError::InvalidUtf8),
            };

            let value = buf.read_cstring().map_err(|_| ProtocolError::InvalidUtf8)?;

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
    use crate::protocol::codec::WritePgExt;

    use super::*;

    #[test]
    fn test_parse_ssl_request() {
        // SSL_REQUEST_CODE = 80877103 = 0x04D2162F
        let buf = [0x04, 0xD2, 0x16, 0x2F];
        let msg = StartupMessage::parse(&buf).unwrap();
        assert!(matches!(msg, StartupMessage::SslRequest));
    }

    #[test]
    fn test_parse_startup_message() {
        // Protocol version 3.0 + parameters
        let mut buf = Vec::new();
        buf.write_i32(3 << 16);
        buf.extend_from_slice(b"user\0postgres\0");
        buf.extend_from_slice(b"database\0testdb\0");
        buf.push(0); // terminator

        let msg = StartupMessage::parse(&buf).unwrap();

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
