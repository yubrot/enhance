use bytes::{Buf, BytesMut};
use std::collections::HashMap;
use tokio_util::codec::Decoder;

use crate::protocol::codec::{PostgresCodec, StartupCodec, get_cstring};
use crate::protocol::error::ProtocolError;

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
            _ => Err(ProtocolError::UnknownMessageType(msg_type)),
        }
    }
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
}
