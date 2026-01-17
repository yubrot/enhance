use bytes::{Buf, BufMut, BytesMut};

use crate::protocol::ProtocolError;

/// Maximum message size in bytes (16 MB).
/// PostgreSQL uses up to 1 GB, but 16 MB is a reasonable default for most use cases.
pub const DEFAULT_MAX_MESSAGE_SIZE: usize = 16 * 1024 * 1024;

/// Read a null-terminated string from a BytesMut buffer.
/// Returns an error if there's not enough data (no null terminator found).
/// Returns the string (without the null terminator) if successful.
///
/// This function will search for a null byte within the buffer up to a maximum
/// length to prevent unbounded memory consumption from malicious input.
pub fn get_cstring(src: &mut BytesMut) -> Result<String, ProtocolError> {
    const MAX_CSTRING_LENGTH: usize = 64 * 1024; // 64KB limit

    // Find the null terminator position
    let Some(null_pos) = src.iter().take(MAX_CSTRING_LENGTH).position(|&b| b == 0) else {
        return Err(ProtocolError::InvalidMessage);
    };

    let bytes = src.split_to(null_pos);
    src.advance(1);
    String::from_utf8(bytes.to_vec()).map_err(ProtocolError::InvalidUtf8)
}

/// Write a null-terminated string to a BytesMut buffer.
pub fn put_cstring(dst: &mut BytesMut, s: &str) {
    dst.put_slice(s.as_bytes());
    dst.put_u8(0);
}

/// Codec for the query phase of the PostgreSQL protocol.
/// Encodes BackendMessage (in backend.rs) and decodes FrontendMessage (in frontend.rs).
pub struct PostgresCodec {
    pub(crate) max_message_size: usize,
}

impl PostgresCodec {
    /// Creates a new PostgresCodec with the default maximum message size.
    pub fn new() -> Self {
        Self {
            max_message_size: DEFAULT_MAX_MESSAGE_SIZE,
        }
    }
}

impl Default for PostgresCodec {
    fn default() -> Self {
        Self::new()
    }
}

/// Codec for the startup phase of the PostgreSQL protocol.
/// Decodes StartupMessage only (server doesn't receive backend messages during startup).
pub struct StartupCodec {
    pub(crate) max_message_size: usize,
}

impl StartupCodec {
    /// Creates a new StartupCodec with the default maximum message size.
    pub fn new() -> Self {
        Self {
            max_message_size: DEFAULT_MAX_MESSAGE_SIZE,
        }
    }

    /// Transitions to query phase codec after successful startup.
    pub fn ready(self) -> PostgresCodec {
        PostgresCodec {
            max_message_size: self.max_message_size,
        }
    }
}

impl Default for StartupCodec {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_cstring() {
        let mut buf = BytesMut::from(&b"hello\0world"[..]);
        assert_eq!(get_cstring(&mut buf).unwrap(), "hello".to_string());
        assert_eq!(buf, b"world"[..]);
    }

    #[test]
    fn test_get_cstring_incomplete() {
        let mut buf = BytesMut::from(&b"hello"[..]);
        assert!(get_cstring(&mut buf).is_err());
    }

    #[test]
    fn test_put_cstring() {
        let mut buf = BytesMut::new();
        put_cstring(&mut buf, "test");
        assert_eq!(buf, b"test\0"[..]);
    }
}
