use std::io;
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};

use crate::protocol::ProtocolError;

/// Read a null-terminated string from an async reader.
/// Returns the string (without the null terminator).
///
/// NOTE: Production improvements needed:
/// - Add maximum length parameter to prevent unbounded memory allocation
/// - A malicious client could send data without null terminator, causing OOM
/// - Consider using a bounded buffer with explicit size limit (e.g., 64KB)
pub async fn read_cstring<R: AsyncRead + Unpin>(r: &mut R) -> Result<String, ProtocolError> {
    let mut bytes = Vec::new();
    loop {
        let byte = r.read_u8().await?;
        if byte == 0 {
            break;
        }
        bytes.push(byte);
    }
    String::from_utf8(bytes).map_err(ProtocolError::InvalidUtf8)
}

/// Read a nullable byte array from an async reader.
/// Returns None if the length is -1 (SQL NULL), otherwise reads the specified number of bytes.
///
/// Wire format: Int32 length (-1 for NULL, >= 0 for data), followed by data bytes if length >= 0
pub async fn read_nullable_bytes<R: AsyncRead + Unpin>(
    r: &mut R,
) -> Result<Option<Vec<u8>>, ProtocolError> {
    let len = r.read_i32().await?;
    if len < 0 {
        Ok(None)
    } else {
        let mut buf = vec![0u8; len as usize];
        r.read_exact(&mut buf).await?;
        Ok(Some(buf))
    }
}

/// Write a null-terminated string to an async writer.
pub async fn write_cstring<W: AsyncWrite + Unpin>(w: &mut W, s: &str) -> io::Result<()> {
    w.write_all(s.as_bytes()).await?;
    w.write_u8(0).await?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[tokio::test]
    async fn test_read_cstring() {
        let mut cursor = Cursor::new(b"hello\0world");
        assert_eq!(read_cstring(&mut cursor).await.unwrap(), "hello");
    }

    #[tokio::test]
    async fn test_read_nullable_bytes_null() {
        let mut cursor = Cursor::new(vec![0xFF, 0xFF, 0xFF, 0xFF]); // -1 in big-endian
        assert_eq!(read_nullable_bytes(&mut cursor).await.unwrap(), None);
    }

    #[tokio::test]
    async fn test_read_nullable_bytes_data() {
        let mut cursor = Cursor::new(vec![0, 0, 0, 5, b'h', b'e', b'l', b'l', b'o']); // length 5 + data
        assert_eq!(
            read_nullable_bytes(&mut cursor).await.unwrap(),
            Some(b"hello".to_vec())
        );
    }

    #[tokio::test]
    async fn test_read_nullable_bytes_empty() {
        let mut cursor = Cursor::new(vec![0, 0, 0, 0]); // length 0
        assert_eq!(
            read_nullable_bytes(&mut cursor).await.unwrap(),
            Some(vec![])
        );
    }

    #[tokio::test]
    async fn test_write_cstring() {
        let mut buf = Vec::new();
        write_cstring(&mut buf, "test").await.unwrap();
        assert_eq!(buf, b"test\0");
    }
}
