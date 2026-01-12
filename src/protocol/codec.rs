use std::io;
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};

/// Read a null-terminated string from an async reader.
/// Returns the string (without the null terminator).
///
/// NOTE: Production improvements needed:
/// - Add maximum length parameter to prevent unbounded memory allocation
/// - A malicious client could send data without null terminator, causing OOM
/// - Consider using a bounded buffer with explicit size limit (e.g., 64KB)
pub async fn read_cstring<R: AsyncRead + Unpin>(r: &mut R) -> io::Result<String> {
    let mut bytes = Vec::new();
    loop {
        let byte = r.read_u8().await?;
        if byte == 0 {
            break;
        }
        bytes.push(byte);
    }
    String::from_utf8(bytes)
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "invalid UTF-8"))
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
    async fn test_write_cstring() {
        let mut buf = Vec::new();
        write_cstring(&mut buf, "test").await.unwrap();
        assert_eq!(buf, b"test\0");
    }
}
