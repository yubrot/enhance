use std::io::{self, Read};

/// Extension trait for reading PostgreSQL protocol values (big-endian).
pub trait ReadPgExt: Read {
    /// Read a big-endian i32 from the reader.
    fn read_i32(&mut self) -> io::Result<i32> {
        let mut buf = [0u8; 4];
        self.read_exact(&mut buf)?;
        Ok(i32::from_be_bytes(buf))
    }

    /// Read a null-terminated string from a reader.
    /// Returns the string (without the null terminator).
    fn read_cstring(&mut self) -> io::Result<String> {
        let mut bytes = Vec::new();
        loop {
            let mut byte = [0u8; 1];
            self.read_exact(&mut byte)?;
            if byte[0] == 0 {
                break;
            }
            bytes.push(byte[0]);
        }
        // We only support UTF-8
        String::from_utf8(bytes)
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "invalid UTF-8"))
    }
}

impl<R: Read> ReadPgExt for R {}

/// Extension trait for writing PostgreSQL protocol values (big-endian).
pub trait WritePgExt {
    /// Write a big-endian i32 to the buffer.
    fn write_i32(&mut self, val: i32);

    /// Write a null-terminated string to the buffer.
    fn write_cstring(&mut self, s: &str);
}

impl WritePgExt for Vec<u8> {
    fn write_i32(&mut self, val: i32) {
        self.extend_from_slice(&val.to_be_bytes());
    }

    fn write_cstring(&mut self, s: &str) {
        self.extend_from_slice(s.as_bytes());
        self.push(0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read_i32() {
        let buf = [0x00, 0x00, 0x00, 0x08];
        let mut cursor = &buf[..];
        assert_eq!(cursor.read_i32().unwrap(), 8);
    }

    #[test]
    fn test_read_cstring() {
        let buf = b"hello\0world";
        let mut cursor = &buf[..];
        assert_eq!(cursor.read_cstring().unwrap(), "hello");
    }

    #[test]
    fn test_write_i32() {
        let mut buf = Vec::new();
        buf.write_i32(8);
        assert_eq!(buf, vec![0x00, 0x00, 0x00, 0x08]);
    }

    #[test]
    fn test_write_cstring() {
        let mut buf = Vec::new();
        buf.write_cstring("test");
        assert_eq!(buf, b"test\0");
    }
}
