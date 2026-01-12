use std::io;
use tokio::io::{AsyncWrite, AsyncWriteExt};

use crate::protocol::codec::write_cstring;

/// Messages sent by the backend (server) to the client.
#[derive(Debug)]
pub enum BackendMessage {
    /// 'R' - Authentication response (AuthenticationOk)
    AuthenticationOk,
    /// 'K' - Backend key data for cancel requests
    BackendKeyData { process_id: i32, secret_key: i32 },
    /// 'S' - Parameter status notification
    ParameterStatus { name: String, value: String },
    /// 'Z' - Ready for query
    ReadyForQuery { status: TransactionStatus },
    /// 'E' - Error response
    ErrorResponse { fields: Vec<ErrorField> },
}

impl BackendMessage {
    /// Write this message to the stream.
    pub async fn write<W: AsyncWrite + Unpin>(&self, w: &mut W) -> io::Result<()> {
        match self {
            BackendMessage::AuthenticationOk => {
                w.write_u8(b'R').await?;
                w.write_i32(8).await?; // length
                w.write_i32(0).await?; // auth type 0 = Ok
            }
            BackendMessage::BackendKeyData {
                process_id,
                secret_key,
            } => {
                w.write_u8(b'K').await?;
                w.write_i32(12).await?; // length
                w.write_i32(*process_id).await?;
                w.write_i32(*secret_key).await?;
            }
            BackendMessage::ParameterStatus { name, value } => {
                w.write_u8(b'S').await?;
                let len = 4 + name.len() + 1 + value.len() + 1;
                w.write_i32(len as i32).await?;
                write_cstring(w, name).await?;
                write_cstring(w, value).await?;
            }
            BackendMessage::ReadyForQuery { status } => {
                w.write_u8(b'Z').await?;
                w.write_i32(5).await?; // length
                w.write_u8(status.as_byte()).await?;
            }
            BackendMessage::ErrorResponse { fields } => {
                w.write_u8(b'E').await?;
                // Calculate body length
                let body_len: usize = fields.iter().map(|f| 1 + f.value.len() + 1).sum::<usize>() + 1;
                w.write_i32((4 + body_len) as i32).await?;
                for field in fields {
                    w.write_u8(field.code).await?;
                    write_cstring(w, &field.value).await?;
                }
                w.write_u8(0).await?; // terminator
            }
        }
        Ok(())
    }
}

/// Transaction status indicator for ReadyForQuery message.
#[derive(Debug, Clone, Copy)]
pub enum TransactionStatus {
    /// 'I' - Idle (not in a transaction block)
    Idle,
    /// 'T' - In a transaction block
    InTransaction,
    /// 'E' - In a failed transaction block
    Failed,
}

impl TransactionStatus {
    fn as_byte(self) -> u8 {
        match self {
            TransactionStatus::Idle => b'I',
            TransactionStatus::InTransaction => b'T',
            TransactionStatus::Failed => b'E',
        }
    }
}

/// Error/Notice field codes.
#[derive(Debug)]
pub struct ErrorField {
    pub code: u8,
    pub value: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_write_authentication_ok() {
        let msg = BackendMessage::AuthenticationOk;
        let mut buf = Vec::new();
        msg.write(&mut buf).await.unwrap();
        assert_eq!(buf, vec![b'R', 0, 0, 0, 8, 0, 0, 0, 0]);
    }

    #[tokio::test]
    async fn test_write_ready_for_query() {
        let msg = BackendMessage::ReadyForQuery {
            status: TransactionStatus::Idle,
        };
        let mut buf = Vec::new();
        msg.write(&mut buf).await.unwrap();
        assert_eq!(buf, vec![b'Z', 0, 0, 0, 5, b'I']);
    }

    #[tokio::test]
    async fn test_write_parameter_status() {
        let msg = BackendMessage::ParameterStatus {
            name: "server_version".to_string(),
            value: "16.0".to_string(),
        };
        let mut buf = Vec::new();
        msg.write(&mut buf).await.unwrap();
        // 'S' + length(4) + "server_version\0" + "16.0\0"
        // length = 4 + 15 ("server_version\0") + 5 ("16.0\0") = 24
        assert_eq!(buf[0], b'S');
        assert_eq!(&buf[1..5], &[0, 0, 0, 24]); // length field
        assert_eq!(
            &buf[5..],
            b"server_version\0\x31\x36\x2e\x30\0" // "server_version\016.0\0"
        );
    }
}
