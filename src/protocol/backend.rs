use crate::protocol::codec::WritePgExt;

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
    /// Encode the message to bytes.
    pub fn encode(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.encode_into(&mut buf);
        buf
    }

    /// Encode the message into an existing buffer.
    pub fn encode_into(&self, buf: &mut Vec<u8>) {
        match self {
            BackendMessage::AuthenticationOk => {
                buf.push(b'R');
                buf.write_i32(8); // length
                buf.write_i32(0); // auth type 0 = Ok
            }
            BackendMessage::BackendKeyData {
                process_id,
                secret_key,
            } => {
                buf.push(b'K');
                buf.write_i32(12); // length
                buf.write_i32(*process_id);
                buf.write_i32(*secret_key);
            }
            BackendMessage::ParameterStatus { name, value } => {
                buf.push(b'S');
                let len = 4 + name.len() + 1 + value.len() + 1;
                buf.write_i32(len as i32);
                buf.write_cstring(name);
                buf.write_cstring(value);
            }
            BackendMessage::ReadyForQuery { status } => {
                buf.push(b'Z');
                buf.write_i32(5); // length
                buf.push(status.as_byte());
            }
            BackendMessage::ErrorResponse { fields } => {
                buf.push(b'E');
                let mut body = Vec::new();
                for field in fields {
                    body.push(field.code);
                    body.write_cstring(&field.value);
                }
                body.push(0); // terminator
                buf.write_i32((4 + body.len()) as i32);
                buf.extend(body);
            }
        }
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

    #[test]
    fn test_encode_authentication_ok() {
        let msg = BackendMessage::AuthenticationOk;
        let bytes = msg.encode();
        assert_eq!(bytes, vec![b'R', 0, 0, 0, 8, 0, 0, 0, 0]);
    }

    #[test]
    fn test_encode_ready_for_query() {
        let msg = BackendMessage::ReadyForQuery {
            status: TransactionStatus::Idle,
        };
        let bytes = msg.encode();
        assert_eq!(bytes, vec![b'Z', 0, 0, 0, 5, b'I']);
    }

    #[test]
    fn test_encode_parameter_status() {
        let msg = BackendMessage::ParameterStatus {
            name: "server_version".to_string(),
            value: "16.0".to_string(),
        };
        let bytes = msg.encode();
        // 'S' + length(4) + "server_version\0" + "16.0\0"
        // length = 4 + 15 ("server_version\0") + 5 ("16.0\0") = 24
        assert_eq!(bytes[0], b'S');
        assert_eq!(&bytes[1..5], &[0, 0, 0, 24]); // length field
        assert_eq!(
            &bytes[5..],
            b"server_version\0\x31\x36\x2e\x30\0" // "server_version\016.0\0"
        );
    }
}
