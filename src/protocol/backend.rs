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
    /// 'T' - Row description (column metadata)
    RowDescription { fields: Vec<FieldDescription> },
    /// 'D' - Data row
    DataRow { values: Vec<DataValue> },
    /// 'C' - Command complete
    CommandComplete { tag: String },
    /// 'I' - Empty query response
    EmptyQueryResponse,
}

impl BackendMessage {
    /// Writes message header (type byte and length) to the stream.
    async fn write_head<W: AsyncWrite + Unpin>(
        w: &mut W,
        msg_type: u8,
        body_len: usize,
    ) -> io::Result<()> {
        w.write_u8(msg_type).await?;
        w.write_i32((4 + body_len) as i32).await?;
        Ok(())
    }

    /// Write this message to the stream.
    pub async fn write<W: AsyncWrite + Unpin>(&self, w: &mut W) -> io::Result<()> {
        match self {
            BackendMessage::AuthenticationOk => {
                Self::write_head(w, b'R', 4).await?;
                w.write_i32(0).await?; // auth type 0 = Ok
            }
            BackendMessage::BackendKeyData {
                process_id,
                secret_key,
            } => {
                Self::write_head(w, b'K', 8).await?;
                w.write_i32(*process_id).await?;
                w.write_i32(*secret_key).await?;
            }
            BackendMessage::ParameterStatus { name, value } => {
                Self::write_head(w, b'S', name.len() + 1 + value.len() + 1).await?;
                write_cstring(w, name).await?;
                write_cstring(w, value).await?;
            }
            BackendMessage::ReadyForQuery { status } => {
                Self::write_head(w, b'Z', 1).await?;
                w.write_u8(status.as_byte()).await?;
            }
            BackendMessage::ErrorResponse { fields } => {
                let body_len = fields.iter().map(|f| f.encoded_len()).sum::<usize>() + 1;
                Self::write_head(w, b'E', body_len).await?;
                for field in fields {
                    field.write(w).await?;
                }
                w.write_u8(0).await?; // terminator
            }
            BackendMessage::RowDescription { fields } => {
                let body_len = 2 + fields.iter().map(|f| f.encoded_len()).sum::<usize>();
                Self::write_head(w, b'T', body_len).await?;
                w.write_i16(fields.len() as i16).await?;
                for field in fields {
                    field.write(w).await?;
                }
            }
            BackendMessage::DataRow { values } => {
                let body_len = 2 + values.iter().map(|v| v.encoded_len()).sum::<usize>();
                Self::write_head(w, b'D', body_len).await?;
                w.write_i16(values.len() as i16).await?;
                for value in values {
                    value.write(w).await?;
                }
            }
            BackendMessage::CommandComplete { tag } => {
                Self::write_head(w, b'C', tag.len() + 1).await?;
                write_cstring(w, tag).await?;
            }
            BackendMessage::EmptyQueryResponse => {
                Self::write_head(w, b'I', 0).await?;
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

impl ErrorField {
    /// Returns the encoded length of this field in bytes (code + value + null terminator).
    fn encoded_len(&self) -> usize {
        1 + self.value.len() + 1
    }

    /// Writes this field to the stream.
    async fn write<W: AsyncWrite + Unpin>(&self, w: &mut W) -> io::Result<()> {
        w.write_u8(self.code).await?;
        write_cstring(w, &self.value).await?;
        Ok(())
    }
}

/// A single column value in a data row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DataValue {
    /// SQL NULL value (encoded as length -1)
    Null,
    /// Binary data (encoded as length + data bytes)
    Binary(Vec<u8>),
}

impl DataValue {
    /// Returns the encoded length of this value in bytes (length field + data).
    fn encoded_len(&self) -> usize {
        match self {
            DataValue::Null => 4,                        // length field only
            DataValue::Binary(bytes) => 4 + bytes.len(), // length + data
        }
    }

    /// Writes this value to the stream.
    async fn write<W: AsyncWrite + Unpin>(&self, w: &mut W) -> io::Result<()> {
        match self {
            DataValue::Null => {
                w.write_i32(-1).await?;
            }
            DataValue::Binary(bytes) => {
                w.write_i32(bytes.len() as i32).await?;
                w.write_all(bytes).await?;
            }
        }
        Ok(())
    }
}

/// Field description for RowDescription message.
#[derive(Debug, Clone)]
pub struct FieldDescription {
    /// Column name
    pub name: String,
    /// Table OID (0 if not from a table)
    pub table_oid: i32,
    /// Column attribute number (0 if not from a table)
    pub column_id: i16,
    /// Data type OID
    pub type_oid: i32,
    /// Data type size (-1 for variable length)
    pub type_size: i16,
    /// Type modifier (-1 if not applicable)
    pub type_modifier: i32,
    /// Format code (0 = text, 1 = binary)
    pub format_code: i16,
}

impl FieldDescription {
    /// Returns the encoded length of this field in bytes.
    fn encoded_len(&self) -> usize {
        self.name.len() + 1 + 4 + 2 + 4 + 2 + 4 + 2
    }

    /// Writes this field to the stream.
    async fn write<W: AsyncWrite + Unpin>(&self, w: &mut W) -> io::Result<()> {
        write_cstring(w, &self.name).await?;
        w.write_i32(self.table_oid).await?;
        w.write_i16(self.column_id).await?;
        w.write_i32(self.type_oid).await?;
        w.write_i16(self.type_size).await?;
        w.write_i32(self.type_modifier).await?;
        w.write_i16(self.format_code).await?;
        Ok(())
    }
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
    async fn test_write_backend_key_data() {
        let msg = BackendMessage::BackendKeyData {
            process_id: 12345,
            secret_key: 67890,
        };
        let mut buf = Vec::new();
        msg.write(&mut buf).await.unwrap();

        assert_eq!(buf[0], b'K');
        // length = 4 + 8 = 12
        assert_eq!(&buf[1..5], &12i32.to_be_bytes());
        // process_id = 12345
        assert_eq!(&buf[5..9], &12345i32.to_be_bytes());
        // secret_key = 67890
        assert_eq!(&buf[9..13], &67890i32.to_be_bytes());
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
    async fn test_write_error_response() {
        let msg = BackendMessage::ErrorResponse {
            fields: vec![
                ErrorField {
                    code: b'S',
                    value: "ERROR".to_string(),
                },
                ErrorField {
                    code: b'C',
                    value: "42P01".to_string(),
                },
                ErrorField {
                    code: b'M',
                    value: "table does not exist".to_string(),
                },
            ],
        };
        let mut buf = Vec::new();
        msg.write(&mut buf).await.unwrap();

        assert_eq!(buf[0], b'E');
        // Verify message type and check that fields are present
        // Field 1: 'S' + "ERROR\0" = 1 + 6 = 7 bytes
        // Field 2: 'C' + "42P01\0" = 1 + 6 = 7 bytes
        // Field 3: 'M' + "table does not exist\0" = 1 + 21 = 22 bytes
        // Terminator: 1 byte
        // Total body length: 7 + 7 + 22 + 1 = 37 bytes
        let body_len = i32::from_be_bytes([buf[1], buf[2], buf[3], buf[4]]);
        assert_eq!(body_len, 4 + 37);

        // Verify first field
        assert_eq!(buf[5], b'S');
        assert_eq!(&buf[6..12], b"ERROR\0");

        // Verify second field
        assert_eq!(buf[12], b'C');
        assert_eq!(&buf[13..19], b"42P01\0");

        // Verify third field
        assert_eq!(buf[19], b'M');
        assert_eq!(&buf[20..41], b"table does not exist\0");

        // Verify terminator
        assert_eq!(buf[41], 0);
    }

    #[tokio::test]
    async fn test_write_row_description() {
        let msg = BackendMessage::RowDescription {
            fields: vec![FieldDescription {
                name: "col".to_string(),
                table_oid: 0,
                column_id: 0,
                type_oid: 23, // INT4
                type_size: 4,
                type_modifier: -1,
                format_code: 0,
            }],
        };
        let mut buf = Vec::new();
        msg.write(&mut buf).await.unwrap();

        assert_eq!(buf[0], b'T');
        // Verify field count
        let field_count = i16::from_be_bytes([buf[5], buf[6]]);
        assert_eq!(field_count, 1);
    }

    #[tokio::test]
    async fn test_write_empty_row_description() {
        let msg = BackendMessage::RowDescription { fields: vec![] };
        let mut buf = Vec::new();
        msg.write(&mut buf).await.unwrap();

        assert_eq!(buf[0], b'T');
        // length = 4 + 2 (field count) = 6
        assert_eq!(&buf[1..5], &6i32.to_be_bytes());
        // field count = 0
        assert_eq!(&buf[5..7], &0i16.to_be_bytes());
    }

    #[tokio::test]
    async fn test_write_data_row() {
        let msg = BackendMessage::DataRow {
            values: vec![
                DataValue::Binary(b"hello".to_vec()), // non-empty value
                DataValue::Binary(vec![]),            // empty value
                DataValue::Null,                      // NULL
            ],
        };
        let mut buf = Vec::new();
        msg.write(&mut buf).await.unwrap();

        assert_eq!(buf[0], b'D');
        // Verify column count
        let col_count = i16::from_be_bytes([buf[5], buf[6]]);
        assert_eq!(col_count, 3);

        // Verify first value: length=5, "hello"
        let val1_len = i32::from_be_bytes([buf[7], buf[8], buf[9], buf[10]]);
        assert_eq!(val1_len, 5);
        assert_eq!(&buf[11..16], b"hello");

        // Verify second value: length=0 (empty)
        let val2_len = i32::from_be_bytes([buf[16], buf[17], buf[18], buf[19]]);
        assert_eq!(val2_len, 0);

        // Verify third value: length=-1 (NULL)
        let val3_len = i32::from_be_bytes([buf[20], buf[21], buf[22], buf[23]]);
        assert_eq!(val3_len, -1);
    }

    #[tokio::test]
    async fn test_write_command_complete() {
        let msg = BackendMessage::CommandComplete {
            tag: "SELECT 1".to_string(),
        };
        let mut buf = Vec::new();
        msg.write(&mut buf).await.unwrap();

        assert_eq!(buf[0], b'C');
        // length = 4 + 9 ("SELECT 1\0") = 13
        assert_eq!(&buf[1..5], &13i32.to_be_bytes());
        assert_eq!(&buf[5..], b"SELECT 1\0");
    }

    #[tokio::test]
    async fn test_write_empty_query_response() {
        let msg = BackendMessage::EmptyQueryResponse;
        let mut buf = Vec::new();
        msg.write(&mut buf).await.unwrap();

        assert_eq!(buf, vec![b'I', 0, 0, 0, 4]);
    }
}
