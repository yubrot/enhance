use std::io;
use tokio::io::{AsyncWrite, AsyncWriteExt};

use crate::protocol::codec::write_cstring;

// TODO: Reduce await by using BytesMut etc.

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
    /// '1' - Parse complete
    ParseComplete,
    /// '2' - Bind complete
    BindComplete,
    /// '3' - Close complete
    CloseComplete,
    /// 'n' - No data
    NoData,
    /// 's' - Portal suspended
    PortalSuspended,
    /// 't' - Parameter description
    ParameterDescription { param_types: Vec<i32> },
}

impl BackendMessage {
    /// Returns the message type byte.
    fn ty(&self) -> u8 {
        match self {
            BackendMessage::AuthenticationOk => b'R',
            BackendMessage::BackendKeyData { .. } => b'K',
            BackendMessage::ParameterStatus { .. } => b'S',
            BackendMessage::ReadyForQuery { .. } => b'Z',
            BackendMessage::ErrorResponse { .. } => b'E',
            BackendMessage::RowDescription { .. } => b'T',
            BackendMessage::DataRow { .. } => b'D',
            BackendMessage::CommandComplete { .. } => b'C',
            BackendMessage::EmptyQueryResponse => b'I',
            BackendMessage::ParseComplete => b'1',
            BackendMessage::BindComplete => b'2',
            BackendMessage::CloseComplete => b'3',
            BackendMessage::NoData => b'n',
            BackendMessage::PortalSuspended => b's',
            BackendMessage::ParameterDescription { .. } => b't',
        }
    }

    /// Returns the body length in bytes (excluding type byte and length field).
    fn body_len(&self) -> usize {
        match self {
            BackendMessage::AuthenticationOk => 4,
            BackendMessage::BackendKeyData { .. } => 8,
            BackendMessage::ParameterStatus { name, value } => name.len() + 1 + value.len() + 1,
            BackendMessage::ReadyForQuery { .. } => 1,
            BackendMessage::ErrorResponse { fields } => {
                fields.iter().map(|f| f.encoded_len()).sum::<usize>() + 1
            }
            BackendMessage::RowDescription { fields } => {
                2 + fields.iter().map(|f| f.encoded_len()).sum::<usize>()
            }
            BackendMessage::DataRow { values } => {
                2 + values.iter().map(|v| v.encoded_len()).sum::<usize>()
            }
            BackendMessage::CommandComplete { tag } => tag.len() + 1,
            BackendMessage::EmptyQueryResponse => 0,
            BackendMessage::ParseComplete => 0,
            BackendMessage::BindComplete => 0,
            BackendMessage::CloseComplete => 0,
            BackendMessage::NoData => 0,
            BackendMessage::PortalSuspended => 0,
            BackendMessage::ParameterDescription { param_types } => 2 + (param_types.len() * 4),
        }
    }

    /// Writes message header (type byte and length) to the stream.
    async fn write_head<W: AsyncWrite + Unpin>(&self, w: &mut W) -> io::Result<()> {
        w.write_u8(self.ty()).await?;
        w.write_i32((4 + self.body_len()) as i32).await?;
        Ok(())
    }

    /// Writes message body to the stream.
    async fn write_body<W: AsyncWrite + Unpin>(&self, w: &mut W) -> io::Result<()> {
        match self {
            BackendMessage::AuthenticationOk => {
                w.write_i32(0).await?; // auth type 0 = Ok
            }
            BackendMessage::BackendKeyData {
                process_id,
                secret_key,
            } => {
                w.write_i32(*process_id).await?;
                w.write_i32(*secret_key).await?;
            }
            BackendMessage::ParameterStatus { name, value } => {
                write_cstring(w, name).await?;
                write_cstring(w, value).await?;
            }
            BackendMessage::ReadyForQuery { status } => {
                w.write_u8(status.as_byte()).await?;
            }
            BackendMessage::ErrorResponse { fields } => {
                for field in fields {
                    field.write(w).await?;
                }
                w.write_u8(0).await?; // terminator
            }
            BackendMessage::RowDescription { fields } => {
                w.write_i16(fields.len() as i16).await?;
                for field in fields {
                    field.write(w).await?;
                }
            }
            BackendMessage::DataRow { values } => {
                w.write_i16(values.len() as i16).await?;
                for value in values {
                    value.write(w).await?;
                }
            }
            BackendMessage::CommandComplete { tag } => {
                write_cstring(w, tag).await?;
            }
            BackendMessage::EmptyQueryResponse
            | BackendMessage::ParseComplete
            | BackendMessage::BindComplete
            | BackendMessage::CloseComplete
            | BackendMessage::NoData
            | BackendMessage::PortalSuspended => {
                // No body for these messages
            }
            BackendMessage::ParameterDescription { param_types } => {
                w.write_i16(param_types.len() as i16).await?;
                for oid in param_types {
                    w.write_i32(*oid).await?;
                }
            }
        }
        Ok(())
    }

    /// Writes this message to the stream.
    pub async fn write<W: AsyncWrite + Unpin>(&self, w: &mut W) -> io::Result<()> {
        self.write_head(w).await?;
        self.write_body(w).await?;
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

    /// Helper to write a message and return the buffer.
    async fn write_message(msg: &BackendMessage) -> Vec<u8> {
        let mut buf = Vec::new();
        msg.write(&mut buf).await.unwrap();
        buf
    }

    /// Helper to read i32 from buffer at offset.
    fn read_i32(buf: &[u8], offset: usize) -> i32 {
        i32::from_be_bytes([
            buf[offset],
            buf[offset + 1],
            buf[offset + 2],
            buf[offset + 3],
        ])
    }

    /// Helper to read i16 from buffer at offset.
    fn read_i16(buf: &[u8], offset: usize) -> i16 {
        i16::from_be_bytes([buf[offset], buf[offset + 1]])
    }

    #[tokio::test]
    async fn test_write_authentication_ok() {
        let msg = BackendMessage::AuthenticationOk;
        let buf = write_message(&msg).await;
        assert_eq!(buf, vec![b'R', 0, 0, 0, 8, 0, 0, 0, 0]);
    }

    #[tokio::test]
    async fn test_write_backend_key_data() {
        let msg = BackendMessage::BackendKeyData {
            process_id: 12345,
            secret_key: 67890,
        };
        let buf = write_message(&msg).await;

        assert_eq!(buf[0], b'K');
        assert_eq!(read_i32(&buf, 1), 12); // length = 4 + 8 = 12
        assert_eq!(read_i32(&buf, 5), 12345); // process_id
        assert_eq!(read_i32(&buf, 9), 67890); // secret_key
    }

    #[tokio::test]
    async fn test_write_parameter_status() {
        let msg = BackendMessage::ParameterStatus {
            name: "server_version".to_string(),
            value: "16.0".to_string(),
        };
        let buf = write_message(&msg).await;

        assert_eq!(buf[0], b'S');
        assert_eq!(read_i32(&buf, 1), 24); // length = 4 + 15 + 5 = 24
        assert_eq!(&buf[5..], b"server_version\016.0\0");
    }

    #[tokio::test]
    async fn test_write_ready_for_query() {
        let msg = BackendMessage::ReadyForQuery {
            status: TransactionStatus::Idle,
        };
        let buf = write_message(&msg).await;
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
        let buf = write_message(&msg).await;

        assert_eq!(buf[0], b'E');
        assert_eq!(read_i32(&buf, 1), 41); // 4 + (7 + 7 + 22 + 1)

        // Verify fields
        assert_eq!(buf[5], b'S');
        assert_eq!(&buf[6..12], b"ERROR\0");
        assert_eq!(buf[12], b'C');
        assert_eq!(&buf[13..19], b"42P01\0");
        assert_eq!(buf[19], b'M');
        assert_eq!(&buf[20..41], b"table does not exist\0");
        assert_eq!(buf[41], 0); // terminator
    }

    #[tokio::test]
    async fn test_write_row_description() {
        let msg = BackendMessage::RowDescription {
            fields: vec![
                FieldDescription {
                    name: "col".to_string(),
                    table_oid: 0,
                    column_id: 0,
                    type_oid: 23, // INT4
                    type_size: 4,
                    type_modifier: -1,
                    format_code: 0,
                },
                FieldDescription {
                    name: "text_col".to_string(),
                    table_oid: 16384,
                    column_id: 2,
                    type_oid: 25, // TEXT (variable length)
                    type_size: -1,
                    type_modifier: -1,
                    format_code: 0,
                },
                FieldDescription {
                    name: "binary_col".to_string(),
                    table_oid: 16384,
                    column_id: 3,
                    type_oid: 17, // BYTEA
                    type_size: -1,
                    type_modifier: -1,
                    format_code: 1, // binary format
                },
            ],
        };
        let buf = write_message(&msg).await;

        assert_eq!(buf[0], b'T');
        assert_eq!(read_i16(&buf, 5), 3); // field count
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
        let buf = write_message(&msg).await;

        assert_eq!(buf[0], b'D');
        assert_eq!(read_i16(&buf, 5), 3); // column count

        // Verify values
        assert_eq!(read_i32(&buf, 7), 5); // length of "hello"
        assert_eq!(&buf[11..16], b"hello");
        assert_eq!(read_i32(&buf, 16), 0); // empty value
        assert_eq!(read_i32(&buf, 20), -1); // NULL
    }

    #[tokio::test]
    async fn test_write_command_complete() {
        let msg = BackendMessage::CommandComplete {
            tag: "SELECT 1".to_string(),
        };
        let buf = write_message(&msg).await;

        assert_eq!(buf[0], b'C');
        assert_eq!(read_i32(&buf, 1), 13); // 4 + 9
        assert_eq!(&buf[5..], b"SELECT 1\0");
    }

    #[tokio::test]
    async fn test_write_empty_query_response() {
        let msg = BackendMessage::EmptyQueryResponse;
        let buf = write_message(&msg).await;
        assert_eq!(buf, vec![b'I', 0, 0, 0, 4]);
    }

    #[tokio::test]
    async fn test_write_parse_complete() {
        let msg = BackendMessage::ParseComplete;
        let buf = write_message(&msg).await;
        assert_eq!(buf, vec![b'1', 0, 0, 0, 4]);
    }

    #[tokio::test]
    async fn test_write_bind_complete() {
        let msg = BackendMessage::BindComplete;
        let buf = write_message(&msg).await;
        assert_eq!(buf, vec![b'2', 0, 0, 0, 4]);
    }

    #[tokio::test]
    async fn test_write_close_complete() {
        let msg = BackendMessage::CloseComplete;
        let buf = write_message(&msg).await;
        assert_eq!(buf, vec![b'3', 0, 0, 0, 4]);
    }

    #[tokio::test]
    async fn test_write_no_data() {
        let msg = BackendMessage::NoData;
        let buf = write_message(&msg).await;
        assert_eq!(buf, vec![b'n', 0, 0, 0, 4]);
    }

    #[tokio::test]
    async fn test_write_portal_suspended() {
        let msg = BackendMessage::PortalSuspended;
        let buf = write_message(&msg).await;
        assert_eq!(buf, vec![b's', 0, 0, 0, 4]);
    }

    #[tokio::test]
    async fn test_write_parameter_description() {
        let msg = BackendMessage::ParameterDescription {
            param_types: vec![23, 25, 1043], // INT4, TEXT, VARCHAR
        };
        let buf = write_message(&msg).await;

        assert_eq!(buf[0], b't');
        assert_eq!(read_i32(&buf, 1), 18); // 4 + 2 + 3*4
        assert_eq!(read_i16(&buf, 5), 3); // param count
        assert_eq!(read_i32(&buf, 7), 23); // INT4
        assert_eq!(read_i32(&buf, 11), 25); // TEXT
        assert_eq!(read_i32(&buf, 15), 1043); // VARCHAR
    }
}
