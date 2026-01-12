mod error;

pub use error::ConnectionError;

use tokio::io::{AsyncReadExt, AsyncWriteExt, BufWriter};
use tokio::net::TcpStream;
use tokio_util::sync::CancellationToken;

use crate::protocol::{BackendMessage, ErrorField, ProtocolError, TransactionStatus};

/// A single client connection.
///
/// NOTE: This is a minimal implementation suitable for learning/development.
/// For production use, the following improvements would be necessary:
///
/// 1. Connection Lifecycle:
///    - Implement idle connection timeout
///    - Add query execution timeout
///    - Support graceful shutdown notification from listener
///
/// 2. Protocol Completeness:
///    - Handle all frontend message types (currently only startup + terminate)
///    - Support COPY protocol for bulk data transfer
pub struct Connection {
    socket: BufWriter<TcpStream>,
    pid: i32,
    cancel_token: CancellationToken,
}

impl Connection {
    pub fn new(socket: BufWriter<TcpStream>, pid: i32, cancel_token: CancellationToken) -> Self {
        Self {
            socket,
            pid,
            cancel_token,
        }
    }

    pub async fn run(&mut self) -> Result<(), ConnectionError> {
        loop {
            tokio::select! {
                res = Self::handle_query_phase_internal(&mut self.socket) => {
                    if let Some(should_terminate) = res? {
                        if should_terminate {
                            return Ok(());
                        }
                    }
                }
                _ = self.cancel_token.cancelled() => {
                    println!("Connection cancelled (pid={})", self.pid);
                    return Ok(());
                }
            }
        }
    }

    async fn handle_query_phase_internal(
        socket: &mut BufWriter<TcpStream>,
    ) -> Result<Option<bool>, ConnectionError> {
        // Read message type byte
        let msg_type = match socket.read_u8().await {
            Ok(t) => t,
            Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => {
                return Ok(Some(true));
            }
            Err(e) => return Err(e.into()),
        };

        // Read length
        let length = socket.read_i32().await?;
        if length < 4 {
            return Err(ConnectionError::Protocol(ProtocolError::InvalidMessage));
        }

        // Skip message body
        if length > 4 {
            let body_len = (length - 4) as usize;
            let mut buf = vec![0u8; body_len];
            socket.read_exact(&mut buf).await?;
        }

        match msg_type {
            b'X' => {
                return Ok(Some(true));
            }
            _ => {
                BackendMessage::ErrorResponse {
                    fields: vec![
                        ErrorField {
                            code: b'S',
                            value: "ERROR".to_string(),
                        },
                        ErrorField {
                            code: b'V',
                            value: "ERROR".to_string(),
                        },
                        ErrorField {
                            code: b'C',
                            value: "0A000".to_string(),
                        },
                        ErrorField {
                            code: b'M',
                            value: "Queries not yet implemented".to_string(),
                        },
                    ],
                }
                .write(socket)
                .await?;

                BackendMessage::ReadyForQuery {
                    status: TransactionStatus::Idle,
                }
                .write(socket)
                .await?;

                socket.flush().await?;
            }
        }

        Ok(None)
    }
}
