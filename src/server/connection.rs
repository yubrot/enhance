mod error;

pub use error::ConnectionError;

use tokio::io::{AsyncReadExt, AsyncWriteExt, BufWriter};
use tokio::net::TcpStream;

use crate::protocol::{
    BackendMessage, ErrorField, ProtocolError, StartupMessage, TransactionStatus,
};

/// Connection state during the startup sequence.
#[derive(Debug, Clone, Copy, PartialEq)]
enum ConnectionState {
    /// Initial state - waiting for first message
    AwaitingStartup,
    /// Received SSLRequest, sent 'N', waiting for StartupMessage
    SslRejected,
    /// Received StartupMessage, processing authentication
    Authenticating,
    /// Authentication complete, sending startup messages
    SendingStartupInfo,
    /// Ready to accept queries
    Ready,
    /// Connection should be closed
    Terminated,
}

/// A single client connection.
///
/// NOTE: This is a minimal implementation suitable for learning/development.
/// For production use, the following improvements would be necessary:
///
/// 1. Authentication:
///    - Implement proper authentication methods (MD5, SCRAM-SHA-256)
///    - Validate credentials against user database
///    - Support pg_hba.conf-style access control rules
///
/// 2. Security:
///    - Use cryptographically secure random number generator for secret_key
///    - Implement SSL/TLS support (currently rejected)
///    - Add rate limiting for failed authentication attempts
///
/// 3. Connection Lifecycle:
///    - Implement idle connection timeout
///    - Add query execution timeout
///    - Support graceful shutdown notification from server
///
/// 4. Protocol Completeness:
///    - Handle all frontend message types (currently only startup + terminate)
///    - Implement query cancellation via CancelRequest
///    - Support COPY protocol for bulk data transfer
pub struct Connection {
    socket: BufWriter<TcpStream>,
    process_id: i32,
    secret_key: i32,
    state: ConnectionState,
}

impl Connection {
    pub fn new(socket: TcpStream, process_id: i32) -> Self {
        // NOTE: Production would use a CSPRNG (e.g., rand::thread_rng())
        // The secret_key is used to authenticate CancelRequest messages
        let secret_key = process_id.wrapping_mul(0x5DEECE66u32 as i32);

        Self {
            socket: BufWriter::new(socket),
            process_id,
            secret_key,
            state: ConnectionState::AwaitingStartup,
        }
    }

    pub async fn run(&mut self) -> Result<(), ConnectionError> {
        loop {
            match self.state {
                ConnectionState::AwaitingStartup | ConnectionState::SslRejected => {
                    self.handle_startup_message().await?;
                }
                ConnectionState::Authenticating => {
                    self.send_authentication_ok().await?;
                }
                ConnectionState::SendingStartupInfo => {
                    self.send_startup_info().await?;
                }
                ConnectionState::Ready => {
                    self.handle_query_phase().await?;
                }
                ConnectionState::Terminated => {
                    return Ok(());
                }
            }
        }
    }

    async fn handle_startup_message(&mut self) -> Result<(), ConnectionError> {
        let message = StartupMessage::read(&mut self.socket).await?;

        match message {
            StartupMessage::SslRequest => {
                // Reject SSL with 'N'
                self.socket.write_all(b"N").await?;
                self.socket.flush().await?;
                self.state = ConnectionState::SslRejected;
            }
            StartupMessage::GssEncRequest => {
                // Reject GSSAPI encryption with 'N'
                self.socket.write_all(b"N").await?;
                self.socket.flush().await?;
                self.state = ConnectionState::SslRejected;
            }
            StartupMessage::Startup {
                protocol_version: _,
                parameters,
            } => {
                // TODO: checks user and password
                println!(
                    "Startup: user={}, database={:?}",
                    parameters.user, parameters.database
                );
                self.state = ConnectionState::Authenticating;
            }
            StartupMessage::CancelRequest { .. } => {
                // TODO: cancellation
                // Just close the connection for cancel requests
                self.state = ConnectionState::Terminated;
            }
        }

        Ok(())
    }

    async fn send_authentication_ok(&mut self) -> Result<(), ConnectionError> {
        BackendMessage::AuthenticationOk
            .write(&mut self.socket)
            .await?;
        self.socket.flush().await?;
        self.state = ConnectionState::SendingStartupInfo;
        Ok(())
    }

    async fn send_startup_info(&mut self) -> Result<(), ConnectionError> {
        // Send BackendKeyData
        BackendMessage::BackendKeyData {
            process_id: self.process_id,
            secret_key: self.secret_key,
        }
        .write(&mut self.socket)
        .await?;

        // Send essential ParameterStatus messages
        // psql expects certain parameters to be present
        let params = [
            ("server_version", "16.0"),
            ("server_encoding", "UTF8"),
            ("client_encoding", "UTF8"),
            ("DateStyle", "ISO, MDY"),
            ("TimeZone", "UTC"),
            ("integer_datetimes", "on"),
            ("standard_conforming_strings", "on"),
        ];

        for (name, value) in params {
            BackendMessage::ParameterStatus {
                name: name.to_string(),
                value: value.to_string(),
            }
            .write(&mut self.socket)
            .await?;
        }

        // Send ReadyForQuery
        BackendMessage::ReadyForQuery {
            status: TransactionStatus::Idle,
        }
        .write(&mut self.socket)
        .await?;

        self.socket.flush().await?;
        self.state = ConnectionState::Ready;
        Ok(())
    }

    async fn handle_query_phase(&mut self) -> Result<(), ConnectionError> {
        // NOTE: Production improvements needed:
        // - Add message size limit (e.g., max 1GB) to prevent memory exhaustion
        // - Implement read timeout to detect hung clients
        // - Use a bounded buffer pool instead of allocating per-message

        // Read message type byte
        let msg_type = match self.socket.read_u8().await {
            Ok(t) => t,
            Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => {
                self.state = ConnectionState::Terminated;
                return Ok(());
            }
            Err(e) => return Err(e.into()),
        };

        // Read length (big-endian, includes the 4-byte length field itself)
        let length = self.socket.read_i32().await?;
        if length < 4 {
            return Err(ConnectionError::Protocol(ProtocolError::InvalidMessage));
        }

        // Skip message body if present
        if length > 4 {
            let body_len = (length - 4) as usize;
            let mut buf = vec![0u8; body_len];
            self.socket.read_exact(&mut buf).await?;
        }

        match msg_type {
            b'X' => {
                // Terminate message
                self.state = ConnectionState::Terminated;
            }
            _ => {
                // Send ErrorResponse for any query (not yet implemented)
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
                .write(&mut self.socket)
                .await?;

                // Send ReadyForQuery to allow client to continue
                BackendMessage::ReadyForQuery {
                    status: TransactionStatus::Idle,
                }
                .write(&mut self.socket)
                .await?;

                self.socket.flush().await?;
            }
        }

        Ok(())
    }
}
