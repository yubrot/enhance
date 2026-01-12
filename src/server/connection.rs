mod error;

pub use error::ConnectionError;

use tokio::io::{AsyncReadExt, AsyncWriteExt};
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
pub struct Connection {
    socket: TcpStream,
    process_id: i32,
    secret_key: i32,
    state: ConnectionState,
    buffer: Vec<u8>,
}

impl Connection {
    pub fn new(socket: TcpStream, process_id: i32) -> Self {
        // Generate a simple secret key
        let secret_key = process_id.wrapping_mul(0x5DEECE66u32 as i32);

        Self {
            socket,
            process_id,
            secret_key,
            state: ConnectionState::AwaitingStartup,
            buffer: Vec::with_capacity(8192),
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
        // Read the length prefix
        let length = self.socket.read_i32().await?;

        if !(8..=10000).contains(&length) {
            return Err(ConnectionError::Protocol(ProtocolError::InvalidMessage));
        }

        // Read the message body (length includes the 4-byte length field itself)
        self.buffer.resize((length - 4) as usize, 0);
        self.socket.read_exact(&mut self.buffer).await?;
        let message = StartupMessage::parse(&self.buffer)?;

        match message {
            StartupMessage::SslRequest => {
                // Reject SSL with 'N'
                self.socket.write_all(b"N").await?;
                self.state = ConnectionState::SslRejected;
            }
            StartupMessage::GssEncRequest => {
                // Reject GSSAPI encryption with 'N'
                self.socket.write_all(b"N").await?;
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
        let msg = BackendMessage::AuthenticationOk;
        self.socket.write_all(&msg.encode()).await?;
        self.state = ConnectionState::SendingStartupInfo;
        Ok(())
    }

    async fn send_startup_info(&mut self) -> Result<(), ConnectionError> {
        let mut buf = Vec::new();

        // Send BackendKeyData
        BackendMessage::BackendKeyData {
            process_id: self.process_id,
            secret_key: self.secret_key,
        }
        .encode_into(&mut buf);

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
            .encode_into(&mut buf);
        }

        // Send ReadyForQuery
        BackendMessage::ReadyForQuery {
            status: TransactionStatus::Idle,
        }
        .encode_into(&mut buf);

        self.socket.write_all(&buf).await?;
        self.state = ConnectionState::Ready;
        Ok(())
    }

    async fn handle_query_phase(&mut self) -> Result<(), ConnectionError> {
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

        // Read message body
        if length > 4 {
            let body_len = (length - 4) as usize;
            self.buffer.resize(body_len, 0);
            self.socket.read_exact(&mut self.buffer).await?;
        }

        match msg_type {
            b'X' => {
                // Terminate message
                self.state = ConnectionState::Terminated;
            }
            _ => {
                // Send ErrorResponse for any query (not yet implemented)
                let error = BackendMessage::ErrorResponse {
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
                };

                let mut buf = Vec::new();
                error.encode_into(&mut buf);

                // Send ReadyForQuery to allow client to continue
                BackendMessage::ReadyForQuery {
                    status: TransactionStatus::Idle,
                }
                .encode_into(&mut buf);

                self.socket.write_all(&buf).await?;
            }
        }

        Ok(())
    }
}
