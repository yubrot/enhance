use tokio::io::{AsyncWriteExt, BufWriter};
use tokio::net::TcpStream;

use crate::protocol::{BackendMessage, StartupMessage, TransactionStatus};
use crate::server::connection::ConnectionError;

pub enum HandshakeResult {
    /// Handshake completed successfully, transitioning to query phase.
    Success {
        socket: BufWriter<TcpStream>,
        secret_key: i32,
    },
    /// Handshake was a CancelRequest.
    CancelRequested { pid: i32, secret_key: i32 },
}

/// A single client handshake implementation.
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
///    - Implement SSL/TLS support (currently rejected)
///    - Add rate limiting for failed authentication attempts
pub struct Handshake {
    socket: BufWriter<TcpStream>,
    pid: i32,
}

impl Handshake {
    pub fn new(socket: TcpStream, pid: i32) -> Self {
        Self {
            socket: BufWriter::new(socket),
            pid,
        }
    }

    pub async fn run(mut self) -> Result<HandshakeResult, ConnectionError> {
        loop {
            let message = StartupMessage::read(&mut self.socket).await?;

            match message {
                StartupMessage::SslRequest | StartupMessage::GssEncRequest => {
                    // Reject SSL/GSSAPI with 'N'
                    self.socket.write_all(b"N").await?;
                    self.socket.flush().await?;
                }
                StartupMessage::Startup { parameters, .. } => {
                    // TODO: proper auth
                    println!(
                        "Startup: user={}, database={:?}",
                        parameters.user, parameters.database
                    );

                    let secret_key = rand::random::<i32>();
                    self.send_startup_info(secret_key).await?;

                    return Ok(HandshakeResult::Success {
                        socket: self.socket,
                        secret_key,
                    });
                }
                StartupMessage::CancelRequest {
                    process_id,
                    secret_key,
                } => {
                    return Ok(HandshakeResult::CancelRequested {
                        pid: process_id,
                        secret_key,
                    });
                }
            }
        }
    }

    async fn send_startup_info(&mut self, secret_key: i32) -> Result<(), ConnectionError> {
        BackendMessage::AuthenticationOk
            .write(&mut self.socket)
            .await?;

        BackendMessage::BackendKeyData {
            process_id: self.pid,
            secret_key,
        }
        .write(&mut self.socket)
        .await?;

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

        BackendMessage::ReadyForQuery {
            status: TransactionStatus::Idle,
        }
        .write(&mut self.socket)
        .await?;

        self.socket.flush().await?;
        Ok(())
    }
}
