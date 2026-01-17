use futures_util::{SinkExt, StreamExt};
use tokio::io::AsyncWriteExt;
use tokio::net::TcpStream;
use tokio_util::codec::Framed;

use crate::protocol::{
    BackendMessage, PostgresCodec, StartupCodec, StartupMessage, TransactionStatus,
};
use crate::server::connection::ConnectionError;

pub enum HandshakeResult {
    /// Handshake completed successfully, transitioning to query phase.
    Success {
        framed: Framed<TcpStream, PostgresCodec>,
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
    framed: Framed<TcpStream, StartupCodec>,
    pid: i32,
}

impl Handshake {
    pub fn new(socket: TcpStream, pid: i32) -> Self {
        Self {
            framed: Framed::new(socket, StartupCodec::new()),
            pid,
        }
    }

    pub async fn run(mut self) -> Result<HandshakeResult, ConnectionError> {
        loop {
            let message = self.framed.next().await.ok_or_else(|| {
                std::io::Error::new(
                    std::io::ErrorKind::UnexpectedEof,
                    "Connection closed during handshake",
                )
            })??;

            match message {
                StartupMessage::SslRequest | StartupMessage::GssEncRequest => {
                    // Reject SSL/GSSAPI with 'N' - write directly to socket
                    self.framed.get_mut().write_all(b"N").await?;
                    self.framed.get_mut().flush().await?;
                }
                StartupMessage::Startup { parameters, .. } => {
                    // TODO: proper auth
                    println!(
                        "Startup: user={}, database={:?}",
                        parameters.user, parameters.database
                    );

                    let secret_key = rand::random::<i32>();

                    // Send startup info using StartupCodec
                    self.send_startup_info(secret_key).await?;

                    // Transition to query phase
                    let framed = self.framed.map_codec(|c| c.ready());
                    return Ok(HandshakeResult::Success { framed, secret_key });
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

    /// Sends the startup information to the client.
    async fn send_startup_info(&mut self, secret_key: i32) -> Result<(), ConnectionError> {
        self.framed.send(BackendMessage::AuthenticationOk).await?;

        self.framed
            .send(BackendMessage::BackendKeyData {
                process_id: self.pid,
                secret_key,
            })
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
            self.framed
                .send(BackendMessage::ParameterStatus {
                    name: name.to_string(),
                    value: value.to_string(),
                })
                .await?;
        }

        self.framed
            .send(BackendMessage::ReadyForQuery {
                status: TransactionStatus::Idle,
            })
            .await?;

        self.framed.flush().await?;
        Ok(())
    }
}
