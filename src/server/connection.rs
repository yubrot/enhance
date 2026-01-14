mod error;

pub use error::ConnectionError;

use tokio::io::{AsyncWriteExt, BufWriter};
use tokio::net::TcpStream;
use tokio_util::sync::CancellationToken;

use crate::protocol::{BackendMessage, ErrorField, FrontendMessage, TransactionStatus};

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
}

impl Connection {
    pub fn new(socket: BufWriter<TcpStream>, pid: i32) -> Self {
        Self { socket, pid }
    }

    pub async fn run(&mut self, cancel_token: CancellationToken) -> Result<(), ConnectionError> {
        loop {
            tokio::select! {
                res = self.handle_message() => {
                    if res? {
                        return Ok(());
                    }
                }
                _ = cancel_token.cancelled() => {
                    println!("Connection cancelled (pid={})", self.pid);
                    return Ok(());
                }
            }
        }
    }

    /// Handle a single message from the client.
    /// Returns true if the connection should terminate.
    async fn handle_message(&mut self) -> Result<bool, ConnectionError> {
        let message = match FrontendMessage::read(&mut self.socket).await? {
            Some(msg) => msg,
            None => return Ok(true), // EOF - client disconnected
        };

        match message {
            FrontendMessage::Query(query) => {
                self.handle_query(query.trim()).await?;
                Ok(false)
            }
            FrontendMessage::Terminate => Ok(true),
        }
    }

    /// Handle a query from the client.
    ///
    /// NOTE: This is a minimal implementation that returns dummy responses.
    /// Real SQL parsing and execution will be implemented in Weeks 13-14.
    async fn handle_query(&mut self, query: &str) -> Result<(), ConnectionError> {
        println!("(pid={}) Query: {}", self.pid, query);

        // Handle empty query
        if query.is_empty() {
            BackendMessage::EmptyQueryResponse
                .write(&mut self.socket)
                .await?;
            BackendMessage::ReadyForQuery {
                status: TransactionStatus::Idle,
            }
            .write(&mut self.socket)
            .await?;
            self.socket.flush().await?;
            return Ok(());
        }

        // Classify query by prefix and respond with appropriate dummy response
        let query_upper = query.to_uppercase();

        if query_upper.starts_with("SELECT") {
            // SELECT: return empty result set
            // https://www.postgresql.org/docs/current/protocol-message-formats.html#PROTOCOL-MESSAGE-FORMATS-COMMANDCOMPLETE
            BackendMessage::RowDescription { fields: vec![] }
                .write(&mut self.socket)
                .await?;
            BackendMessage::CommandComplete {
                tag: "SELECT 0".to_string(),
            }
            .write(&mut self.socket)
            .await?;
        } else if query_upper.starts_with("SET") {
            BackendMessage::CommandComplete {
                tag: "SET".to_string(),
            }
            .write(&mut self.socket)
            .await?;
        } else if query_upper.starts_with("CREATE TABLE") {
            BackendMessage::CommandComplete {
                tag: "CREATE TABLE".to_string(),
            }
            .write(&mut self.socket)
            .await?;
        } else if query_upper.starts_with("CREATE") {
            BackendMessage::CommandComplete {
                tag: "CREATE".to_string(),
            }
            .write(&mut self.socket)
            .await?;
        } else if query_upper.starts_with("INSERT") {
            BackendMessage::CommandComplete {
                tag: "INSERT 0 0".to_string(),
            }
            .write(&mut self.socket)
            .await?;
        } else if query_upper.starts_with("UPDATE") {
            BackendMessage::CommandComplete {
                tag: "UPDATE 0".to_string(),
            }
            .write(&mut self.socket)
            .await?;
        } else if query_upper.starts_with("DELETE") {
            BackendMessage::CommandComplete {
                tag: "DELETE 0".to_string(),
            }
            .write(&mut self.socket)
            .await?;
        } else if query_upper.starts_with("BEGIN") || query_upper.starts_with("START TRANSACTION") {
            BackendMessage::CommandComplete {
                tag: "BEGIN".to_string(),
            }
            .write(&mut self.socket)
            .await?;
        } else if query_upper.starts_with("COMMIT") {
            BackendMessage::CommandComplete {
                tag: "COMMIT".to_string(),
            }
            .write(&mut self.socket)
            .await?;
        } else if query_upper.starts_with("ROLLBACK") {
            BackendMessage::CommandComplete {
                tag: "ROLLBACK".to_string(),
            }
            .write(&mut self.socket)
            .await?;
        } else {
            // Unknown query type - return error
            // https://www.postgresql.org/docs/current/protocol-error-fields.html
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
                        value: "42601".to_string(), // syntax_error
                    },
                    ErrorField {
                        code: b'M',
                        value: format!(
                            "Unrecognized query type: {}",
                            query.chars().take(50).collect::<String>()
                        ),
                    },
                ],
            }
            .write(&mut self.socket)
            .await?;
        }

        // Always send ReadyForQuery after response
        BackendMessage::ReadyForQuery {
            status: TransactionStatus::Idle,
        }
        .write(&mut self.socket)
        .await?;

        self.socket.flush().await?;
        Ok(())
    }
}
