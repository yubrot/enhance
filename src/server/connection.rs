mod error;

pub use error::ConnectionError;

use futures_util::{SinkExt, StreamExt};
use tokio::net::TcpStream;
use tokio_util::codec::Framed;
use tokio_util::sync::CancellationToken;

use crate::protocol::{
    BackendMessage, ErrorField, FrontendMessage, PostgresCodec, TransactionStatus,
};

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
    framed: Framed<TcpStream, PostgresCodec>,
    pid: i32,
}

impl Connection {
    pub fn new(framed: Framed<TcpStream, PostgresCodec>, pid: i32) -> Self {
        Self { framed, pid }
    }

    /// Classify a query and return the appropriate command completion tag.
    /// Returns None if the query is empty (should send EmptyQueryResponse).
    ///
    /// NOTE: This is a stub implementation. Real SQL parsing comes in Weeks 13-14.
    fn classify_query(query: &str) -> Option<&'static str> {
        let query = query.trim();

        if query.is_empty() {
            return None;
        }

        // Use case-insensitive ASCII comparison without allocation
        if query.len() >= 6 && query[..6].eq_ignore_ascii_case("SELECT") {
            Some("SELECT 0")
        } else if query.len() >= 3 && query[..3].eq_ignore_ascii_case("SET") {
            Some("SET")
        } else if query.len() >= 12 && query[..12].eq_ignore_ascii_case("CREATE TABLE") {
            Some("CREATE TABLE")
        } else if query.len() >= 6 && query[..6].eq_ignore_ascii_case("CREATE") {
            Some("CREATE")
        } else if query.len() >= 6 && query[..6].eq_ignore_ascii_case("INSERT") {
            Some("INSERT 0 0")
        } else if query.len() >= 6 && query[..6].eq_ignore_ascii_case("UPDATE") {
            Some("UPDATE 0")
        } else if query.len() >= 6 && query[..6].eq_ignore_ascii_case("DELETE") {
            Some("DELETE 0")
        } else if (query.len() >= 5 && query[..5].eq_ignore_ascii_case("BEGIN"))
            || (query.len() >= 17 && query[..17].eq_ignore_ascii_case("START TRANSACTION"))
        {
            Some("BEGIN")
        } else if query.len() >= 6 && query[..6].eq_ignore_ascii_case("COMMIT") {
            Some("COMMIT")
        } else if query.len() >= 8 && query[..8].eq_ignore_ascii_case("ROLLBACK") {
            Some("ROLLBACK")
        } else {
            // Unknown query type
            Some("OK")
        }
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
        let message = match self.framed.next().await {
            Some(Ok(msg)) => msg,
            Some(Err(e)) => return Err(e.into()),
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

        match Self::classify_query(query) {
            None => {
                // Empty query
                self.framed.send(BackendMessage::EmptyQueryResponse).await?;
            }
            Some("SELECT 0") => {
                // SELECT: return empty result set
                // https://www.postgresql.org/docs/current/protocol-message-formats.html#PROTOCOL-MESSAGE-FORMATS-COMMANDCOMPLETE
                self.framed
                    .send(BackendMessage::RowDescription { fields: vec![] })
                    .await?;
                self.framed
                    .send(BackendMessage::CommandComplete {
                        tag: "SELECT 0".to_string(),
                    })
                    .await?;
            }
            Some("OK") => {
                // Unknown query type - return error
                // https://www.postgresql.org/docs/current/protocol-error-fields.html
                self.framed
                    .send(BackendMessage::ErrorResponse {
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
                    })
                    .await?;
            }
            Some(tag) => {
                // All other recognized query types
                self.framed
                    .send(BackendMessage::CommandComplete {
                        tag: tag.to_string(),
                    })
                    .await?;
            }
        }

        // Always send ReadyForQuery after response
        self.framed
            .send(BackendMessage::ReadyForQuery {
                status: TransactionStatus::Idle,
            })
            .await?;

        self.framed.flush().await?;
        Ok(())
    }
}
