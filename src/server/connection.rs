mod error;
mod state;

pub use error::ConnectionError;
use state::{ConnectionState, Portal, PreparedStatement};

use futures_util::{SinkExt, StreamExt};
use tokio::net::TcpStream;
use tokio_util::codec::Framed;
use tokio_util::sync::CancellationToken;

use crate::protocol::{
    BackendMessage, BindMessage, CloseMessage, CloseTarget, DescribeMessage, DescribeTarget,
    ErrorField, ExecuteMessage, FrontendMessage, ParseMessage, PostgresCodec, TransactionStatus,
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
    state: ConnectionState,
}

impl Connection {
    pub fn new(framed: Framed<TcpStream, PostgresCodec>, pid: i32) -> Self {
        Self {
            framed,
            pid,
            state: ConnectionState::new(),
        }
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
            FrontendMessage::Parse(msg) => {
                self.handle_parse(msg).await?;
                Ok(false)
            }
            FrontendMessage::Bind(msg) => {
                self.handle_bind(msg).await?;
                Ok(false)
            }
            FrontendMessage::Describe(msg) => {
                self.handle_describe(msg).await?;
                Ok(false)
            }
            FrontendMessage::Execute(msg) => {
                self.handle_execute(msg).await?;
                Ok(false)
            }
            FrontendMessage::Close(msg) => {
                self.handle_close(msg).await?;
                Ok(false)
            }
            FrontendMessage::Sync => {
                self.handle_sync().await?;
                Ok(false)
            }
            FrontendMessage::Flush => {
                self.framed.flush().await?;
                Ok(false)
            }
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
                self.framed.send(BackendMessage::RowDescription { fields: vec![] }).await?;
                self.framed.send(BackendMessage::CommandComplete {
                    tag: "SELECT 0".to_string(),
                }).await?;
            }
            Some("OK") => {
                // Unknown query type - return error
                // https://www.postgresql.org/docs/current/protocol-error-fields.html
                self.framed.send(BackendMessage::ErrorResponse {
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
                }).await?;
            }
            Some(tag) => {
                // All other recognized query types
                self.framed.send(BackendMessage::CommandComplete {
                    tag: tag.to_string(),
                }).await?;
            }
        }

        // Always send ReadyForQuery after response
        self.framed.send(BackendMessage::ReadyForQuery {
            status: TransactionStatus::Idle,
        }).await?;

        self.framed.flush().await?;
        Ok(())
    }

    /// Handle a Parse message - create a prepared statement.
    async fn handle_parse(&mut self, msg: ParseMessage) -> Result<(), ConnectionError> {
        println!(
            "(pid={}) Parse: name='{}', query='{}'",
            self.pid, msg.statement_name, msg.query
        );

        // Store the prepared statement
        // NOTE: In future weeks, this is where SQL parsing/validation happens
        let stmt = PreparedStatement {
            query: msg.query,
            param_types: msg.param_types,
        };
        self.state.put_statement(msg.statement_name, stmt);

        // Send success
        self.framed.send(BackendMessage::ParseComplete).await?;
        Ok(())
    }

    /// Handle a Bind message - bind parameters to create a portal.
    async fn handle_bind(&mut self, msg: BindMessage) -> Result<(), ConnectionError> {
        println!(
            "(pid={}) Bind: portal='{}', statement='{}'",
            self.pid, msg.portal_name, msg.statement_name
        );

        // Verify statement exists
        if self.state.get_statement(&msg.statement_name).is_none() {
            return self
                .send_error(
                    "26000",
                    format!(
                        "prepared statement \"{}\" does not exist",
                        msg.statement_name
                    ),
                )
                .await;
        }

        // Create portal
        let portal = Portal {
            statement_name: msg.statement_name,
            _param_values: msg.param_values,
            _param_format_codes: msg.param_format_codes,
            _result_format_codes: msg.result_format_codes,
        };
        self.state.put_portal(msg.portal_name, portal);

        self.framed.send(BackendMessage::BindComplete).await?;
        Ok(())
    }

    /// Handle a Describe message - get metadata about a statement or portal.
    async fn handle_describe(&mut self, msg: DescribeMessage) -> Result<(), ConnectionError> {
        println!(
            "(pid={}) Describe: type={:?}, name='{}'",
            self.pid, msg.target_type, msg.name
        );

        match msg.target_type {
            DescribeTarget::Statement => {
                if let Some(stmt) = self.state.get_statement(&msg.name) {
                    // Send ParameterDescription
                    self.framed.send(BackendMessage::ParameterDescription {
                        param_types: stmt.param_types.clone(),
                    }).await?;

                    // For stub: Send NoData (no result columns yet)
                    // NOTE: Real implementation analyzes query to determine columns
                    self.framed.send(BackendMessage::NoData).await?;
                } else {
                    return self
                        .send_error(
                            "26000",
                            format!("prepared statement \"{}\" does not exist", msg.name),
                        )
                        .await;
                }
            }
            DescribeTarget::Portal => {
                if self.state.get_portal(&msg.name).is_some() {
                    // For stub: Send NoData (no result columns yet)
                    self.framed.send(BackendMessage::NoData).await?;
                } else {
                    return self
                        .send_error("34000", format!("portal \"{}\" does not exist", msg.name))
                        .await;
                }
            }
        }
        Ok(())
    }

    /// Handle an Execute message - execute a portal.
    async fn handle_execute(&mut self, msg: ExecuteMessage) -> Result<(), ConnectionError> {
        println!(
            "(pid={}) Execute: portal='{}', max_rows={}",
            self.pid, msg.portal_name, msg.max_rows
        );

        let portal = match self.state.get_portal(&msg.portal_name) {
            Some(p) => p,
            None => {
                return self
                    .send_error(
                        "34000",
                        format!("portal \"{}\" does not exist", msg.portal_name),
                    )
                    .await;
            }
        };

        let stmt = match self.state.get_statement(&portal.statement_name) {
            Some(s) => s,
            None => {
                return self
                    .send_error("26000", "statement for portal does not exist")
                    .await;
            }
        };

        // Stub execution - classify query and return appropriate response
        // NOTE: Uses same classification as handle_query() - real execution comes later
        match Self::classify_query(&stmt.query) {
            None => {
                // Empty query
                self.framed.send(BackendMessage::EmptyQueryResponse).await?;
            }
            Some(tag) => {
                // All query types return CommandComplete (errors ignored in extended protocol)
                self.framed.send(BackendMessage::CommandComplete {
                    tag: tag.to_string(),
                }).await?;
            }
        }

        Ok(())
    }

    /// Handle a Close message - close a statement or portal.
    async fn handle_close(&mut self, msg: CloseMessage) -> Result<(), ConnectionError> {
        println!(
            "(pid={}) Close: type={:?}, name='{}'",
            self.pid, msg.target_type, msg.name
        );

        match msg.target_type {
            CloseTarget::Statement => {
                self.state.close_statement(&msg.name);
            }
            CloseTarget::Portal => {
                self.state.close_portal(&msg.name);
            }
        }

        self.framed.send(BackendMessage::CloseComplete).await?;
        Ok(())
    }

    /// Handle a Sync message - end implicit transaction and clean up.
    async fn handle_sync(&mut self) -> Result<(), ConnectionError> {
        println!("(pid={}) Sync", self.pid);

        // Clear unnamed statement/portal (per PostgreSQL spec)
        self.state.clear_unnamed();

        // Send ReadyForQuery
        self.framed.send(BackendMessage::ReadyForQuery {
            status: TransactionStatus::Idle,
        }).await?;

        self.framed.flush().await?;
        Ok(())
    }

    /// Send an error response to the client.
    async fn send_error(
        &mut self,
        code: &str,
        message: impl Into<String>,
    ) -> Result<(), ConnectionError> {
        self.framed.send(BackendMessage::ErrorResponse {
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
                    value: code.to_string(),
                },
                ErrorField {
                    code: b'M',
                    value: message.into(),
                },
            ],
        }).await?;
        Ok(())
    }
}
