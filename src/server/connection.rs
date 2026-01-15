mod error;
mod state;

pub use error::ConnectionError;
use state::{ConnectionState, Portal, PreparedStatement};

use tokio::io::{AsyncWriteExt, BufWriter};
use tokio::net::TcpStream;
use tokio_util::sync::CancellationToken;

use crate::protocol::{
    BackendMessage, BindMessage, CloseMessage, CloseTarget, DescribeMessage, DescribeTarget,
    ErrorField, ExecuteMessage, FrontendMessage, ParseMessage, TransactionStatus,
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
    socket: BufWriter<TcpStream>,
    pid: i32,
    state: ConnectionState,
}

impl Connection {
    pub fn new(socket: BufWriter<TcpStream>, pid: i32) -> Self {
        Self {
            socket,
            pid,
            state: ConnectionState::new(),
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
                self.socket.flush().await?;
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
        BackendMessage::ParseComplete
            .write(&mut self.socket)
            .await?;
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

        BackendMessage::BindComplete.write(&mut self.socket).await?;
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
                    BackendMessage::ParameterDescription {
                        param_types: stmt.param_types.clone(),
                    }
                    .write(&mut self.socket)
                    .await?;

                    // For stub: Send NoData (no result columns yet)
                    // NOTE: Real implementation analyzes query to determine columns
                    BackendMessage::NoData.write(&mut self.socket).await?;
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
                    BackendMessage::NoData.write(&mut self.socket).await?;
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
        // NOTE: This mirrors handle_query() logic - real execution comes later
        let query_upper = stmt.query.to_uppercase();

        if query_upper.trim().is_empty() {
            BackendMessage::EmptyQueryResponse
                .write(&mut self.socket)
                .await?;
        } else if query_upper.starts_with("SELECT") {
            BackendMessage::CommandComplete {
                tag: "SELECT 0".to_string(),
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
            // Default for other statement types
            BackendMessage::CommandComplete {
                tag: "OK".to_string(),
            }
            .write(&mut self.socket)
            .await?;
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

        BackendMessage::CloseComplete
            .write(&mut self.socket)
            .await?;
        Ok(())
    }

    /// Handle a Sync message - end implicit transaction and clean up.
    async fn handle_sync(&mut self) -> Result<(), ConnectionError> {
        println!("(pid={}) Sync", self.pid);

        // Clear unnamed statement/portal (per PostgreSQL spec)
        self.state.clear_unnamed();

        // Send ReadyForQuery
        BackendMessage::ReadyForQuery {
            status: TransactionStatus::Idle,
        }
        .write(&mut self.socket)
        .await?;

        self.socket.flush().await?;
        Ok(())
    }

    /// Send an error response to the client.
    async fn send_error(
        &mut self,
        code: &str,
        message: impl Into<String>,
    ) -> Result<(), ConnectionError> {
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
                    value: code.to_string(),
                },
                ErrorField {
                    code: b'M',
                    value: message.into(),
                },
            ],
        }
        .write(&mut self.socket)
        .await?;
        Ok(())
    }
}
