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
    ErrorField, ErrorFieldCode, ExecuteMessage, FrontendMessage, ParseMessage, PostgresCodec,
    TransactionStatus, sql_state,
};
use crate::sql::{Parser, Statement};

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
///    - Handle all frontend message types
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

    /// Parses a SQL query and returns the AST.
    ///
    /// Returns `Ok(None)` for empty queries, `Ok(Some(stmt))` for valid SQL,
    /// or `Err` for syntax errors.
    fn parse_query(query: &str) -> Result<Option<Statement>, crate::sql::SyntaxError> {
        let query = query.trim();

        if query.is_empty() {
            return Ok(None);
        }

        let mut parser = Parser::new(query);
        parser.parse().map(Some)
    }

    /// Returns the command completion tag for a statement.
    ///
    /// NOTE: Row counts are stubbed to 0 for now. Real execution comes in later steps.
    fn command_tag(stmt: &Statement) -> String {
        match stmt {
            Statement::Select(_) => "SELECT 0".to_string(),
            Statement::Insert(_) => "INSERT 0 0".to_string(),
            Statement::Update(_) => "UPDATE 0".to_string(),
            Statement::Delete(_) => "DELETE 0".to_string(),
            Statement::CreateTable(_) => "CREATE TABLE".to_string(),
            Statement::DropTable(_) => "DROP TABLE".to_string(),
            Statement::CreateIndex(_) => "CREATE INDEX".to_string(),
            Statement::DropIndex(_) => "DROP INDEX".to_string(),
            Statement::Begin => "BEGIN".to_string(),
            Statement::Commit => "COMMIT".to_string(),
            Statement::Rollback => "ROLLBACK".to_string(),
            Statement::Set(_) => "SET".to_string(),
            Statement::Explain(_) => "EXPLAIN".to_string(),
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
            }
            FrontendMessage::Terminate => return Ok(true),
            FrontendMessage::Parse(_)
            | FrontendMessage::Bind(_)
            | FrontendMessage::Describe(_)
            | FrontendMessage::Execute(_)
            | FrontendMessage::Close(_)
                if self.state.in_error =>
            {
                // Skip extended query messages when in error state
            }
            FrontendMessage::Parse(msg) => {
                self.handle_parse(msg).await?;
            }
            FrontendMessage::Bind(msg) => {
                self.handle_bind(msg).await?;
            }
            FrontendMessage::Describe(msg) => {
                self.handle_describe(msg).await?;
            }
            FrontendMessage::Execute(msg) => {
                self.handle_execute(msg).await?;
            }
            FrontendMessage::Close(msg) => {
                self.handle_close(msg).await?;
            }
            FrontendMessage::Sync => {
                self.handle_sync().await?;
            }
            FrontendMessage::Flush => {
                self.framed.flush().await?;
            }
        }
        Ok(false)
    }

    /// Handle a query from the client (Simple Query Protocol).
    ///
    /// Parses the SQL, and returns appropriate responses.
    /// NOTE: Actual execution is stubbed - real execution comes in later steps.
    async fn handle_query(&mut self, query: &str) -> Result<(), ConnectionError> {
        println!("(pid={}) Query: {}", self.pid, query);

        match Self::parse_query(query) {
            Ok(None) => {
                // Empty query
                self.framed.send(BackendMessage::EmptyQueryResponse).await?;
            }
            Ok(Some(stmt)) => {
                // Successfully parsed
                let tag = Self::command_tag(&stmt);

                // For SELECT, send RowDescription before CommandComplete
                if matches!(stmt, Statement::Select(_)) {
                    self.framed
                        .send(BackendMessage::RowDescription { fields: vec![] })
                        .await?;
                }

                self.framed
                    .send(BackendMessage::CommandComplete { tag })
                    .await?;
            }
            Err(err) => {
                // Parse error - send error response with position
                self.framed
                    .send(BackendMessage::ErrorResponse {
                        fields: vec![
                            ErrorField::new(ErrorFieldCode::Severity, "ERROR"),
                            ErrorField::new(ErrorFieldCode::SeverityNonLocalized, "ERROR"),
                            ErrorField::new(ErrorFieldCode::SqlState, sql_state::SYNTAX_ERROR),
                            ErrorField::new(ErrorFieldCode::Message, &err.message),
                            ErrorField::new(ErrorFieldCode::Position, err.position().to_string()),
                        ],
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

    /// Handle a Parse message - create a prepared statement.
    async fn handle_parse(&mut self, msg: ParseMessage) -> Result<(), ConnectionError> {
        println!(
            "(pid={}) Parse: name='{}', query='{}'",
            self.pid, msg.statement_name, msg.query
        );

        // Parse the SQL
        let ast = match Self::parse_query(&msg.query) {
            Ok(Some(ast)) => ast,
            Ok(None) => {
                // Empty query not allowed in Extended Query Protocol
                return self
                    .send_error(sql_state::SYNTAX_ERROR, "empty query".to_string(), true)
                    .await;
            }
            Err(err) => {
                // Parse error - send error response with position
                let position = err.position();
                return self
                    .send_error_with_position(sql_state::SYNTAX_ERROR, err.message, position, true)
                    .await;
            }
        };

        // Store the prepared statement
        let stmt = PreparedStatement {
            ast,
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
                    sql_state::INVALID_SQL_STATEMENT_NAME,
                    format!(
                        "prepared statement \"{}\" does not exist",
                        msg.statement_name
                    ),
                    true,
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
                let Some(stmt) = self.state.get_statement(&msg.name) else {
                    return self
                        .send_error(
                            sql_state::INVALID_SQL_STATEMENT_NAME,
                            format!("prepared statement \"{}\" does not exist", msg.name),
                            true,
                        )
                        .await;
                };

                // Send ParameterDescription
                self.framed
                    .send(BackendMessage::ParameterDescription {
                        param_types: stmt.param_types.clone(),
                    })
                    .await?;

                // For stub: Send NoData (no result columns yet)
                // NOTE: Real implementation analyzes query to determine columns
                self.framed.send(BackendMessage::NoData).await?;
            }
            DescribeTarget::Portal => {
                let Some(_portal) = self.state.get_portal(&msg.name) else {
                    return self
                        .send_error(
                            sql_state::INVALID_CURSOR_NAME,
                            format!("portal \"{}\" does not exist", msg.name),
                            true,
                        )
                        .await;
                };

                // For stub: Send NoData (no result columns yet)
                self.framed.send(BackendMessage::NoData).await?;
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

        let Some(portal) = self.state.get_portal(&msg.portal_name) else {
            return self
                .send_error(
                    sql_state::INVALID_CURSOR_NAME,
                    format!("portal \"{}\" does not exist", msg.portal_name),
                    true,
                )
                .await;
        };

        let Some(stmt) = self.state.get_statement(&portal.statement_name) else {
            return self
                .send_error(
                    sql_state::INVALID_SQL_STATEMENT_NAME,
                    "statement for portal does not exist".to_string(),
                    true,
                )
                .await;
        };

        // Stub execution - use stored AST to determine response
        // NOTE: Real execution comes in later steps
        let tag = Self::command_tag(&stmt.ast);
        self.framed
            .send(BackendMessage::CommandComplete { tag })
            .await?;

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

        self.state.in_error = false;
        self.state.clear_unnamed();

        self.framed
            .send(BackendMessage::ReadyForQuery {
                status: TransactionStatus::Idle,
            })
            .await?;

        self.framed.flush().await?;
        Ok(())
    }

    /// Send an error response and mark the connection as in-error state.
    ///
    /// In error state, subsequent extended query messages (Parse, Bind, Describe,
    /// Execute, Close) are skipped until Sync.
    async fn send_error(
        &mut self,
        code: &str,
        message: String,
        into_error_state: bool,
    ) -> Result<(), ConnectionError> {
        self.framed
            .send(BackendMessage::error(code, message))
            .await?;
        self.state.in_error = into_error_state;
        Ok(())
    }

    /// Send an error response with position information.
    async fn send_error_with_position(
        &mut self,
        code: &str,
        message: String,
        position: usize,
        into_error_state: bool,
    ) -> Result<(), ConnectionError> {
        self.framed
            .send(BackendMessage::ErrorResponse {
                fields: vec![
                    ErrorField::new(ErrorFieldCode::Severity, "ERROR"),
                    ErrorField::new(ErrorFieldCode::SeverityNonLocalized, "ERROR"),
                    ErrorField::new(ErrorFieldCode::SqlState, code),
                    ErrorField::new(ErrorFieldCode::Message, &message),
                    ErrorField::new(ErrorFieldCode::Position, position.to_string()),
                ],
            })
            .await?;
        self.state.in_error = into_error_state;
        Ok(())
    }
}
