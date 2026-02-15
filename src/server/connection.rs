mod error;
mod state;

pub use error::ConnectionError;
use state::{ConnectionState, Portal, PreparedStatement};

use futures_util::{SinkExt, StreamExt};
use std::sync::Arc;
use tokio::net::TcpStream;
use tokio_util::codec::Framed;
use tokio_util::sync::CancellationToken;

use crate::datum::Value;
use crate::engine::Engine;
use crate::protocol::{
    BackendMessage, BindMessage, CloseMessage, CloseTarget, DataValue, DescribeMessage,
    DescribeTarget, ErrorInfo, ExecuteMessage, FieldDescription, FormatCode, FrontendMessage,
    ParseMessage, PostgresCodec, TransactionStatus, sql_state,
};
use crate::session::{QueryResult, Session};
use crate::sql::Parser;
use crate::storage::{Replacer, Storage};

/// A single client connection.
///
/// Handles the PostgreSQL wire protocol and delegates SQL execution to [`Session`].
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
pub struct Connection<S: Storage, R: Replacer> {
    framed: Framed<TcpStream, PostgresCodec>,
    pid: i32,
    state: ConnectionState,
    session: Session<S, R>,
}

impl<S: Storage, R: Replacer> Connection<S, R> {
    /// Creates a new connection with the given engine.
    pub fn new(
        framed: Framed<TcpStream, PostgresCodec>,
        pid: i32,
        engine: Arc<Engine<S, R>>,
    ) -> Self {
        Self {
            framed,
            pid,
            state: ConnectionState::new(),
            session: Session::new(engine),
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
                self.handle_query(&query).await?;
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
    /// Delegates SQL parsing and execution to the session.
    async fn handle_query(&mut self, query: &str) -> Result<(), ConnectionError> {
        println!("(pid={}) Query: {}", self.pid, query);

        match self.session.execute_query(query).await {
            Ok(None) => {
                self.framed.send(BackendMessage::EmptyQueryResponse).await?;
            }
            Ok(Some(QueryResult::Command { tag })) => {
                self.send_command_complete(tag).await?;
            }
            Ok(Some(QueryResult::Rows { columns, rows })) => {
                self.send_row_description(&columns).await?;
                self.send_data_rows(&rows).await?;
                self.send_command_complete(format!("SELECT {}", rows.len()))
                    .await?;
            }
            Err(e) => {
                self.framed.send(e.to_error_info().into()).await?;
            }
        }

        self.send_ready_for_query().await
    }

    /// Handle a Parse message - create a prepared statement.
    async fn handle_parse(&mut self, msg: ParseMessage) -> Result<(), ConnectionError> {
        println!(
            "(pid={}) Parse: name='{}', query='{}'",
            self.pid, msg.statement_name, msg.query
        );

        // Parse the SQL
        let ast = match Parser::new(&msg.query).parse() {
            Ok(Some(ast)) => ast,
            Ok(None) => {
                // Empty query not allowed in Extended Query Protocol
                let error = ErrorInfo::new(sql_state::SYNTAX_ERROR, "empty query");
                return self.send_error(error, true).await;
            }
            Err(err) => {
                // Parse error - send error response with position
                let error = ErrorInfo::new(sql_state::SYNTAX_ERROR, &err.message)
                    .with_position(err.position());
                return self.send_error(error, true).await;
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
        if let Err(error) = self.state.resolve_statement(&msg.statement_name) {
            return self.send_error(error, true).await;
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

        let stmt = match msg.target_type {
            DescribeTarget::Statement => {
                match self.state.resolve_statement(&msg.name) {
                    Ok(stmt) => {
                        // Send ParameterDescription
                        let param_types = stmt.param_types.clone();
                        self.framed
                            .send(BackendMessage::ParameterDescription { param_types })
                            .await?;

                        &stmt.ast
                    }
                    Err(error) => return self.send_error(error, true).await,
                }
            }
            DescribeTarget::Portal => match self.state.resolve_portal_statement(&msg.name) {
                Ok(stmt) => &stmt.ast,
                Err(error) => return self.send_error(error, true).await,
            },
        };

        match self.session.describe_statement(stmt).await {
            Ok(Some(columns)) => self.send_row_description(&columns).await,
            Ok(None) => {
                self.framed.send(BackendMessage::NoData).await?;
                Ok(())
            }
            Err(e) => self.send_error(e.to_error_info(), true).await,
        }
    }

    /// Handle an Execute message - execute a portal.
    async fn handle_execute(&mut self, msg: ExecuteMessage) -> Result<(), ConnectionError> {
        println!(
            "(pid={}) Execute: portal='{}', max_rows={}",
            self.pid, msg.portal_name, msg.max_rows
        );

        let stmt = match self.state.resolve_portal_statement(&msg.portal_name) {
            Ok(stmt) => stmt,
            Err(error) => return self.send_error(error, true).await,
        };

        // Execute the statement via Session.
        // In the Extended Query Protocol, RowDescription is sent by Describe,
        // so Execute only sends DataRow messages and CommandComplete.
        match self.session.execute_statement(&stmt.ast).await {
            Ok(QueryResult::Command { tag }) => {
                self.send_command_complete(tag).await?;
            }
            Ok(QueryResult::Rows { rows, .. }) => {
                self.send_data_rows(&rows).await?;
                let tag = format!("SELECT {}", rows.len());
                self.send_command_complete(tag).await?;
            }
            Err(e) => {
                return self.send_error(e.to_error_info(), true).await;
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
            CloseTarget::Statement => self.state.close_statement(&msg.name),
            CloseTarget::Portal => self.state.close_portal(&msg.name),
        }

        self.framed.send(BackendMessage::CloseComplete).await?;
        Ok(())
    }

    /// Handle a Sync message - end implicit transaction and clean up.
    async fn handle_sync(&mut self) -> Result<(), ConnectionError> {
        println!("(pid={}) Sync", self.pid);

        self.state.in_error = false;
        self.state.clear_unnamed();

        self.send_ready_for_query().await
    }

    /// Send an error response and mark the connection as in-error state.
    ///
    /// In error state, subsequent extended query messages (Parse, Bind, Describe,
    /// Execute, Close) are skipped until Sync.
    async fn send_error(
        &mut self,
        error: ErrorInfo,
        into_error_state: bool,
    ) -> Result<(), ConnectionError> {
        self.framed.send(error.into()).await?;
        self.state.in_error = into_error_state;
        Ok(())
    }

    /// Sends a RowDescription message describing the output columns.
    async fn send_row_description(
        &mut self,
        columns: &[crate::executor::ColumnDesc],
    ) -> Result<(), ConnectionError> {
        let row_description = BackendMessage::RowDescription {
            fields: columns
                .iter()
                .map(|col| {
                    let (table_oid, column_id) = match &col.source {
                        Some(s) => (s.table_oid as i32, s.column_id),
                        None => (0, 0),
                    };
                    FieldDescription {
                        name: col.name.clone(),
                        table_oid,
                        column_id,
                        type_oid: col.ty.oid(),
                        type_size: col.ty.fixed_size().map(|s| s as i16).unwrap_or(-1),
                        type_modifier: -1,
                        format_code: FormatCode::Text,
                    }
                })
                .collect(),
        };
        self.framed.send(row_description).await?;
        Ok(())
    }

    /// Sends Row messages for each row in the result set.
    ///
    /// Used by Extended Query Protocol where RowDescription is sent
    /// separately by Describe, and Execute only sends DataRow messages.
    async fn send_data_rows(
        &mut self,
        rows: &[crate::executor::Row],
    ) -> Result<(), ConnectionError> {
        for row in rows {
            let values: Vec<DataValue> = row
                .record
                .values
                .iter()
                .map(|v| match v {
                    Value::Null => DataValue::Null,
                    _ => DataValue::Data(v.to_text().into_bytes()),
                })
                .collect();
            self.framed.send(BackendMessage::DataRow { values }).await?;
        }
        Ok(())
    }

    /// Sends a CommandComplete message with the given tag.
    async fn send_command_complete(&mut self, tag: String) -> Result<(), ConnectionError> {
        self.framed
            .send(BackendMessage::CommandComplete { tag })
            .await?;
        Ok(())
    }

    /// Send ReadyForQuery and flush the connection.
    ///
    /// This is the common termination sequence for both Simple Query Protocol
    /// (after Query message) and Extended Query Protocol (after Sync message).
    async fn send_ready_for_query(&mut self) -> Result<(), ConnectionError> {
        let status = match self.session.transaction() {
            Some(tx) => match tx.failed {
                true => TransactionStatus::Failed,
                false => TransactionStatus::InTransaction,
            },
            None => TransactionStatus::Idle,
        };
        let message = BackendMessage::ReadyForQuery { status };
        self.framed.send(message).await?;
        self.framed.flush().await?;
        Ok(())
    }
}
