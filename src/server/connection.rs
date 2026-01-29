mod error;
mod state;

pub use error::ConnectionError;
use state::{ConnectionState, Portal, PreparedStatement};

use futures_util::{SinkExt, StreamExt};
use std::sync::Arc;
use tokio::net::TcpStream;
use tokio_util::codec::Framed;
use tokio_util::sync::CancellationToken;

use crate::db::Database;
use crate::executor::plan_select;
use crate::heap::Value;
use crate::protocol::{
    BackendMessage, BindMessage, CloseMessage, CloseTarget, DataValue, DescribeMessage,
    DescribeTarget, ErrorInfo, ExecuteMessage, FieldDescription, FormatCode, FrontendMessage,
    ParseMessage, PostgresCodec, TransactionStatus, sql_state,
};
use crate::sql::{Parser, Statement};
use crate::storage::{Replacer, Storage};
use crate::tx::CommandId;

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
pub struct Connection<S: Storage, R: Replacer> {
    framed: Framed<TcpStream, PostgresCodec>,
    pid: i32,
    state: ConnectionState,
    database: Arc<Database<S, R>>,
}

impl<S: Storage + 'static, R: Replacer + 'static> Connection<S, R> {
    pub fn new(
        framed: Framed<TcpStream, PostgresCodec>,
        pid: i32,
        database: Arc<Database<S, R>>,
    ) -> Self {
        Self {
            framed,
            pid,
            state: ConnectionState::new(),
            database,
        }
    }

    /// Returns the command completion tag for a statement with row count.
    fn command_tag(stmt: &Statement, row_count: u64) -> String {
        match stmt {
            Statement::Select(_) => format!("SELECT {}", row_count),
            Statement::Insert(_) => format!("INSERT 0 {}", row_count),
            Statement::Update(_) => format!("UPDATE {}", row_count),
            Statement::Delete(_) => format!("DELETE {}", row_count),
            Statement::CreateTable(_) => "CREATE TABLE".to_string(),
            Statement::DropTable(_) => "DROP TABLE".to_string(),
            Statement::CreateIndex(_) => "CREATE INDEX".to_string(),
            Statement::DropIndex(_) => "DROP INDEX".to_string(),
            Statement::Begin => "BEGIN".to_string(),
            Statement::Commit => "COMMIT".to_string(),
            Statement::Rollback => "ROLLBACK".to_string(),
            Statement::Set(_) => "SET".to_string(),
            Statement::Explain(_) => format!("EXPLAIN {}", row_count),
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
    /// Parses the SQL, and returns appropriate responses.
    async fn handle_query(&mut self, query: &str) -> Result<(), ConnectionError> {
        println!("(pid={}) Query: {}", self.pid, query);

        match Parser::new(query).parse() {
            Ok(None) => {
                // Empty query
                self.framed.send(BackendMessage::EmptyQueryResponse).await?;
            }
            Ok(Some(stmt)) => {
                // Handle transaction control commands
                match &stmt {
                    Statement::Begin => {
                        if self.state.transaction().is_none() {
                            let txid = self.database.tx_manager().begin();
                            self.state.begin_transaction(txid);
                        }
                        // If already in transaction, BEGIN is a no-op (PostgreSQL behavior)
                    }
                    Statement::Commit => {
                        if let Some(transaction) = self.state.transaction() {
                            self.database.tx_manager().commit(transaction.txid)?;
                        }
                        self.state.end_transaction();
                    }
                    Statement::Rollback => {
                        if let Some(transaction) = self.state.transaction() {
                            let _ = self.database.tx_manager().abort(transaction.txid);
                        }
                        self.state.end_transaction();
                    }
                    _ => {
                        // For other statements, increment cid if in active transaction
                        self.state.increment_cid();
                    }
                }

                // Execute statement
                let row_count = match self.execute_statement(&stmt).await {
                    Ok(count) => count,
                    Err(e) => {
                        let error = ErrorInfo::new(sql_state::INTERNAL_ERROR, e.to_string());
                        self.framed.send(error.into()).await?;
                        return self.send_ready_for_query().await;
                    }
                };

                // Send CommandComplete with row count
                let tag = Self::command_tag(&stmt, row_count);
                self.framed
                    .send(BackendMessage::CommandComplete { tag })
                    .await?;
            }
            Err(err) => {
                // Parse error - send error response with position
                let error = ErrorInfo::new(sql_state::SYNTAX_ERROR, &err.message)
                    .with_position(err.position());
                self.framed.send(error.into()).await?;
            }
        }

        self.send_ready_for_query().await
    }

    /// Execute a parsed statement.
    ///
    /// Returns the number of rows affected or returned.
    async fn execute_statement(&mut self, stmt: &Statement) -> Result<u64, ConnectionError> {
        match stmt {
            Statement::Select(select_stmt) => {
                self.execute_select(select_stmt).await
            }
            Statement::Explain(inner_stmt) => {
                self.execute_explain(inner_stmt).await
            }
            Statement::CreateTable(create_stmt) => {
                // Get or create transaction for DDL
                let (txid, cid) = self.get_or_create_transaction();

                match self
                    .database
                    .catalog()
                    .create_table(txid, cid, create_stmt)
                    .await
                {
                    Ok(table_id) => {
                        if table_id > 0 {
                            println!(
                                "(pid={}) Created table '{}' with id {}",
                                self.pid, create_stmt.name, table_id
                            );
                        } else {
                            println!(
                                "(pid={}) Table '{}' already exists (IF NOT EXISTS)",
                                self.pid, create_stmt.name
                            );
                        }
                        // If not in explicit transaction, commit immediately
                        if self.state.transaction().is_none() {
                            self.database.tx_manager().commit(txid)?;
                        }
                        Ok(0)
                    }
                    Err(e) => {
                        // Abort transaction on error
                        let _ = self.database.tx_manager().abort(txid);
                        if self.state.transaction().is_some() {
                            self.state.end_transaction();
                        }
                        Err(ConnectionError::Catalog(e))
                    }
                }
            }
            // Other statements are stubbed for now
            _ => Ok(0),
        }
    }

    /// Execute a SELECT statement.
    async fn execute_select(
        &mut self,
        select_stmt: &crate::sql::SelectStmt,
    ) -> Result<u64, ConnectionError> {
        let (txid, cid) = self.get_or_create_transaction();
        let snapshot = self.database.tx_manager().snapshot(txid, cid);

        // Plan the query
        let mut executor = plan_select(
            select_stmt,
            snapshot,
            self.database.catalog(),
            self.database.pool().clone(),
            self.database.tx_manager().clone(),
        )
        .await
        .map_err(ConnectionError::Executor)?;

        // Send RowDescription
        let fields: Vec<FieldDescription> = executor
            .schema()
            .iter()
            .map(|col| FieldDescription {
                name: col.name.clone(),
                table_oid: 0,
                column_id: 0,
                type_oid: col.type_oid,
                type_size: type_size(col.type_oid),
                type_modifier: -1,
                format_code: FormatCode::Text,
            })
            .collect();
        self.framed
            .send(BackendMessage::RowDescription { fields })
            .await?;

        // Stream rows
        let mut row_count = 0u64;
        while let Some(tuple) = executor.next().await.map_err(ConnectionError::Executor)? {
            let values: Vec<DataValue> = tuple.values.iter().map(value_to_data_value).collect();
            self.framed.send(BackendMessage::DataRow { values }).await?;
            row_count += 1;
        }

        // If not in explicit transaction, commit
        if self.state.transaction().is_none() {
            self.database.tx_manager().commit(txid)?;
        }

        Ok(row_count)
    }

    /// Execute an EXPLAIN statement.
    async fn execute_explain(&mut self, inner_stmt: &Statement) -> Result<u64, ConnectionError> {
        let (txid, cid) = self.get_or_create_transaction();
        let snapshot = self.database.tx_manager().snapshot(txid, cid);

        // Get the plan text based on the inner statement
        let plan_text = match inner_stmt {
            Statement::Select(select_stmt) => {
                let executor = plan_select(
                    select_stmt,
                    snapshot,
                    self.database.catalog(),
                    self.database.pool().clone(),
                    self.database.tx_manager().clone(),
                )
                .await
                .map_err(ConnectionError::Executor)?;
                executor.explain(0)
            }
            _ => {
                // For non-SELECT statements, just return a placeholder
                format!("{:?}", inner_stmt)
            }
        };

        // Send RowDescription for EXPLAIN (single TEXT column)
        self.framed
            .send(BackendMessage::RowDescription {
                fields: vec![FieldDescription {
                    name: "QUERY PLAN".to_string(),
                    table_oid: 0,
                    column_id: 0,
                    type_oid: crate::protocol::type_oid::TEXT,
                    type_size: -1,
                    type_modifier: -1,
                    format_code: FormatCode::Text,
                }],
            })
            .await?;

        // Send each line as a separate row
        let lines: Vec<&str> = plan_text.lines().collect();
        let row_count = lines.len() as u64;
        for line in lines {
            self.framed
                .send(BackendMessage::DataRow {
                    values: vec![DataValue::Binary(line.as_bytes().to_vec())],
                })
                .await?;
        }

        // If not in explicit transaction, commit
        if self.state.transaction().is_none() {
            self.database.tx_manager().commit(txid)?;
        }

        Ok(row_count)
    }

    /// Get the current transaction or create a new one for auto-commit mode.
    fn get_or_create_transaction(&mut self) -> (crate::tx::TxId, CommandId) {
        if let Some(tx) = self.state.transaction() {
            (tx.txid, tx.cid)
        } else {
            let txid = self.database.tx_manager().begin();
            (txid, CommandId::FIRST)
        }
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
        if self.state.get_statement(&msg.statement_name).is_none() {
            let error = ErrorInfo::new(
                sql_state::INVALID_SQL_STATEMENT_NAME,
                format!(
                    "prepared statement \"{}\" does not exist",
                    msg.statement_name
                ),
            );
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

        match msg.target_type {
            DescribeTarget::Statement => {
                let Some(stmt) = self.state.get_statement(&msg.name) else {
                    let error = ErrorInfo::new(
                        sql_state::INVALID_SQL_STATEMENT_NAME,
                        format!("prepared statement \"{}\" does not exist", msg.name),
                    );
                    return self.send_error(error, true).await;
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
                    let error = ErrorInfo::new(
                        sql_state::INVALID_CURSOR_NAME,
                        format!("portal \"{}\" does not exist", msg.name),
                    );
                    return self.send_error(error, true).await;
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
            let error = ErrorInfo::new(
                sql_state::INVALID_CURSOR_NAME,
                format!("portal \"{}\" does not exist", msg.portal_name),
            );
            return self.send_error(error, true).await;
        };

        let statement_name = portal.statement_name.clone();

        let Some(stmt) = self.state.get_statement(&statement_name) else {
            let error = ErrorInfo::new(
                sql_state::INVALID_SQL_STATEMENT_NAME,
                "statement for portal does not exist",
            );
            return self.send_error(error, true).await;
        };

        // Clone AST to avoid borrow issues
        let ast = stmt.ast.clone();

        // Execute the statement
        let row_count = match self.execute_statement(&ast).await {
            Ok(count) => count,
            Err(e) => {
                let error = ErrorInfo::new(sql_state::INTERNAL_ERROR, e.to_string());
                return self.send_error(error, true).await;
            }
        };

        let tag = Self::command_tag(&ast, row_count);
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

    /// Send ReadyForQuery and flush the connection.
    ///
    /// This is the common termination sequence for both Simple Query Protocol
    /// (after Query message) and Extended Query Protocol (after Sync message).
    async fn send_ready_for_query(&mut self) -> Result<(), ConnectionError> {
        let status = match self.state.transaction() {
            Some(tx) => tx.status(),
            None => TransactionStatus::Idle,
        };
        let message = BackendMessage::ReadyForQuery { status };
        self.framed.send(message).await?;
        self.framed.flush().await?;
        Ok(())
    }
}

/// Converts a heap::Value to a protocol DataValue (text format).
fn value_to_data_value(val: &Value) -> DataValue {
    match val {
        Value::Null => DataValue::Null,
        Value::Boolean(b) => {
            let s = if *b { "t" } else { "f" };
            DataValue::Binary(s.as_bytes().to_vec())
        }
        Value::Int16(n) => DataValue::Binary(n.to_string().into_bytes()),
        Value::Int32(n) => DataValue::Binary(n.to_string().into_bytes()),
        Value::Int64(n) => DataValue::Binary(n.to_string().into_bytes()),
        Value::Float32(n) => DataValue::Binary(n.to_string().into_bytes()),
        Value::Float64(n) => DataValue::Binary(n.to_string().into_bytes()),
        Value::Text(s) => DataValue::Binary(s.as_bytes().to_vec()),
        Value::Bytea(b) => {
            // Encode as PostgreSQL bytea hex format: \x followed by hex digits
            let hex: String = b.iter().map(|byte| format!("{:02x}", byte)).collect();
            DataValue::Binary(format!("\\x{}", hex).into_bytes())
        }
    }
}

/// Returns the type size for a given type OID.
///
/// Returns -1 for variable-length types, or the fixed size for fixed-size types.
fn type_size(type_oid: i32) -> i16 {
    use crate::protocol::type_oid::*;
    match type_oid {
        BOOL => 1,
        INT2 => 2,
        INT4 => 4,
        INT8 => 8,
        FLOAT4 => 4,
        FLOAT8 => 8,
        _ => -1, // Variable length (TEXT, BYTEA, etc.)
    }
}
