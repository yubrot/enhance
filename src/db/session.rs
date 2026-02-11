//! Client session management for database operations.
//!
//! The [`Session`] type represents a single client session and manages
//! transaction state and SQL execution. It sits between the protocol layer
//! (Connection) and the infrastructure layer (Database).

use std::future::Future;
use std::sync::Arc;

use super::Database;
use super::error::DatabaseError;
use crate::executor::{self, ColumnDesc, Row};
use crate::sql::{Parser, Statement};
use crate::storage::{Replacer, Storage};
use crate::tx::{CommandId, TxId};

/// Result of executing a SQL statement.
#[derive(Debug)]
pub enum QueryResult {
    /// Command completed successfully (DDL, DML, transaction control).
    Command {
        /// Command completion tag (e.g., "CREATE TABLE", "INSERT 0 1").
        ///
        /// This tag is sent as-is in the wire protocol's `CommandComplete` message.
        /// The format follows PostgreSQL's command tag conventions.
        tag: String,
    },
    /// Query returned rows (SELECT, EXPLAIN).
    Rows {
        /// Column metadata for the result set.
        columns: Vec<ColumnDesc>,
        /// Result rows.
        rows: Vec<Row>,
    },
}

impl QueryResult {
    fn command(tag: impl Into<String>) -> Self {
        Self::Command { tag: tag.into() }
    }
}

/// Transaction state for a session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TransactionState {
    /// Transaction ID.
    pub txid: TxId,
    /// Command ID within this transaction.
    pub cid: CommandId,
    /// Whether the transaction has failed and awaits ROLLBACK.
    pub failed: bool,
}

/// A client session managing transaction state and SQL execution.
///
/// Session provides the business logic layer between the protocol layer
/// (Connection) and the infrastructure layer (Database). It handles:
/// - Transaction lifecycle (BEGIN/COMMIT/ROLLBACK)
/// - Auto-commit mode for individual statements
/// - SQL parsing and execution coordination
///
/// # Transaction Cleanup
///
/// When a `Session` is dropped with an active transaction, the transaction is
/// automatically rolled back. This prevents zombie transactions from accumulating
/// in the transaction manager (e.g., when a client disconnects unexpectedly).
pub struct Session<S: Storage, R: Replacer> {
    database: Arc<Database<S, R>>,
    transaction: Option<TransactionState>,
}

impl<S: Storage, R: Replacer> Drop for Session<S, R> {
    fn drop(&mut self) {
        self.rollback();
    }
}

impl<S: Storage, R: Replacer> Session<S, R> {
    /// Creates a new session with the given database.
    pub fn new(database: Arc<Database<S, R>>) -> Self {
        Self {
            database,
            transaction: None,
        }
    }

    /// Returns a reference to the underlying database.
    pub fn database(&self) -> &Arc<Database<S, R>> {
        &self.database
    }

    /// Returns the current transaction state, if any.
    pub fn transaction(&self) -> Option<TransactionState> {
        self.transaction
    }

    /// Begins an explicit transaction.
    ///
    /// If already in a transaction, this is a no-op (following PostgreSQL behavior).
    pub fn begin(&mut self) {
        if self.transaction.is_none() {
            let txid = self.database.tx_manager().begin();
            self.transaction = Some(TransactionState {
                txid,
                cid: CommandId::FIRST,
                failed: false,
            });
        }
    }

    /// Commits the current transaction.
    ///
    /// If not in a transaction, this is a no-op.
    ///
    /// # Errors
    ///
    /// Returns an error if the transaction manager fails to commit.
    pub fn commit(&mut self) -> Result<(), DatabaseError> {
        if let Some(tx) = self.transaction.take() {
            self.database.tx_manager().commit(tx.txid)?;
        }
        Ok(())
    }

    /// Rolls back the current transaction.
    ///
    /// If not in a transaction, this is a no-op.
    pub fn rollback(&mut self) {
        if let Some(tx) = self.transaction.take() {
            let _ = self.database.tx_manager().abort(tx.txid);
        }
    }

    /// Parses and executes a SQL query string.
    ///
    /// This is the main entry point for the Simple Query Protocol.
    ///
    /// # Returns
    ///
    /// * `Ok(None)` - Empty query (no statement parsed)
    /// * `Ok(Some(QueryResult))` - Execution result
    /// * `Err(DatabaseError::Parse)` - If SQL parsing fails
    /// * `Err(DatabaseError::*)` - If execution fails
    pub async fn execute_query(
        &mut self,
        query: &str,
    ) -> Result<Option<QueryResult>, DatabaseError> {
        match Parser::new(query).parse() {
            Ok(None) => Ok(None),
            Ok(Some(stmt)) => Ok(Some(self.execute_statement(&stmt).await?)),
            Err(err) => Err(DatabaseError::Parse(err)),
        }
    }

    /// Returns the output column descriptions for a statement without executing it.
    ///
    /// Used by the Extended Query Protocol's Describe message to send
    /// `RowDescription` before Execute.
    ///
    /// Returns `None` for statements that don't produce rows (DDL, DML,
    /// transaction control).
    ///
    /// # Errors
    ///
    /// Returns an error if query planning fails (e.g., table not found).
    pub async fn describe_statement(
        &mut self,
        stmt: &Statement,
    ) -> Result<Option<Vec<ColumnDesc>>, DatabaseError> {
        match stmt {
            Statement::Select(select_stmt) => {
                self.run_in_transaction(false, |db, txid, cid| async move {
                    let snapshot = db.tx_manager().snapshot(txid, cid);
                    let plan = executor::plan_select(select_stmt, db.catalog(), &snapshot).await?;
                    Ok(Some(plan.columns().to_vec()))
                })
                .await
            }
            Statement::Explain(inner_stmt) => match inner_stmt.as_ref() {
                Statement::Select(_)
                | Statement::Insert(_)
                | Statement::Update(_)
                | Statement::Delete(_) => Ok(Some(vec![ColumnDesc::explain()])),
                _ => Ok(None),
            },
            _ => Ok(None),
        }
    }

    /// Executes a parsed SQL statement.
    ///
    /// This is used by both the Simple Query Protocol (after parsing)
    /// and the Extended Query Protocol (for prepared statements).
    ///
    /// # Returns
    ///
    /// * `Ok(QueryResult)` - Execution result with command tag
    /// * `Err(DatabaseError)` - If execution fails
    pub async fn execute_statement(
        &mut self,
        stmt: &Statement,
    ) -> Result<QueryResult, DatabaseError> {
        match stmt {
            Statement::Begin => {
                self.begin();
                Ok(QueryResult::command("BEGIN"))
            }
            Statement::Commit => {
                self.commit()?;
                Ok(QueryResult::command("COMMIT"))
            }
            Statement::Rollback => {
                self.rollback();
                Ok(QueryResult::command("ROLLBACK"))
            }
            Statement::CreateTable(create_stmt) => {
                self.run_in_transaction(true, |db, txid, cid| async move {
                    db.catalog()
                        .create_table(txid, cid, create_stmt)
                        .await
                        .map_err(DatabaseError::Catalog)?;
                    Ok(QueryResult::command("CREATE TABLE"))
                })
                .await
            }
            Statement::Select(select_stmt) => {
                self.run_in_transaction(false, |db, txid, cid| async move {
                    let snapshot = db.tx_manager().snapshot(txid, cid);
                    let plan = executor::plan_select(select_stmt, db.catalog(), &snapshot).await?;
                    let columns = plan.columns().to_vec();

                    let ctx = db.exec_context(snapshot);
                    let mut node = plan.prepare_for_execute(&ctx);
                    let mut rows = Vec::new();
                    while let Some(row) = node.next().await? {
                        rows.push(row);
                    }
                    Ok(QueryResult::Rows { columns, rows })
                })
                .await
            }
            Statement::Insert(_) | Statement::Update(_) | Statement::Delete(_) => {
                self.run_in_transaction(true, |db, txid, cid| async move {
                    let snapshot = db.tx_manager().snapshot(txid, cid);
                    let plan = match stmt {
                        Statement::Insert(s) => {
                            executor::plan_insert(s, db.catalog(), &snapshot).await?
                        }
                        Statement::Update(s) => {
                            executor::plan_update(s, db.catalog(), &snapshot).await?
                        }
                        Statement::Delete(s) => {
                            executor::plan_delete(s, db.catalog(), &snapshot).await?
                        }
                        _ => unreachable!(),
                    };
                    let ctx = db.exec_context(snapshot);
                    let result = plan.execute_dml(&ctx).await?;
                    Ok(QueryResult::command(result.command_tag()))
                })
                .await
            }
            Statement::DropTable(_) => Ok(QueryResult::command("DROP TABLE")),
            Statement::CreateIndex(_) => Ok(QueryResult::command("CREATE INDEX")),
            Statement::DropIndex(_) => Ok(QueryResult::command("DROP INDEX")),
            Statement::Set(_) => Ok(QueryResult::command("SET")),
            Statement::Explain(inner_stmt) => {
                self.run_in_transaction(false, |db, txid, cid| async move {
                    let snapshot = db.tx_manager().snapshot(txid, cid);
                    let explain_text = match inner_stmt.as_ref() {
                        Statement::Select(select_stmt) => {
                            executor::plan_select(select_stmt, db.catalog(), &snapshot)
                                .await?
                                .explain()
                        }
                        Statement::Insert(insert_stmt) => {
                            executor::plan_insert(insert_stmt, db.catalog(), &snapshot)
                                .await?
                                .explain()
                        }
                        Statement::Update(update_stmt) => {
                            executor::plan_update(update_stmt, db.catalog(), &snapshot)
                                .await?
                                .explain()
                        }
                        Statement::Delete(delete_stmt) => {
                            executor::plan_delete(delete_stmt, db.catalog(), &snapshot)
                                .await?
                                .explain()
                        }
                        _ => {
                            return Err(DatabaseError::Executor(
                                crate::executor::ExecutorError::Unsupported(
                                    "EXPLAIN for this statement type".to_string(),
                                ),
                            ));
                        }
                    };
                    Ok(QueryResult::Rows {
                        columns: vec![ColumnDesc::explain()],
                        rows: explain_text.lines().map(Row::explain_line).collect(),
                    })
                })
                .await
            }
        }
    }

    /// Executes a function within a transaction context.
    ///
    /// This helper handles the common transaction management pattern:
    /// - Increments command ID if in an active transaction
    /// - Creates an auto-commit transaction if not currently in one
    /// - On success in auto-commit mode: commits if `commit_on_auto` is true,
    ///   aborts otherwise (suitable for read-only operations like SELECT/EXPLAIN)
    /// - On error: aborts the transaction if in auto-commit mode, or sets
    ///   the failed flag if in an explicit transaction
    async fn run_in_transaction<T, F, Fut>(
        &mut self,
        commit_on_auto: bool,
        f: F,
    ) -> Result<T, DatabaseError>
    where
        F: FnOnce(Arc<Database<S, R>>, TxId, CommandId) -> Fut,
        Fut: Future<Output = Result<T, DatabaseError>>,
    {
        let (txid, cid, auto_commit) = match &mut self.transaction {
            Some(tx) if !tx.failed => {
                tx.cid = tx.cid.next();
                (tx.txid, tx.cid, false)
            }
            Some(_) => return Err(DatabaseError::TransactionAborted),
            None => (self.database.tx_manager().begin(), CommandId::FIRST, true),
        };

        match f(Arc::clone(&self.database), txid, cid).await {
            Ok(result) => {
                if auto_commit {
                    if commit_on_auto {
                        self.database.tx_manager().commit(txid)?;
                    } else {
                        let _ = self.database.tx_manager().abort(txid);
                    }
                }
                Ok(result)
            }
            Err(e) => {
                if auto_commit {
                    let _ = self.database.tx_manager().abort(txid);
                } else if let Some(tx) = &mut self.transaction {
                    tx.failed = true;
                }
                Err(e)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::MemoryStorage;
    use crate::tx::TxState;

    #[tokio::test]
    async fn test_session_transaction_lifecycle() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        // Initially idle
        assert_eq!(session.transaction, None);
        assert!(session.transaction().is_none());

        // Begin transaction
        session.begin();
        assert!(matches!(
            session.transaction(),
            Some(tx) if !tx.failed
        ));

        // Commit
        session.commit().unwrap();
        assert!(session.transaction().is_none());
    }

    #[tokio::test]
    async fn test_session_rollback() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        session.begin();
        assert!(matches!(
            session.transaction(),
            Some(tx) if !tx.failed
        ));

        session.rollback();
        assert!(session.transaction().is_none());
    }

    #[tokio::test]
    async fn test_session_execute_query_empty() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        let result = session.execute_query("").await.unwrap();
        assert!(result.is_none());
    }

    #[tokio::test]
    async fn test_session_execute_query_create_table() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        let result = session
            .execute_query("CREATE TABLE test (id INT)")
            .await
            .unwrap();

        let Some(QueryResult::Command { tag }) = result else {
            panic!("expected Command result");
        };
        assert_eq!(tag, "CREATE TABLE");

        // Auto-commit should leave us in idle state
        assert!(session.transaction().is_none());
    }

    #[tokio::test]
    async fn test_session_execute_query_in_transaction() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        // Begin transaction
        let result = session.execute_query("BEGIN").await.unwrap();
        let Some(QueryResult::Command { tag }) = result else {
            panic!("expected Command result");
        };
        assert_eq!(tag, "BEGIN");
        assert!(matches!(
            session.transaction(),
            Some(tx) if !tx.failed
        ));

        // Execute DDL in transaction
        session
            .execute_query("CREATE TABLE test (id INT)")
            .await
            .unwrap();
        assert!(matches!(
            session.transaction(),
            Some(tx) if !tx.failed
        ));

        // Commit transaction
        let result = session.execute_query("COMMIT").await.unwrap();
        let Some(QueryResult::Command { tag }) = result else {
            panic!("expected Command result");
        };
        assert_eq!(tag, "COMMIT");
        assert!(session.transaction().is_none());
    }

    #[tokio::test]
    async fn test_session_parse_error() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        let result = session.execute_query("INVALID SQL").await;
        assert!(matches!(result, Err(DatabaseError::Parse(_))));
    }

    #[tokio::test]
    async fn test_select_from_sys_tables() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        let result = session
            .execute_query("SELECT * FROM sys_tables")
            .await
            .unwrap()
            .unwrap();

        let QueryResult::Rows { columns, rows } = result else {
            panic!("expected Rows result");
        };
        assert_eq!(columns.len(), 3);
        assert_eq!(columns[0].name, "table_id");
        assert_eq!(columns[1].name, "table_name");
        assert_eq!(columns[2].name, "first_page");
        // At least sys_tables, sys_columns, sys_sequences
        assert!(rows.len() >= 3);
    }

    #[tokio::test]
    async fn test_select_with_where_filter() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        let result = session
            .execute_query("SELECT table_name FROM sys_tables WHERE table_id = 1")
            .await
            .unwrap()
            .unwrap();

        let QueryResult::Rows { columns, rows } = result else {
            panic!("expected Rows result");
        };
        assert_eq!(columns.len(), 1);
        assert_eq!(columns[0].name, "table_name");
        assert_eq!(rows.len(), 1);
        assert_eq!(
            rows[0].record.values[0],
            crate::datum::Value::Text("sys_tables".to_string())
        );
    }

    #[tokio::test]
    async fn test_select_with_column_list() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        let result = session
            .execute_query("SELECT table_id, table_name FROM sys_tables")
            .await
            .unwrap()
            .unwrap();

        let QueryResult::Rows { columns, rows } = result else {
            panic!("expected Rows result");
        };
        assert_eq!(columns.len(), 2);
        assert_eq!(columns[0].name, "table_id");
        assert_eq!(columns[1].name, "table_name");
        assert!(rows.len() >= 3);
    }

    #[tokio::test]
    async fn test_select_no_from() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        // Arithmetic
        let result = session
            .execute_query("SELECT 2 * 3 + 1")
            .await
            .unwrap()
            .unwrap();
        let QueryResult::Rows { rows, columns } = result else {
            panic!("expected Rows result");
        };
        assert_eq!(columns.len(), 1);
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].record.values[0], crate::datum::Value::Bigint(7));

        // String concatenation
        let result = session
            .execute_query("SELECT 'hello' || ' world'")
            .await
            .unwrap()
            .unwrap();
        let QueryResult::Rows { rows, .. } = result else {
            panic!("expected Rows result");
        };
        assert_eq!(
            rows[0].record.values[0],
            crate::datum::Value::Text("hello world".to_string())
        );
    }

    #[tokio::test]
    async fn test_explain_select() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        let result = session
            .execute_query("EXPLAIN SELECT * FROM sys_tables")
            .await
            .unwrap()
            .unwrap();

        let QueryResult::Rows { columns, rows } = result else {
            panic!("expected Rows result");
        };
        assert_eq!(columns.len(), 1);
        assert_eq!(columns[0].name, "QUERY PLAN");
        assert!(!rows.is_empty());
        // Should contain at least a Projection and SeqScan
        let plan_text: String = rows
            .iter()
            .map(|r| match &r.record.values[0] {
                crate::datum::Value::Text(s) => s.as_str(),
                _ => "",
            })
            .collect::<Vec<_>>()
            .join("\n");
        assert!(plan_text.contains("SeqScan"));
        assert!(plan_text.contains("Projection"));
    }

    #[tokio::test]
    async fn test_describe_explain_select() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        let stmt = Parser::new("EXPLAIN SELECT * FROM sys_tables")
            .parse()
            .unwrap()
            .unwrap();

        let columns = session
            .describe_statement(&stmt)
            .await
            .unwrap()
            .expect("EXPLAIN SELECT should return columns");

        assert_eq!(columns.len(), 1);
        assert_eq!(columns[0].name, "QUERY PLAN");
        assert_eq!(columns[0].ty, crate::datum::Type::Text);
        assert!(columns[0].source.is_none());
    }

    #[tokio::test]
    async fn test_describe_select() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        let stmt = Parser::new("SELECT table_id, table_name FROM sys_tables")
            .parse()
            .unwrap()
            .unwrap();

        let columns = session
            .describe_statement(&stmt)
            .await
            .unwrap()
            .expect("SELECT should return columns");

        assert_eq!(columns.len(), 2);
        assert_eq!(columns[0].name, "table_id");
        assert_eq!(columns[1].name, "table_name");
    }

    #[tokio::test]
    async fn test_describe_non_query() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        let stmt = Parser::new("CREATE TABLE test (id INT)")
            .parse()
            .unwrap()
            .unwrap();

        let result = session.describe_statement(&stmt).await.unwrap();
        assert!(result.is_none(), "DDL should return None");

        let stmt = Parser::new("BEGIN").parse().unwrap().unwrap();
        let result = session.describe_statement(&stmt).await.unwrap();
        assert!(result.is_none(), "Transaction control should return None");
    }

    #[tokio::test]
    async fn test_explicit_transaction_error_sets_failed_flag() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        // Start explicit transaction
        session.execute_query("BEGIN").await.unwrap();
        assert!(matches!(
            session.transaction(),
            Some(tx) if !tx.failed
        ));

        // Cause an error within the transaction
        let result = session.execute_query("SELECT * FROM nonexistent").await;
        assert!(matches!(result, Err(DatabaseError::Executor(_))));

        // Transaction should be marked as failed
        assert!(matches!(
            session.transaction(),
            Some(tx) if tx.failed
        ));

        // Subsequent commands should be rejected with TransactionAborted
        let result = session.execute_query("SELECT 1").await;
        assert!(matches!(result, Err(DatabaseError::TransactionAborted)));

        // ROLLBACK should clear the failed state
        session.execute_query("ROLLBACK").await.unwrap();
        assert!(session.transaction().is_none());

        // After rollback, normal operations should work again
        let result = session.execute_query("SELECT 1").await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_select_table_not_found() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        let result = session.execute_query("SELECT * FROM nonexistent").await;
        assert!(matches!(result, Err(DatabaseError::Executor(_))));
    }

    #[tokio::test]
    async fn test_select_column_not_found() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let mut session = Session::new(db);

        let result = session
            .execute_query("SELECT nonexistent_col FROM sys_tables")
            .await;
        assert!(matches!(result, Err(DatabaseError::Executor(_))));
    }

    #[tokio::test]
    async fn test_drop_rolls_back_active_transaction() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());
        let tx_manager = Arc::clone(db.tx_manager());

        let txid = {
            let mut session = Session::new(db);
            session.begin();
            let txid = session.transaction().unwrap().txid;

            // Transaction should be in-progress before drop
            assert_eq!(tx_manager.state(txid), TxState::InProgress);
            txid
            // session is dropped here
        };

        // After drop, the transaction should be aborted
        assert_eq!(tx_manager.state(txid), TxState::Aborted);
    }

    #[tokio::test]
    async fn test_drop_without_transaction_is_noop() {
        let storage = Arc::new(MemoryStorage::new());
        let db = Arc::new(Database::open(storage, 100).await.unwrap());

        // Session with no transaction — drop should not panic
        let session = Session::new(db);
        drop(session);
    }

    // --- DML integration tests ---

    #[tokio::test]
    async fn test_insert_and_select() {
        let db = Arc::new(Database::open(MemoryStorage::new(), 100).await.unwrap());
        let mut session = Session::new(db);

        session
            .execute_query("CREATE TABLE t (id INTEGER, name TEXT)")
            .await
            .unwrap();

        let result = session
            .execute_query("INSERT INTO t VALUES (1, 'Alice'), (2, 'Bob')")
            .await
            .unwrap()
            .unwrap();
        let QueryResult::Command { tag } = result else {
            panic!("expected Command");
        };
        assert_eq!(tag, "INSERT 0 2");

        let result = session
            .execute_query("SELECT name FROM t WHERE id = 1")
            .await
            .unwrap()
            .unwrap();
        let QueryResult::Rows { rows, .. } = result else {
            panic!("expected Rows");
        };
        assert_eq!(rows.len(), 1);
        assert_eq!(
            rows[0].record.values[0],
            crate::datum::Value::Text("Alice".into())
        );
    }

    #[tokio::test]
    async fn test_update_and_select() {
        let db = Arc::new(Database::open(MemoryStorage::new(), 100).await.unwrap());
        let mut session = Session::new(db);

        session
            .execute_query("CREATE TABLE t (id INTEGER, name TEXT)")
            .await
            .unwrap();
        session
            .execute_query("INSERT INTO t VALUES (1, 'Alice'), (2, 'Bob')")
            .await
            .unwrap();

        let result = session
            .execute_query("UPDATE t SET name = 'Updated' WHERE id = 1")
            .await
            .unwrap()
            .unwrap();
        let QueryResult::Command { tag } = result else {
            panic!("expected Command");
        };
        assert_eq!(tag, "UPDATE 1");

        let result = session
            .execute_query("SELECT name FROM t WHERE id = 1")
            .await
            .unwrap()
            .unwrap();
        let QueryResult::Rows { rows, .. } = result else {
            panic!("expected Rows");
        };
        assert_eq!(rows.len(), 1);
        assert_eq!(
            rows[0].record.values[0],
            crate::datum::Value::Text("Updated".into())
        );
    }

    #[tokio::test]
    async fn test_delete_and_select() {
        let db = Arc::new(Database::open(MemoryStorage::new(), 100).await.unwrap());
        let mut session = Session::new(db);

        session
            .execute_query("CREATE TABLE t (id INTEGER, name TEXT)")
            .await
            .unwrap();
        session
            .execute_query("INSERT INTO t VALUES (1, 'Alice'), (2, 'Bob'), (3, 'Carol')")
            .await
            .unwrap();

        let result = session
            .execute_query("DELETE FROM t WHERE id = 2")
            .await
            .unwrap()
            .unwrap();
        let QueryResult::Command { tag } = result else {
            panic!("expected Command");
        };
        assert_eq!(tag, "DELETE 1");

        let result = session
            .execute_query("SELECT * FROM t")
            .await
            .unwrap()
            .unwrap();
        let QueryResult::Rows { rows, .. } = result else {
            panic!("expected Rows");
        };
        assert_eq!(rows.len(), 2);
    }

    #[tokio::test]
    async fn test_serial_auto_increment() {
        let db = Arc::new(Database::open(MemoryStorage::new(), 100).await.unwrap());
        let mut session = Session::new(db);

        session
            .execute_query("CREATE TABLE t (id SERIAL, name TEXT)")
            .await
            .unwrap();
        session
            .execute_query("INSERT INTO t (name) VALUES ('Alice'), ('Bob')")
            .await
            .unwrap();

        let result = session
            .execute_query("SELECT id, name FROM t")
            .await
            .unwrap()
            .unwrap();
        let QueryResult::Rows { rows, .. } = result else {
            panic!("expected Rows");
        };
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0].record.values[0], crate::datum::Value::Integer(1));
        assert_eq!(rows[1].record.values[0], crate::datum::Value::Integer(2));
    }

    #[tokio::test]
    async fn test_transaction_dml_sequence() {
        let db = Arc::new(Database::open(MemoryStorage::new(), 100).await.unwrap());
        let mut session = Session::new(db);

        session
            .execute_query("CREATE TABLE t (id INTEGER, val TEXT)")
            .await
            .unwrap();

        // Multi-statement transaction
        session.execute_query("BEGIN").await.unwrap();
        session
            .execute_query("INSERT INTO t VALUES (1, 'a'), (2, 'b'), (3, 'c')")
            .await
            .unwrap();
        session
            .execute_query("UPDATE t SET val = 'x' WHERE id = 2")
            .await
            .unwrap();
        session
            .execute_query("DELETE FROM t WHERE id = 3")
            .await
            .unwrap();

        let result = session
            .execute_query("SELECT val FROM t")
            .await
            .unwrap()
            .unwrap();
        let QueryResult::Rows { rows, .. } = result else {
            panic!("expected Rows");
        };
        assert_eq!(rows.len(), 2);
        let vals: Vec<&crate::datum::Value> = rows.iter().map(|r| &r.record.values[0]).collect();
        assert!(vals.contains(&&crate::datum::Value::Text("a".into())));
        assert!(vals.contains(&&crate::datum::Value::Text("x".into())));

        session.execute_query("COMMIT").await.unwrap();
    }

    #[tokio::test]
    async fn test_explain_insert() {
        let db = Arc::new(Database::open(MemoryStorage::new(), 100).await.unwrap());
        let mut session = Session::new(db);

        session
            .execute_query("CREATE TABLE t (id INTEGER, name TEXT)")
            .await
            .unwrap();

        let result = session
            .execute_query("EXPLAIN INSERT INTO t VALUES (1, 'Alice'), (2, 'Bob')")
            .await
            .unwrap()
            .unwrap();
        let QueryResult::Rows { rows, .. } = result else {
            panic!("expected Rows");
        };
        let plan_text = match &rows[0].record.values[0] {
            crate::datum::Value::Text(s) => s.clone(),
            v => panic!("expected Text, got {:?}", v),
        };
        assert!(plan_text.contains("Insert on t"));
    }

    #[tokio::test]
    async fn test_dml_auto_commit() {
        let db = Arc::new(Database::open(MemoryStorage::new(), 100).await.unwrap());
        let mut session = Session::new(db);

        session
            .execute_query("CREATE TABLE t (id INTEGER)")
            .await
            .unwrap();

        // INSERT without explicit transaction → auto-commit
        session
            .execute_query("INSERT INTO t VALUES (1)")
            .await
            .unwrap();
        assert!(session.transaction().is_none()); // Should be idle

        // Data should be visible in a new auto-commit SELECT
        let result = session
            .execute_query("SELECT * FROM t")
            .await
            .unwrap()
            .unwrap();
        let QueryResult::Rows { rows, .. } = result else {
            panic!("expected Rows");
        };
        assert_eq!(rows.len(), 1);
    }

    #[tokio::test]
    async fn test_failed_dml_sets_failed_flag() {
        let db = Arc::new(Database::open(MemoryStorage::new(), 100).await.unwrap());
        let mut session = Session::new(db);

        session.execute_query("BEGIN").await.unwrap();

        // INSERT into non-existent table
        let result = session
            .execute_query("INSERT INTO nonexistent VALUES (1)")
            .await;
        assert!(result.is_err());

        // Transaction should be in failed state
        assert!(matches!(
            session.transaction(),
            Some(tx) if tx.failed
        ));

        session.execute_query("ROLLBACK").await.unwrap();
    }
}
