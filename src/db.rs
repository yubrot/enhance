//! Database orchestrator for managing buffer pool, transaction manager, and catalog.
//!
//! The [`Database`] type is the main entry point for database operations.
//! It initializes or opens an existing database and provides access to
//! the core components.
//!
//! The [`Session`] type provides a client session abstraction that manages
//! transaction state and SQL execution.
//!
//! # Architecture
//!
//! ```text
//!                    +---------------------+
//!                    |     Connection      |  <- server module (Protocol layer)
//!                    | (PostgreSQL wire)   |
//!                    +----------+----------+
//!                               | owns
//!                               v
//!                    +---------------------+
//!                    |       Session       |  <- db module (Business layer)
//!                    | (Tx lifecycle, SQL) |
//!                    +----------+----------+
//!                               | Arc<Database>
//!                               v
//! +------------------------------------------------------------------+
//! |                         Database                                 |
//! |  (Orchestrates core infrastructure components)                   |
//! |                                                                  |
//! |  +-----------------+  +--------------------+  +---------------+  |
//! |  | Arc<BufferPool> |  | Arc<TxManager>     |  | CatalogStore |  |
//! |  | (Page I/O,      |  | (TxId allocation,  |  | (Table/column |  |
//! |  |  LRU eviction)  |  |  commit/abort)     |  |  metadata)    |  |
//! |  +--------+--------+  +--------------------+  +-------+-------+  |
//! |           |                                           |          |
//! +-----------+-------------------------------------------+----------+
//!             |                                           |
//!             v                                           | uses
//!       +---------------------+                           |
//!       |  storage::Storage   |<--------------------------+
//!       | (Memory / File)     |
//!       +---------------------+
//! ```

mod database;
mod error;
mod session;

pub use database::Database;
pub use error::DatabaseError;
pub use session::{QueryResult, Session, TransactionState};

/// Test helpers for database-layer tests used across multiple test modules.
#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::executor::{ColumnDesc, Row};
    use crate::sql::tests::parse_create_table;
    use crate::storage::{LruReplacer, MemoryStorage};
    use crate::tx::CommandId;
    use std::sync::Arc;

    /// Type alias for a test database backed by in-memory storage.
    pub type TestDb = Database<MemoryStorage, LruReplacer>;

    /// Type alias for a test session backed by in-memory storage.
    pub type TestSession = Session<MemoryStorage, LruReplacer>;

    /// Opens a test database with in-memory storage and 100-frame buffer pool.
    pub async fn open_test_db() -> TestDb {
        Database::open(MemoryStorage::new(), 100).await.unwrap()
    }

    /// Opens a test database and creates a [`Session`] connected to it.
    pub async fn open_test_session() -> TestSession {
        let db = Arc::new(open_test_db().await);
        Session::new(db)
    }

    impl TestDb {
        /// Creates a table using the given DDL and commits it in its own transaction.
        ///
        /// Parses the DDL string as a `CREATE TABLE` statement, executes it within
        /// a new transaction, and commits immediately.
        pub async fn create_table(&self, ddl: &str) {
            let txid = self.tx_manager().begin();
            let stmt = parse_create_table(ddl);
            self.catalog_store()
                .create_table(txid, CommandId::FIRST, &stmt)
                .await
                .unwrap();
            self.tx_manager().commit(txid).unwrap();
        }
    }

    impl TestSession {
        /// Executes a query and extracts the `Rows` result.
        ///
        /// Panics if the query fails, returns no result, or returns a `Command`.
        pub async fn query_rows(&mut self, sql: &str) -> (Vec<ColumnDesc>, Vec<Row>) {
            let result = self.execute_query(sql).await.unwrap().unwrap();
            let QueryResult::Rows { columns, rows } = result else {
                panic!("expected Rows result from: {sql}");
            };
            (columns, rows)
        }

        /// Executes a statement and extracts the command tag.
        ///
        /// Panics if the query fails, returns no result, or returns `Rows`.
        pub async fn execute_command(&mut self, sql: &str) -> String {
            let result = self.execute_query(sql).await.unwrap().unwrap();
            let QueryResult::Command { tag } = result else {
                panic!("expected Command result from: {sql}");
            };
            tag
        }
    }
}
