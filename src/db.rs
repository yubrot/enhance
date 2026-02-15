//! Database orchestrator for managing buffer pool, transaction manager, and catalog.
//!
//! The [`Database`] type is the main entry point for database infrastructure.
//! It initializes or opens an existing database and provides access to
//! the core components (buffer pool, transaction manager, catalog).
//!
//! # Architecture
//!
//! ```text
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

pub use database::Database;
pub use error::DatabaseError;

/// Test helpers for database-layer tests used across multiple test modules.
#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::sql::tests::parse_create_table;
    use crate::storage::{LruReplacer, MemoryStorage};
    use crate::tx::CommandId;

    /// Type alias for a test database backed by in-memory storage.
    pub type TestDb = Database<MemoryStorage, LruReplacer>;

    /// Opens a test database with in-memory storage and 100-frame buffer pool.
    pub async fn open_test_db() -> TestDb {
        Database::open(MemoryStorage::new(), 100).await.unwrap()
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
}
