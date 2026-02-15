//! Engine orchestrator for managing buffer pool, transaction manager, and catalog.
//!
//! The [`Engine`] type is the main entry point for database infrastructure.
//! It initializes or opens an existing database and provides access to
//! the core components (buffer pool, transaction manager, catalog operations).
//!
//! # Architecture
//!
//! ```text
//! +------------------------------------------------------------------+
//! |                          Engine                                  |
//! |  (Orchestrates core infrastructure components)                   |
//! |                                                                  |
//! |  +-----------------+  +--------------------+  +---------------+  |
//! |  | Arc<BufferPool> |  | Arc<TxManager>     |  | Superblock    |  |
//! |  | (Page I/O,      |  | (TxId allocation,  |  | (Table/column |  |
//! |  |  LRU eviction)  |  |  commit/abort)     |  |  page IDs)    |  |
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

mod core;
mod error;
mod exec_context;
mod superblock;

pub use core::Engine;
pub use error::EngineError;
pub use exec_context::ExecContextImpl;
pub use superblock::Superblock;

/// Test helpers for engine-layer tests used across multiple test modules.
#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::sql::tests::parse_create_table;
    use crate::storage::{LruReplacer, MemoryStorage};
    use crate::tx::CommandId;

    /// Type alias for a test engine backed by in-memory storage.
    pub type TestEngine = Engine<MemoryStorage, LruReplacer>;

    /// Opens a test engine with in-memory storage and 100-frame buffer pool.
    pub async fn open_test_engine() -> TestEngine {
        Engine::open(MemoryStorage::new(), 100).await.unwrap()
    }

    impl TestEngine {
        /// Creates a table using the given DDL and commits it in its own transaction.
        ///
        /// Parses the DDL string as a `CREATE TABLE` statement, executes it within
        /// a new transaction, and commits immediately.
        pub async fn create_test_table(&self, ddl: &str) {
            let txid = self.tx_manager().begin();
            let stmt = parse_create_table(ddl);
            self.create_table(txid, CommandId::FIRST, &stmt)
                .await
                .unwrap();
            self.register_ddl(txid);
            self.tx_manager().commit(txid).unwrap();
        }
    }
}
