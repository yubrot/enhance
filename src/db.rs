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
//! |  | Arc<BufferPool> |  | Arc<TxManager>     |  |    Catalog    |  |
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

// Re-export executor types used in QueryResult
pub use crate::executor::{ColumnDesc, Row};
