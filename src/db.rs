//! Database orchestrator for managing buffer pool, transaction manager, and catalog.
//!
//! The [`Database`] type is the main entry point for database operations.
//! It initializes or opens an existing database and provides access to
//! the core components.
//!
//! # Example
//!
//! ```no_run
//! use enhance::db::Database;
//! use enhance::storage::{FileStorage, LruReplacer};
//!
//! # async fn example() -> Result<(), Box<dyn std::error::Error>> {
//! // Open or create a database
//! let storage = FileStorage::open("enhance.db").await?;
//! let db = Database::<_, LruReplacer>::open(storage, 1000).await?;
//!
//! // Use the database components
//! let txid = db.tx_manager().begin();
//! // ... perform operations ...
//! db.tx_manager().commit(txid)?;
//!
//! // Flush changes to disk
//! db.flush().await?;
//! # Ok(())
//! # }
//! ```

mod database;
mod error;

pub use database::Database;
pub use error::DatabaseError;
