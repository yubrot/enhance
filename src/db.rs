//! Database orchestrator for managing buffer pool, transaction manager, and catalog.
//!
//! The [`Database`] type is the main entry point for database operations.
//! It initializes or opens an existing database and provides access to
//! the core components.

mod database;
mod error;

pub use database::Database;
pub use error::DatabaseError;
