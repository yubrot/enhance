//! System catalog for table and column metadata.
//!
//! This module manages metadata about tables, columns, and sequences
//! in self-hosted heap tables with MVCC support.
//!
//! # Architecture
//!
//! ```text
//! Page 0          Heap Pages
//! +------------+  +-------------+  +---------------+  +----------------+
//! | Superblock |  | sys_tables  |  | sys_columns   |  | sys_sequences  |
//! +------------+  +-------------+  +---------------+  +----------------+
//!       |               |                 |                   |
//!       |               v                 v                   v
//!       |         [ TableInfo ]    [ ColumnInfo ]     [ SequenceInfo ]
//!       |
//!       +-> Catalog Page IDs + ID Generators
//! ```
//!
//! ## Catalog Tables
//!
//! | Table Name      | Rust Type        | Description                     |
//! |-----------------|------------------|---------------------------------|
//! | `sys_tables`    | [`TableInfo`]    | Table metadata (id, name, page) |
//! | `sys_columns`   | [`ColumnInfo`]   | Column metadata per table       |
//! | `sys_sequences` | [`SequenceInfo`] | SERIAL column sequences         |
//!
//! ## Components
//!
//! - [`CatalogStore`]: Low-level catalog operations (create table, heap lookups)
//! - [`Superblock`]: Database metadata stored in page 0 (page IDs, ID generators)
//! - [`TableInfo`], [`ColumnInfo`], [`SequenceInfo`]: Typed wrappers for catalog rows
//!
//! ## Bootstrap
//!
//! On first startup, the catalog is bootstrapped by:
//! 1. Allocating page 0 as the superblock
//! 2. Creating heap pages for sys_tables, sys_columns, sys_sequences
//! 3. Inserting self-describing metadata for the catalog tables
//!
//! ## Usage
//!
//! The catalog is accessed through the [`Database`](crate::db::Database) type,
//! which orchestrates the buffer pool, transaction manager, and catalog.

mod cache;
mod error;
mod schema;
mod snapshot;
mod store;
mod superblock;

pub use cache::CatalogCache;
pub use error::CatalogError;
pub use schema::{ColumnInfo, LAST_RESERVED_TABLE_ID, SequenceInfo, SystemCatalogTable, TableInfo};
pub use snapshot::{CatalogSnapshot, TableEntry};
pub use store::CatalogStore;
pub use superblock::Superblock;

/// Test helpers for catalog-layer tests used across multiple test modules.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::tests::test_pool;
    use crate::storage::{LruReplacer, MemoryStorage};
    use crate::tx::TransactionManager;
    use std::sync::Arc;

    /// Bootstraps a [`CatalogStore`] backed by in-memory storage for testing.
    ///
    /// Returns the store and a shared [`TransactionManager`].
    pub async fn test_catalog_store() -> (
        CatalogStore<MemoryStorage, LruReplacer>,
        Arc<TransactionManager>,
    ) {
        let pool = test_pool();
        let tx_manager = Arc::new(TransactionManager::new());
        let store = CatalogStore::bootstrap(pool, tx_manager.clone())
            .await
            .unwrap();
        (store, tx_manager)
    }
}
