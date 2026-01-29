//! System catalog for table and column metadata.
//!
//! The catalog stores metadata about tables, columns, and sequences in
//! self-hosted heap tables with MVCC support.
//!
//! ## Catalog Tables
//!
//! - `sys_tables`: Table metadata (table_id, table_name, first_page)
//! - `sys_columns`: Column metadata (table_id, column_num, column_name, type_oid, seq_id)
//! - `sys_sequences`: Sequence metadata for SERIAL columns (seq_id, seq_name, next_val)
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
mod core;
mod error;
mod schema;
mod superblock;
mod types;

pub use self::core::Catalog;
pub use error::CatalogError;
pub use schema::{
    data_type_to_oid, is_serial, table_id, sys_columns, sys_sequences, sys_tables,
    SYS_COLUMNS_SCHEMA, SYS_SEQUENCES_SCHEMA, SYS_TABLES_SCHEMA,
};
pub use superblock::{Superblock, SUPERBLOCK_MAGIC, SUPERBLOCK_SIZE, SUPERBLOCK_VERSION};
pub use types::{ColumnInfo, SequenceInfo, TableInfo};
