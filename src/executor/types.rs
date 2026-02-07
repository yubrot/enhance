//! Core types for the query executor.

use crate::datum::{Type, Value};

/// Metadata describing a result column.
#[derive(Debug, Clone)]
pub struct ColumnDesc {
    /// Column name (or alias).
    pub name: String,
    /// OID of the source table (0 if not from a table).
    pub table_oid: i32,
    /// Column attribute number within the source table (0 if not from a table).
    pub column_id: i16,
    /// Data type.
    pub data_type: Type,
}

/// A single result row as a vector of values.
pub type Row = Vec<Value>;
