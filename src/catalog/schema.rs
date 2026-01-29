//! Hardcoded catalog table schemas and type mappings.
//!
//! This module defines the schema for system catalog tables and provides
//! mappings between SQL data types and PostgreSQL type OIDs.

use crate::protocol::type_oid;
use crate::sql::DataType;

/// Reserved table IDs for system catalog tables.
pub mod table_id {
    /// sys_tables table ID.
    pub const SYS_TABLES: u32 = 1;
    /// sys_columns table ID.
    pub const SYS_COLUMNS: u32 = 2;
    /// sys_sequences table ID.
    pub const SYS_SEQUENCES: u32 = 3;
    /// First available ID for user tables.
    pub const FIRST_USER_TABLE: u32 = 100;
}

/// Schema for sys_tables catalog table.
///
/// Columns:
/// - table_id: INT4 (primary key)
/// - table_name: TEXT (unique)
/// - first_page: INT8 (PageId of first heap page)
pub const SYS_TABLES_SCHEMA: [i32; 3] = [type_oid::INT4, type_oid::TEXT, type_oid::INT8];

/// Column indices for sys_tables.
pub mod sys_tables {
    /// table_id column index.
    pub const TABLE_ID: usize = 0;
    /// table_name column index.
    pub const TABLE_NAME: usize = 1;
    /// first_page column index.
    pub const FIRST_PAGE: usize = 2;
}

/// Schema for sys_columns catalog table.
///
/// Columns:
/// - table_id: INT4 (FK to sys_tables)
/// - column_num: INT4 (0-based position)
/// - column_name: TEXT
/// - type_oid: INT4 (PostgreSQL type OID)
/// - seq_id: INT4 (FK to sys_sequences, or 0 if not SERIAL)
pub const SYS_COLUMNS_SCHEMA: [i32; 5] = [
    type_oid::INT4,
    type_oid::INT4,
    type_oid::TEXT,
    type_oid::INT4,
    type_oid::INT4,
];

/// Column indices for sys_columns.
pub mod sys_columns {
    /// table_id column index.
    pub const TABLE_ID: usize = 0;
    /// column_num column index.
    pub const COLUMN_NUM: usize = 1;
    /// column_name column index.
    pub const COLUMN_NAME: usize = 2;
    /// type_oid column index.
    pub const TYPE_OID: usize = 3;
    /// seq_id column index (0 = not a SERIAL column).
    pub const SEQ_ID: usize = 4;
}

/// Schema for sys_sequences catalog table.
///
/// Columns:
/// - seq_id: INT4 (primary key)
/// - seq_name: TEXT
/// - next_val: INT8
pub const SYS_SEQUENCES_SCHEMA: [i32; 3] = [type_oid::INT4, type_oid::TEXT, type_oid::INT8];

/// Column indices for sys_sequences.
pub mod sys_sequences {
    /// seq_id column index.
    pub const SEQ_ID: usize = 0;
    /// seq_name column index.
    pub const SEQ_NAME: usize = 1;
    /// next_val column index.
    pub const NEXT_VAL: usize = 2;
}

/// Converts a SQL `DataType` to a PostgreSQL type OID.
///
/// SERIAL columns are stored as INT4 with a linked sequence.
pub fn data_type_to_oid(data_type: &DataType) -> i32 {
    match data_type {
        DataType::Boolean => type_oid::BOOL,
        DataType::Smallint => type_oid::INT2,
        DataType::Integer => type_oid::INT4,
        DataType::Bigint => type_oid::INT8,
        DataType::Real => type_oid::FLOAT4,
        DataType::DoublePrecision => type_oid::FLOAT8,
        DataType::Text => type_oid::TEXT,
        DataType::Varchar(_) => type_oid::VARCHAR,
        DataType::Bytea => type_oid::BYTEA,
        // SERIAL is stored as INT4 internally; sequence handles auto-increment
        DataType::Serial => type_oid::INT4,
    }
}

/// Returns true if the data type is SERIAL (auto-increment).
pub fn is_serial(data_type: &DataType) -> bool {
    matches!(data_type, DataType::Serial)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_data_type_to_oid() {
        assert_eq!(data_type_to_oid(&DataType::Boolean), type_oid::BOOL);
        assert_eq!(data_type_to_oid(&DataType::Smallint), type_oid::INT2);
        assert_eq!(data_type_to_oid(&DataType::Integer), type_oid::INT4);
        assert_eq!(data_type_to_oid(&DataType::Bigint), type_oid::INT8);
        assert_eq!(data_type_to_oid(&DataType::Real), type_oid::FLOAT4);
        assert_eq!(data_type_to_oid(&DataType::DoublePrecision), type_oid::FLOAT8);
        assert_eq!(data_type_to_oid(&DataType::Text), type_oid::TEXT);
        assert_eq!(data_type_to_oid(&DataType::Varchar(Some(255))), type_oid::VARCHAR);
        assert_eq!(data_type_to_oid(&DataType::Bytea), type_oid::BYTEA);
        // SERIAL is stored as INT4
        assert_eq!(data_type_to_oid(&DataType::Serial), type_oid::INT4);
    }

    #[test]
    fn test_is_serial() {
        assert!(is_serial(&DataType::Serial));
        assert!(!is_serial(&DataType::Integer));
        assert!(!is_serial(&DataType::Text));
    }

    #[test]
    fn test_schema_lengths() {
        assert_eq!(SYS_TABLES_SCHEMA.len(), 3);
        assert_eq!(SYS_COLUMNS_SCHEMA.len(), 5);
        assert_eq!(SYS_SEQUENCES_SCHEMA.len(), 3);
    }
}
