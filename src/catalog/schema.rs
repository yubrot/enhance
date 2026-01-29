//! System catalog schema definitions.
//!
//! This module defines the schema for system catalog tables (sys_tables,
//! sys_columns, sys_sequences) including their table IDs, column layouts,
//! and conversion logic between heap records and typed structs.

use crate::heap::{Record, Value};
use crate::protocol::type_oid;
use crate::storage::PageId;

/// Last table ID reserved for system catalog tables.
/// User tables start from `LAST_RESERVED_TABLE_ID + 1`.
pub const LAST_RESERVED_TABLE_ID: u32 = 99;

/// Metadata for a table stored in the catalog (sys_tables row).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TableInfo {
    /// Unique table identifier.
    pub table_id: u32,
    /// Table name.
    pub table_name: String,
    /// Page ID of the first heap page for this table.
    pub first_page: PageId,
}

impl TableInfo {
    /// Table ID for sys_tables itself.
    pub const TABLE_ID: u32 = 1;

    /// Schema for sys_tables catalog table (type OIDs for deserialization).
    pub const SCHEMA: [i32; 3] = [type_oid::INT4, type_oid::TEXT, type_oid::INT8];

    // Column indices
    const COL_TABLE_ID: usize = 0;
    const COL_TABLE_NAME: usize = 1;
    const COL_FIRST_PAGE: usize = 2;

    /// Creates a new TableInfo.
    pub fn new(table_id: u32, table_name: String, first_page: PageId) -> Self {
        Self {
            table_id,
            table_name,
            first_page,
        }
    }

    /// Converts a record from sys_tables into TableInfo.
    ///
    /// Returns `None` if the record has invalid or unexpected value types.
    pub fn from_record(record: &Record) -> Option<Self> {
        let table_id = match record.values.get(Self::COL_TABLE_ID)? {
            Value::Int32(id) => *id as u32,
            _ => return None,
        };
        let table_name = match record.values.get(Self::COL_TABLE_NAME)? {
            Value::Text(s) => s.clone(),
            _ => return None,
        };
        let first_page = match record.values.get(Self::COL_FIRST_PAGE)? {
            Value::Int64(p) => PageId::new(*p as u64),
            _ => return None,
        };
        Some(Self::new(table_id, table_name, first_page))
    }

    /// Converts this TableInfo into a record for sys_tables.
    pub fn to_record(&self) -> Record {
        Record::new(vec![
            Value::Int32(self.table_id as i32),
            Value::Text(self.table_name.clone()),
            Value::Int64(self.first_page.page_num() as i64),
        ])
    }
}

/// Metadata for a column stored in the catalog (sys_columns row).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ColumnInfo {
    /// Table this column belongs to.
    pub table_id: u32,
    /// 0-based column position.
    pub column_num: u32,
    /// Column name.
    pub column_name: String,
    /// Type OID (using PostgreSQL's OID values for psql compatibility).
    pub type_oid: i32,
    /// Linked sequence ID for SERIAL columns (0 if not SERIAL).
    pub seq_id: u32,
}

impl ColumnInfo {
    /// Table ID for sys_columns.
    pub const TABLE_ID: u32 = 2;

    /// Schema for sys_columns catalog table (type OIDs for deserialization).
    pub const SCHEMA: [i32; 5] = [
        type_oid::INT4,
        type_oid::INT4,
        type_oid::TEXT,
        type_oid::INT4,
        type_oid::INT4,
    ];

    // Column indices
    const COL_TABLE_ID: usize = 0;
    const COL_COLUMN_NUM: usize = 1;
    const COL_COLUMN_NAME: usize = 2;
    const COL_TYPE_OID: usize = 3;
    const COL_SEQ_ID: usize = 4;

    /// Creates a new ColumnInfo.
    pub fn new(
        table_id: u32,
        column_num: u32,
        column_name: String,
        type_oid: i32,
        seq_id: u32,
    ) -> Self {
        Self {
            table_id,
            column_num,
            column_name,
            type_oid,
            seq_id,
        }
    }

    /// Converts a record from sys_columns into ColumnInfo.
    ///
    /// Returns `None` if the record has invalid or unexpected value types.
    pub fn from_record(record: &Record) -> Option<Self> {
        let table_id = match record.values.get(Self::COL_TABLE_ID)? {
            Value::Int32(id) => *id as u32,
            _ => return None,
        };
        let column_num = match record.values.get(Self::COL_COLUMN_NUM)? {
            Value::Int32(n) => *n as u32,
            _ => return None,
        };
        let column_name = match record.values.get(Self::COL_COLUMN_NAME)? {
            Value::Text(s) => s.clone(),
            _ => return None,
        };
        let type_oid = match record.values.get(Self::COL_TYPE_OID)? {
            Value::Int32(oid) => *oid,
            _ => return None,
        };
        let seq_id = match record.values.get(Self::COL_SEQ_ID)? {
            Value::Int32(id) => *id as u32,
            _ => return None,
        };
        Some(Self::new(
            table_id,
            column_num,
            column_name,
            type_oid,
            seq_id,
        ))
    }

    /// Converts this ColumnInfo into a record for sys_columns.
    pub fn to_record(&self) -> Record {
        Record::new(vec![
            Value::Int32(self.table_id as i32),
            Value::Int32(self.column_num as i32),
            Value::Text(self.column_name.clone()),
            Value::Int32(self.type_oid),
            Value::Int32(self.seq_id as i32),
        ])
    }

    /// Returns true if this column is a SERIAL (auto-increment) column.
    pub fn is_serial(&self) -> bool {
        self.seq_id != 0
    }
}

/// Metadata for a sequence stored in the catalog (sys_sequences row).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SequenceInfo {
    /// Unique sequence identifier.
    pub seq_id: u32,
    /// Sequence name.
    pub seq_name: String,
    /// Next value to return.
    pub next_val: i64,
}

impl SequenceInfo {
    /// Table ID for sys_sequences.
    pub const TABLE_ID: u32 = 3;

    /// Schema for sys_sequences catalog table (type OIDs for deserialization).
    pub const SCHEMA: [i32; 3] = [type_oid::INT4, type_oid::TEXT, type_oid::INT8];

    // Column indices
    const COL_SEQ_ID: usize = 0;
    const COL_SEQ_NAME: usize = 1;
    const COL_NEXT_VAL: usize = 2;

    /// Creates a new SequenceInfo.
    pub fn new(seq_id: u32, seq_name: String, next_val: i64) -> Self {
        Self {
            seq_id,
            seq_name,
            next_val,
        }
    }

    /// Converts a record from sys_sequences into SequenceInfo.
    ///
    /// Returns `None` if the record has invalid or unexpected value types.
    pub fn from_record(record: &Record) -> Option<Self> {
        let seq_id = match record.values.get(Self::COL_SEQ_ID)? {
            Value::Int32(id) => *id as u32,
            _ => return None,
        };
        let seq_name = match record.values.get(Self::COL_SEQ_NAME)? {
            Value::Text(s) => s.clone(),
            _ => return None,
        };
        let next_val = match record.values.get(Self::COL_NEXT_VAL)? {
            Value::Int64(v) => *v,
            _ => return None,
        };
        Some(Self::new(seq_id, seq_name, next_val))
    }

    /// Converts this SequenceInfo into a record for sys_sequences.
    pub fn to_record(&self) -> Record {
        Record::new(vec![
            Value::Int32(self.seq_id as i32),
            Value::Text(self.seq_name.clone()),
            Value::Int64(self.next_val),
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_table_info() {
        let info = TableInfo::new(1, "users".to_string(), PageId::new(10));
        assert_eq!(info.table_id, 1);
        assert_eq!(info.table_name, "users");
        assert_eq!(info.first_page, PageId::new(10));
    }

    #[test]
    fn test_column_info() {
        let col = ColumnInfo::new(1, 0, "id".to_string(), 23, 5);
        assert_eq!(col.table_id, 1);
        assert_eq!(col.column_num, 0);
        assert_eq!(col.column_name, "id");
        assert_eq!(col.type_oid, 23);
        assert_eq!(col.seq_id, 5);
        assert!(col.is_serial());

        let col2 = ColumnInfo::new(1, 1, "name".to_string(), 25, 0);
        assert!(!col2.is_serial());
    }

    #[test]
    fn test_sequence_info() {
        let seq = SequenceInfo::new(1, "users_id_seq".to_string(), 100);
        assert_eq!(seq.seq_id, 1);
        assert_eq!(seq.seq_name, "users_id_seq");
        assert_eq!(seq.next_val, 100);
    }
}
