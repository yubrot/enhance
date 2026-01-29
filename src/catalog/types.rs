//! Catalog data types for table and column metadata.

use crate::storage::PageId;

/// Metadata for a table stored in the catalog.
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
    /// Creates a new TableInfo.
    pub fn new(table_id: u32, table_name: String, first_page: PageId) -> Self {
        Self {
            table_id,
            table_name,
            first_page,
        }
    }
}

/// Metadata for a column stored in the catalog.
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

    /// Returns true if this column is a SERIAL (auto-increment) column.
    pub fn is_serial(&self) -> bool {
        self.seq_id != 0
    }
}

/// Metadata for a sequence stored in the catalog.
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
    /// Creates a new SequenceInfo.
    pub fn new(seq_id: u32, seq_name: String, next_val: i64) -> Self {
        Self {
            seq_id,
            seq_name,
            next_val,
        }
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
