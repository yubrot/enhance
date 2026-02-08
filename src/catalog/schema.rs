//! System catalog schema definitions.
//!
//! This module defines the schema for system catalog tables (sys_tables,
//! sys_columns, sys_sequences) including their table IDs, column layouts,
//! and conversion logic between heap records and typed structs.

use crate::datum::{Type, Value};
use crate::heap::Record;
use crate::storage::PageId;

/// Last table ID reserved for system catalog tables.
/// User tables start from `LAST_RESERVED_TABLE_ID + 1`.
pub const LAST_RESERVED_TABLE_ID: u32 = 99;

/// Common interface for system catalog tables.
///
/// Each system catalog table (sys_tables, sys_columns, sys_sequences) implements
/// this trait to provide consistent access to metadata and schema information.
///
/// Implementations only need to define the constants; `table_info()` and
/// `columns()` have default implementations that use these constants.
pub trait SystemCatalogTable {
    /// The table ID reserved for this system catalog table.
    const TABLE_ID: u32;

    /// The table name for this system catalog table.
    const TABLE_NAME: &'static str;

    /// The column names for this system catalog table.
    const COLUMN_NAMES: &'static [&'static str];

    /// The schema (data types) for this system catalog table.
    const SCHEMA: &'static [Type];

    /// Returns the TableInfo for this system catalog table.
    ///
    /// Used during bootstrap to insert the table's own metadata.
    fn table_info(page: PageId) -> TableInfo {
        TableInfo::new(Self::TABLE_ID, Self::TABLE_NAME.to_string(), page)
    }

    /// Returns the column definitions for this system catalog table.
    ///
    /// Each tuple is (column_name, data_type), automatically paired from
    /// COLUMN_NAMES and SCHEMA to guarantee consistency.
    fn columns() -> impl IntoIterator<Item = (&'static str, Type)> {
        Self::COLUMN_NAMES
            .iter()
            .copied()
            .zip(Self::SCHEMA.iter().copied())
    }
}

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
            Value::Integer(id) => *id as u32,
            _ => return None,
        };
        let table_name = match record.values.get(Self::COL_TABLE_NAME)? {
            Value::Text(s) => s.clone(),
            _ => return None,
        };
        let first_page = match record.values.get(Self::COL_FIRST_PAGE)? {
            Value::Bigint(p) => PageId::new(*p as u64),
            _ => return None,
        };
        Some(Self::new(table_id, table_name, first_page))
    }

    /// Converts this TableInfo into a record for sys_tables.
    pub fn to_record(&self) -> Record {
        Record::new(vec![
            Value::Integer(self.table_id as i32),
            Value::Text(self.table_name.clone()),
            Value::Bigint(self.first_page.page_num() as i64),
        ])
    }
}

impl SystemCatalogTable for TableInfo {
    const TABLE_ID: u32 = 1;
    const TABLE_NAME: &'static str = "sys_tables";
    const COLUMN_NAMES: &'static [&'static str] = &["table_id", "table_name", "first_page"];
    const SCHEMA: &'static [Type] = &[Type::Integer, Type::Text, Type::Bigint];
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
    /// Data type.
    pub data_type: Type,
    /// Linked sequence ID for SERIAL columns (0 if not SERIAL).
    pub seq_id: u32,
}

impl ColumnInfo {
    const COL_TABLE_ID: usize = 0;
    const COL_COLUMN_NUM: usize = 1;
    const COL_COLUMN_NAME: usize = 2;
    const COL_DATA_TYPE: usize = 3;
    const COL_SEQ_ID: usize = 4;

    /// Creates a new ColumnInfo.
    pub fn new(
        table_id: u32,
        column_num: u32,
        column_name: String,
        data_type: Type,
        seq_id: u32,
    ) -> Self {
        Self {
            table_id,
            column_num,
            column_name,
            data_type,
            seq_id,
        }
    }

    /// Converts a record from sys_columns into ColumnInfo.
    ///
    /// Returns `None` if the record has invalid or unexpected value types.
    pub fn from_record(record: &Record) -> Option<Self> {
        let table_id = match record.values.get(Self::COL_TABLE_ID)? {
            Value::Integer(id) => *id as u32,
            _ => return None,
        };
        let column_num = match record.values.get(Self::COL_COLUMN_NUM)? {
            Value::Integer(n) => *n as u32,
            _ => return None,
        };
        let column_name = match record.values.get(Self::COL_COLUMN_NAME)? {
            Value::Text(s) => s.clone(),
            _ => return None,
        };
        let data_type = match record.values.get(Self::COL_DATA_TYPE)? {
            Value::Integer(oid) => Type::from_oid(*oid)?,
            _ => return None,
        };
        let seq_id = match record.values.get(Self::COL_SEQ_ID)? {
            Value::Integer(id) => *id as u32,
            _ => return None,
        };
        Some(Self::new(
            table_id,
            column_num,
            column_name,
            data_type,
            seq_id,
        ))
    }

    /// Converts this ColumnInfo into a record for sys_columns.
    pub fn to_record(&self) -> Record {
        Record::new(vec![
            Value::Integer(self.table_id as i32),
            Value::Integer(self.column_num as i32),
            Value::Text(self.column_name.clone()),
            Value::Integer(self.data_type.oid()),
            Value::Integer(self.seq_id as i32),
        ])
    }

    /// Returns true if this column is a SERIAL (auto-increment) column.
    pub fn is_serial(&self) -> bool {
        self.seq_id != 0
    }
}

impl SystemCatalogTable for ColumnInfo {
    const TABLE_ID: u32 = 2;
    const TABLE_NAME: &'static str = "sys_columns";
    const COLUMN_NAMES: &'static [&'static str] = &[
        "table_id",
        "column_num",
        "column_name",
        "type_oid",
        "seq_id",
    ];
    const SCHEMA: &'static [Type] = &[
        Type::Integer,
        Type::Integer,
        Type::Text,
        Type::Integer,
        Type::Integer,
    ];
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
            Value::Integer(id) => *id as u32,
            _ => return None,
        };
        let seq_name = match record.values.get(Self::COL_SEQ_NAME)? {
            Value::Text(s) => s.clone(),
            _ => return None,
        };
        let next_val = match record.values.get(Self::COL_NEXT_VAL)? {
            Value::Bigint(v) => *v,
            _ => return None,
        };
        Some(Self::new(seq_id, seq_name, next_val))
    }

    /// Converts this SequenceInfo into a record for sys_sequences.
    pub fn to_record(&self) -> Record {
        Record::new(vec![
            Value::Integer(self.seq_id as i32),
            Value::Text(self.seq_name.clone()),
            Value::Bigint(self.next_val),
        ])
    }
}

impl SystemCatalogTable for SequenceInfo {
    const TABLE_ID: u32 = 3;
    const TABLE_NAME: &'static str = "sys_sequences";
    const COLUMN_NAMES: &'static [&'static str] = &["seq_id", "seq_name", "next_val"];
    const SCHEMA: &'static [Type] = &[Type::Integer, Type::Text, Type::Bigint];
}
