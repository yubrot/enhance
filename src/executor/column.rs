use crate::datum::Type;

/// Source table metadata for columns originating from a table scan.
#[derive(Debug, Clone)]
pub struct ColumnSource {
    /// Source table name (for qualified column resolution).
    pub table_name: String,
    /// OID of the source table.
    pub table_oid: u32,
    /// Column attribute number within the source table (1-indexed).
    pub column_id: i16,
}

/// Metadata describing a result column.
#[derive(Debug, Clone)]
pub struct ColumnDesc {
    /// Column name (or alias).
    pub name: String,
    /// Source table info. `None` for computed/expression columns.
    pub source: Option<ColumnSource>,
    /// Data type.
    pub data_type: Type,
}

impl ColumnDesc {
    pub fn explain() -> Self {
        Self {
            name: "QUERY PLAN".to_string(),
            source: None,
            data_type: Type::Text,
        }
    }

    /// Returns the display name for this column.
    ///
    /// If the column has a source table, returns `table.column`,
    /// otherwise returns just the column name.
    pub fn display_name(&self) -> String {
        match &self.source {
            Some(s) => format!("{}.{}", s.table_name, self.name),
            None => self.name.clone(),
        }
    }
}
