//! Logical query plan representation.
//!
//! Plans describe *what* to execute without loading any data:
//!
//! - [`QueryPlan`] — row-producing plans (SELECT, scan sub-plans) converted
//!   into [`QueryNode`](super::runner::QueryNode) via
//!   [`QueryPlan::prepare_for_execute`].
//! - [`DmlPlan`] — data-modifying plans (INSERT/UPDATE/DELETE) executed via
//!   [`DmlPlan::execute_dml`].

use crate::datum::Type;
use crate::storage::PageId;

use super::ColumnDesc;
use super::expr::BoundExpr;

/// A row-producing logical query plan node.
///
/// Unlike [`QueryNode`](super::runner::QueryNode), a `QueryPlan` contains
/// no pre-loaded data — only the metadata needed to describe the scan, filter,
/// and projection operations.
pub enum QueryPlan {
    /// Sequential heap scan targeting a single table.
    SeqScan {
        /// Table name (for EXPLAIN output).
        table_name: String,
        /// Catalog table ID.
        table_id: u32,
        /// First heap page to scan.
        first_page: PageId,
        /// Column data types for record deserialization.
        schema: Vec<Type>,
        /// Output column descriptors.
        columns: Vec<ColumnDesc>,
    },
    /// Tuple filter (WHERE clause).
    Filter {
        /// Child plan to pull tuples from.
        input: Box<QueryPlan>,
        /// Bound predicate expression.
        predicate: BoundExpr,
    },
    /// Column projection (SELECT list).
    Projection {
        /// Child plan to pull tuples from.
        input: Box<QueryPlan>,
        /// Bound expressions to evaluate for each output column.
        exprs: Vec<BoundExpr>,
        /// Output column descriptors.
        columns: Vec<ColumnDesc>,
    },
    /// Single-row scan for queries without FROM (e.g., `SELECT 1+1`).
    ValuesScan,
}

/// A data-modifying logical plan node (INSERT, UPDATE, DELETE).
pub enum DmlPlan {
    /// INSERT into a table.
    Insert {
        /// Table name (for EXPLAIN output and command tags).
        table_name: String,
        /// Catalog table ID.
        table_id: u32,
        /// First heap page of the table.
        first_page: PageId,
        /// Column data types in table-schema order.
        schema: Vec<Type>,
        /// Bound value expressions for each row, in table-schema order.
        /// Each inner Vec has exactly `schema.len()` elements.
        values: Vec<Vec<BoundExpr>>,
        /// SERIAL columns to auto-populate with nextval (column index, seq_id).
        /// Only includes SERIAL columns NOT explicitly provided in the INSERT column list.
        serial_columns: Vec<(usize, u32)>,
    },
    /// UPDATE on a table.
    Update {
        /// Table name (for EXPLAIN output and command tags).
        table_name: String,
        /// Input plan that scans the rows to update (SeqScan + optional Filter).
        input: Box<QueryPlan>,
        /// Bound SET expressions in table-schema order (one per column).
        /// Columns not in the SET clause contain `BoundExpr::Column { index }` to
        /// preserve the original value.
        assignments: Vec<BoundExpr>,
        /// Column data types in table-schema order.
        schema: Vec<Type>,
        /// First heap page of the table.
        first_page: PageId,
    },
    /// DELETE from a table.
    Delete {
        /// Table name (for EXPLAIN output and command tags).
        table_name: String,
        /// Input plan that scans the rows to delete (SeqScan + optional Filter).
        input: Box<QueryPlan>,
    },
}

impl QueryPlan {
    /// Returns the output column descriptors for this plan node.
    pub fn columns(&self) -> &[ColumnDesc] {
        match self {
            QueryPlan::SeqScan { columns, .. } => columns,
            QueryPlan::Filter { input, .. } => input.columns(),
            QueryPlan::Projection { columns, .. } => columns,
            QueryPlan::ValuesScan => &[],
        }
    }

    /// Formats this plan as a human-readable EXPLAIN string.
    ///
    /// Column indices in bound expressions are resolved back to their
    /// human-readable names using the parent plan node's column schema.
    ///
    /// # Example output
    ///
    /// ```text
    /// Projection: $col0 (table_id), $col1 (table_name)
    ///   Filter: ($col0 (table_id) > 1)
    ///     SeqScan on sys_tables (cols: table_id, table_name, first_page)
    /// ```
    pub fn explain(&self) -> String {
        self.format_explain(0)
    }

    /// Recursively formats a plan node with indentation.
    fn format_explain(&self, indent: usize) -> String {
        let prefix = "  ".repeat(indent);
        match self {
            QueryPlan::SeqScan {
                table_name,
                columns,
                ..
            } => {
                let col_names: Vec<&str> = columns.iter().map(|c| c.name.as_str()).collect();
                format!(
                    "{}SeqScan on {} (cols: {})",
                    prefix,
                    table_name,
                    col_names.join(", ")
                )
            }
            QueryPlan::Filter { input, predicate } => {
                let child_str = input.format_explain(indent + 1);
                format!("{}Filter: {}\n{}", prefix, predicate, child_str)
            }
            QueryPlan::Projection { input, exprs, .. } => {
                let cols: Vec<String> = exprs.iter().map(|e| e.to_string()).collect();
                let child_str = input.format_explain(indent + 1);
                format!("{}Projection: {}\n{}", prefix, cols.join(", "), child_str)
            }
            QueryPlan::ValuesScan => {
                format!("{}ValuesScan (1 row)", prefix)
            }
        }
    }
}

impl DmlPlan {
    /// Formats this plan as a human-readable EXPLAIN string.
    pub fn explain(&self) -> String {
        self.format_explain(0)
    }

    /// Recursively formats a DML plan node with indentation.
    fn format_explain(&self, indent: usize) -> String {
        let prefix = "  ".repeat(indent);
        match self {
            DmlPlan::Insert {
                table_name, values, ..
            } => {
                let row_count = values.len();
                format!(
                    "{}Insert on {} ({} row{})",
                    prefix,
                    table_name,
                    row_count,
                    if row_count == 1 { "" } else { "s" }
                )
            }
            DmlPlan::Update {
                table_name, input, ..
            } => {
                let child_str = input.format_explain(indent + 1);
                format!("{}Update on {}\n{}", prefix, table_name, child_str)
            }
            DmlPlan::Delete {
                table_name, input, ..
            } => {
                let child_str = input.format_explain(indent + 1);
                format!("{}Delete on {}\n{}", prefix, table_name, child_str)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::datum::Type;
    use crate::sql::Parser;
    use crate::storage::PageId;

    fn int_col(name: &str) -> ColumnDesc {
        ColumnDesc {
            name: name.to_string(),
            source: None,
            ty: Type::Bigint,
        }
    }

    /// Parses and binds a SQL expression against the given column descriptors.
    fn bind_expr(sql: &str, columns: &[ColumnDesc]) -> BoundExpr {
        Parser::new(sql)
            .parse_expr()
            .expect("parse error")
            .bind(columns)
            .expect("bind error")
    }

    #[test]
    fn test_explain_seq_scan() {
        let plan = QueryPlan::SeqScan {
            table_name: "users".to_string(),
            table_id: 1,
            first_page: PageId::new(10),
            schema: vec![Type::Bigint, Type::Text],
            columns: vec![int_col("id"), int_col("name")],
        };
        assert_eq!(plan.explain(), "SeqScan on users (cols: id, name)");
    }

    #[test]
    fn test_explain_filter() {
        let scan = QueryPlan::SeqScan {
            table_name: "users".to_string(),
            table_id: 1,
            first_page: PageId::new(10),
            schema: vec![Type::Bigint],
            columns: vec![int_col("id")],
        };
        let plan = QueryPlan::Filter {
            input: Box::new(scan),
            predicate: bind_expr("id > 5", &[int_col("id")]),
        };
        assert_eq!(
            plan.explain(),
            "Filter: ($col0 (id) > 5)\n  SeqScan on users (cols: id)"
        );
    }

    #[test]
    fn test_explain_projection() {
        let scan = QueryPlan::SeqScan {
            table_name: "users".to_string(),
            table_id: 1,
            first_page: PageId::new(10),
            schema: vec![Type::Bigint, Type::Text],
            columns: vec![int_col("id"), int_col("name")],
        };
        let plan = QueryPlan::Projection {
            input: Box::new(scan),
            exprs: vec![bind_expr("name", &[int_col("id"), int_col("name")])],
            columns: vec![int_col("name")],
        };
        assert_eq!(
            plan.explain(),
            "Projection: $col1 (name)\n  SeqScan on users (cols: id, name)"
        );
    }

    #[test]
    fn test_explain_values_scan() {
        assert_eq!(QueryPlan::ValuesScan.explain(), "ValuesScan (1 row)");
    }
}
