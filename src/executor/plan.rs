//! Logical query plan representation.
//!
//! A [`Plan`] describes *what* to execute without loading any data.
//! It is produced by the planner and then converted into an
//! [`ExecutorNode`](super::node::ExecutorNode) by [`Plan::prepare_for_execute`].

use crate::datum::Type;
use crate::storage::PageId;

use super::ColumnDesc;
use super::expr::BoundExpr;

/// A logical query plan node.
///
/// Unlike [`ExecutorNode`](super::node::ExecutorNode), a `Plan` contains no
/// pre-loaded data — only the metadata needed to describe the scan, filter,
/// and projection operations.
pub enum Plan {
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
        input: Box<Plan>,
        /// Bound predicate expression.
        predicate: BoundExpr,
    },
    /// Column projection (SELECT list).
    Projection {
        /// Child plan to pull tuples from.
        input: Box<Plan>,
        /// Bound expressions to evaluate for each output column.
        exprs: Vec<BoundExpr>,
        /// Output column descriptors.
        columns: Vec<ColumnDesc>,
    },
    /// Single-row scan for queries without FROM (e.g., `SELECT 1+1`).
    ValuesScan,
}

impl Plan {
    /// Returns the output column descriptors for this plan node.
    pub fn columns(&self) -> &[ColumnDesc] {
        match self {
            Plan::SeqScan { columns, .. } => columns,
            Plan::Filter { input, .. } => input.columns(),
            Plan::Projection { columns, .. } => columns,
            Plan::ValuesScan => &[],
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
            Plan::SeqScan {
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
            Plan::Filter { input, predicate } => {
                let child_str = input.format_explain(indent + 1);
                format!("{}Filter: {}\n{}", prefix, predicate, child_str)
            }
            Plan::Projection { input, exprs, .. } => {
                let cols: Vec<String> = exprs.iter().map(|e| e.to_string()).collect();
                let child_str = input.format_explain(indent + 1);
                format!("{}Projection: {}\n{}", prefix, cols.join(", "), child_str)
            }
            Plan::ValuesScan => {
                format!("{}ValuesScan (1 row)", prefix)
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
        let plan = Plan::SeqScan {
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
        let scan = Plan::SeqScan {
            table_name: "users".to_string(),
            table_id: 1,
            first_page: PageId::new(10),
            schema: vec![Type::Bigint],
            columns: vec![int_col("id")],
        };
        let plan = Plan::Filter {
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
        let scan = Plan::SeqScan {
            table_name: "users".to_string(),
            table_id: 1,
            first_page: PageId::new(10),
            schema: vec![Type::Bigint, Type::Text],
            columns: vec![int_col("id"), int_col("name")],
        };
        let plan = Plan::Projection {
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
        assert_eq!(Plan::ValuesScan.explain(), "ValuesScan (1 row)");
    }
}
