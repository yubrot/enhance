//! EXPLAIN output formatting for logical plans.
//!
//! Formats a [`Plan`] tree as a human-readable query plan string,
//! resolving column indices back to names for readability.

use super::eval::format_bound_expr_with_columns;
use super::plan::Plan;

/// Formats a [`Plan`] as a human-readable EXPLAIN string.
///
/// Column indices in bound expressions are resolved back to their
/// human-readable names using the parent plan node's column schema.
///
/// # Example output
///
/// ```text
/// Projection: table_id, table_name
///   Filter: (table_id > 1)
///     SeqScan on sys_tables
/// ```
pub fn explain_plan(plan: &Plan) -> String {
    format_plan(plan, 0)
}

/// Recursively formats a plan node with indentation.
fn format_plan(plan: &Plan, indent: usize) -> String {
    let prefix = "  ".repeat(indent);
    match plan {
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
            let input_columns = input.columns();
            let filter_str = format_bound_expr_with_columns(predicate, input_columns);
            let child_str = format_plan(input, indent + 1);
            format!("{}Filter: {}\n{}", prefix, filter_str, child_str)
        }
        Plan::Projection {
            input,
            exprs,
            ..
        } => {
            let input_columns = input.columns();
            let cols: Vec<String> = exprs
                .iter()
                .map(|e| format_bound_expr_with_columns(e, input_columns))
                .collect();
            let child_str = format_plan(input, indent + 1);
            format!("{}Projection: {}\n{}", prefix, cols.join(", "), child_str)
        }
        Plan::ValuesScan => {
            format!("{}ValuesScan (1 row)", prefix)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::eval::BoundExpr;
    use crate::executor::types::ColumnDesc;
    use crate::datum::Type;
    use crate::sql::BinaryOperator;
    use crate::storage::PageId;

    fn int_col(name: &str) -> ColumnDesc {
        ColumnDesc {
            name: name.to_string(),
            table_oid: 0,
            column_id: 0,
            data_type: Type::Int8,
        }
    }

    #[test]
    fn test_explain_seq_scan() {
        let plan = Plan::SeqScan {
            table_name: "users".to_string(),
            table_id: 1,
            first_page: PageId::new(10),
            schema: vec![Type::Int8, Type::Text],
            columns: vec![int_col("id"), int_col("name")],
        };
        let output = explain_plan(&plan);
        assert!(output.contains("SeqScan on users"));
        assert!(output.contains("id, name"));
    }

    #[test]
    fn test_explain_filter() {
        let scan = Plan::SeqScan {
            table_name: "users".to_string(),
            table_id: 1,
            first_page: PageId::new(10),
            schema: vec![Type::Int8],
            columns: vec![int_col("id")],
        };
        let plan = Plan::Filter {
            input: Box::new(scan),
            predicate: BoundExpr::BinaryOp {
                left: Box::new(BoundExpr::Column(0)),
                op: BinaryOperator::Gt,
                right: Box::new(BoundExpr::Integer(5)),
            },
        };
        let output = explain_plan(&plan);
        assert!(output.contains("Filter: (id > 5)"));
        assert!(output.contains("SeqScan on users"));
    }

    #[test]
    fn test_explain_projection() {
        let scan = Plan::SeqScan {
            table_name: "users".to_string(),
            table_id: 1,
            first_page: PageId::new(10),
            schema: vec![Type::Int8, Type::Text],
            columns: vec![int_col("id"), int_col("name")],
        };
        let plan = Plan::Projection {
            input: Box::new(scan),
            exprs: vec![BoundExpr::Column(1)],
            columns: vec![int_col("name")],
        };
        let output = explain_plan(&plan);
        assert!(output.contains("Projection: name"));
        assert!(output.contains("SeqScan on users"));
    }

    #[test]
    fn test_explain_values_scan() {
        let plan = Plan::ValuesScan;
        let output = explain_plan(&plan);
        assert!(output.contains("ValuesScan (1 row)"));
    }
}
