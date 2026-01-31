//! EXPLAIN output formatting.
//!
//! Converts a query execution plan into a human-readable string format
//! similar to PostgreSQL's EXPLAIN output.

use super::expr::BoundExpr;
use super::plan::Plan;
use crate::sql::{BinaryOperator, DataType, UnaryOperator};

/// Formats a plan as a human-readable EXPLAIN string.
///
/// The output format is similar to PostgreSQL's EXPLAIN:
/// ```text
/// Projection (cols: id, name)
///   Filter (predicate: id > 5)
///     SeqScan on users
/// ```
pub fn explain_plan(plan: &Plan) -> String {
    let mut output = String::new();
    format_plan(plan, 0, &mut output);
    output
}

fn format_plan(plan: &Plan, indent: usize, output: &mut String) {
    let prefix = "  ".repeat(indent);

    match plan {
        Plan::SeqScan {
            table_name,
            output_columns,
            ..
        } => {
            output.push_str(&format!("{}SeqScan on {}", prefix, table_name));
            if !output_columns.is_empty() {
                let col_names: Vec<&str> = output_columns.iter().map(|c| c.name.as_str()).collect();
                output.push_str(&format!(" (cols: {})", col_names.join(", ")));
            }
            output.push('\n');
        }

        Plan::Filter { input, predicate } => {
            output.push_str(&format!("{}Filter ({})\n", prefix, format_expr(predicate)));
            format_plan(input, indent + 1, output);
        }

        Plan::Projection {
            input,
            exprs,
            output_columns,
        } => {
            let col_names: Vec<&str> = output_columns.iter().map(|c| c.name.as_str()).collect();
            output.push_str(&format!("{}Projection ({})\n", prefix, col_names.join(", ")));

            // Show expression details if they're not just column references
            if exprs.iter().any(|e| !matches!(e, BoundExpr::Column(_))) {
                for (i, expr) in exprs.iter().enumerate() {
                    output.push_str(&format!(
                        "{}  {}: {}\n",
                        prefix,
                        output_columns.get(i).map(|c| c.name.as_str()).unwrap_or("?"),
                        format_expr(expr)
                    ));
                }
            }

            format_plan(input, indent + 1, output);
        }
    }
}

fn format_expr(expr: &BoundExpr) -> String {
    match expr {
        BoundExpr::Null => "NULL".to_string(),
        BoundExpr::Boolean(b) => if *b { "true" } else { "false" }.to_string(),
        BoundExpr::Integer(n) => n.to_string(),
        BoundExpr::Float(f) => f.to_string(),
        BoundExpr::String(s) => format!("'{}'", s.replace('\'', "''")),
        BoundExpr::Column(idx) => format!("$col{}", idx),

        BoundExpr::BinaryOp { left, op, right } => {
            format!(
                "({} {} {})",
                format_expr(left),
                format_binary_op(op),
                format_expr(right)
            )
        }

        BoundExpr::UnaryOp { op, operand } => {
            format!("({}{})", format_unary_op(op), format_expr(operand))
        }

        BoundExpr::IsNull { expr, negated } => {
            let suffix = if *negated { " IS NOT NULL" } else { " IS NULL" };
            format!("({}{})", format_expr(expr), suffix)
        }

        BoundExpr::Cast { expr, target_type } => {
            format!("({}::{})", format_expr(expr), format_data_type(target_type))
        }
    }
}

fn format_binary_op(op: &BinaryOperator) -> &'static str {
    op.as_str()
}

fn format_unary_op(op: &UnaryOperator) -> &'static str {
    match op {
        UnaryOperator::Not => "NOT ",
        UnaryOperator::Minus => "-",
        UnaryOperator::Plus => "+",
    }
}

fn format_data_type(dt: &DataType) -> String {
    dt.display_name()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::plan::ColumnDesc;
    use crate::protocol::type_oid;
    use crate::storage::PageId;

    #[test]
    fn test_explain_seqscan() {
        let plan = Plan::SeqScan {
            table_name: "users".to_string(),
            table_id: 100,
            first_page: PageId::new(1),
            schema: vec![type_oid::INT4, type_oid::TEXT],
            output_columns: vec![
                ColumnDesc::new("id", type_oid::INT4),
                ColumnDesc::new("name", type_oid::TEXT),
            ],
        };

        let output = explain_plan(&plan);
        assert!(output.contains("SeqScan on users"));
        assert!(output.contains("cols: id, name"));
    }

    #[test]
    fn test_explain_filter() {
        let plan = Plan::Filter {
            input: Box::new(Plan::SeqScan {
                table_name: "users".to_string(),
                table_id: 100,
                first_page: PageId::new(1),
                schema: vec![type_oid::INT4],
                output_columns: vec![ColumnDesc::new("id", type_oid::INT4)],
            }),
            predicate: BoundExpr::BinaryOp {
                left: Box::new(BoundExpr::Column(0)),
                op: BinaryOperator::Gt,
                right: Box::new(BoundExpr::Integer(5)),
            },
        };

        let output = explain_plan(&plan);
        assert!(output.contains("Filter"));
        assert!(output.contains("$col0 > 5"));
        assert!(output.contains("SeqScan on users"));
    }

    #[test]
    fn test_explain_projection() {
        let plan = Plan::Projection {
            input: Box::new(Plan::SeqScan {
                table_name: "users".to_string(),
                table_id: 100,
                first_page: PageId::new(1),
                schema: vec![type_oid::INT4, type_oid::TEXT],
                output_columns: vec![
                    ColumnDesc::new("id", type_oid::INT4),
                    ColumnDesc::new("name", type_oid::TEXT),
                ],
            }),
            exprs: vec![BoundExpr::Column(1)],
            output_columns: vec![ColumnDesc::new("name", type_oid::TEXT)],
        };

        let output = explain_plan(&plan);
        assert!(output.contains("Projection (name)"));
        assert!(output.contains("SeqScan on users"));
    }

    #[test]
    fn test_explain_complex_plan() {
        // Projection -> Filter -> SeqScan
        let plan = Plan::Projection {
            input: Box::new(Plan::Filter {
                input: Box::new(Plan::SeqScan {
                    table_name: "orders".to_string(),
                    table_id: 101,
                    first_page: PageId::new(2),
                    schema: vec![type_oid::INT4, type_oid::INT4, type_oid::TEXT],
                    output_columns: vec![
                        ColumnDesc::new("id", type_oid::INT4),
                        ColumnDesc::new("amount", type_oid::INT4),
                        ColumnDesc::new("status", type_oid::TEXT),
                    ],
                }),
                predicate: BoundExpr::BinaryOp {
                    left: Box::new(BoundExpr::Column(1)),
                    op: BinaryOperator::GtEq,
                    right: Box::new(BoundExpr::Integer(100)),
                },
            }),
            exprs: vec![BoundExpr::Column(0), BoundExpr::Column(2)],
            output_columns: vec![
                ColumnDesc::new("id", type_oid::INT4),
                ColumnDesc::new("status", type_oid::TEXT),
            ],
        };

        let output = explain_plan(&plan);
        let lines: Vec<&str> = output.lines().collect();

        // Verify structure: Projection at top, Filter in middle, SeqScan at bottom
        assert!(lines[0].contains("Projection"));
        assert!(lines.iter().any(|l| l.contains("Filter")));
        assert!(lines.iter().any(|l| l.contains("SeqScan on orders")));
    }

    #[test]
    fn test_format_expr_is_null() {
        let expr = BoundExpr::IsNull {
            expr: Box::new(BoundExpr::Column(0)),
            negated: false,
        };
        assert_eq!(format_expr(&expr), "($col0 IS NULL)");

        let expr = BoundExpr::IsNull {
            expr: Box::new(BoundExpr::Column(0)),
            negated: true,
        };
        assert_eq!(format_expr(&expr), "($col0 IS NOT NULL)");
    }

    #[test]
    fn test_format_expr_cast() {
        let expr = BoundExpr::Cast {
            expr: Box::new(BoundExpr::Integer(42)),
            target_type: DataType::Text,
        };
        assert_eq!(format_expr(&expr), "(42::TEXT)");
    }
}
