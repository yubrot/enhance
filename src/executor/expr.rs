//! Bound expression tree with compile-time column resolution.
//!
//! [`BoundExpr`] is the executor's internal representation of SQL expressions.
//! Unlike the AST [`Expr`](crate::sql::Expr), column references are resolved
//! to positional indices at bind time, enabling O(1) access during evaluation.

use std::fmt;

use crate::datum::Type;
use crate::sql::{BinaryOperator, Expr, UnaryOperator};

use super::ColumnDesc;
use super::error::ExecutorError;

/// An expression tree with column references resolved to positional indices.
///
/// Unlike the AST [`Expr`](crate::sql::Expr), `BoundExpr` replaces
/// `ColumnRef { table, column }` with `Column { index, name }`, enabling O(1) column
/// access during evaluation instead of O(n) name matching on every row.
#[derive(Debug, Clone)]
pub enum BoundExpr {
    /// NULL literal.
    Null,
    /// Boolean literal.
    Boolean(bool),
    /// Integer literal.
    Integer(i64),
    /// Float literal.
    Float(f64),
    /// String literal.
    String(String),
    /// Column reference resolved to a positional index.
    Column {
        /// Positional index into the record.
        index: usize,
        /// Optional resolved column name for display purposes.
        name: Option<String>,
    },
    /// Binary operation.
    BinaryOp {
        left: Box<BoundExpr>,
        op: BinaryOperator,
        right: Box<BoundExpr>,
    },
    /// Unary operation.
    UnaryOp {
        op: UnaryOperator,
        operand: Box<BoundExpr>,
    },
    /// IS [NOT] NULL test.
    IsNull { expr: Box<BoundExpr>, negated: bool },
    /// IN list test.
    InList {
        expr: Box<BoundExpr>,
        list: Vec<BoundExpr>,
        negated: bool,
    },
    /// BETWEEN range test.
    Between {
        expr: Box<BoundExpr>,
        low: Box<BoundExpr>,
        high: Box<BoundExpr>,
        negated: bool,
    },
    /// LIKE / ILIKE pattern matching.
    Like {
        expr: Box<BoundExpr>,
        pattern: Box<BoundExpr>,
        escape: Option<Box<BoundExpr>>,
        negated: bool,
        case_insensitive: bool,
    },
    /// CASE expression (searched or simple).
    Case {
        operand: Option<Box<BoundExpr>>,
        when_clauses: Vec<BoundWhenClause>,
        else_result: Option<Box<BoundExpr>>,
    },
    /// CAST expression.
    Cast {
        expr: Box<BoundExpr>,
        data_type: Type,
    },
}

/// A WHEN clause in a bound CASE expression.
#[derive(Debug, Clone)]
pub struct BoundWhenClause {
    /// Condition (searched CASE) or comparison value (simple CASE).
    pub condition: BoundExpr,
    /// Result expression when the condition matches.
    pub result: BoundExpr,
}

impl BoundExpr {
    /// Converts an AST [`Expr`] into a [`BoundExpr`] by resolving column names
    /// to positional indices via the provided column descriptors.
    ///
    /// Unsupported AST variants (Parameter, Function, Subquery, InSubquery, Exists)
    /// return [`ExecutorError::Unsupported`].
    pub fn bind(expr: &Expr, columns: &[ColumnDesc]) -> Result<BoundExpr, ExecutorError> {
        match expr {
            Expr::Null => Ok(BoundExpr::Null),
            Expr::Boolean(b) => Ok(BoundExpr::Boolean(*b)),
            Expr::Integer(n) => Ok(BoundExpr::Integer(*n)),
            Expr::Float(f) => Ok(BoundExpr::Float(*f)),
            Expr::String(s) => Ok(BoundExpr::String(s.clone())),

            Expr::ColumnRef { table, column } => {
                let idx = resolve_column_index(table.as_deref(), column, columns)?;
                let name = Some(columns[idx].display_name());
                Ok(BoundExpr::Column { index: idx, name })
            }

            Expr::BinaryOp { left, op, right } => Ok(BoundExpr::BinaryOp {
                left: Box::new(BoundExpr::bind(left, columns)?),
                op: *op,
                right: Box::new(BoundExpr::bind(right, columns)?),
            }),

            Expr::UnaryOp { op, operand } => Ok(BoundExpr::UnaryOp {
                op: *op,
                operand: Box::new(BoundExpr::bind(operand, columns)?),
            }),

            Expr::IsNull { expr, negated } => Ok(BoundExpr::IsNull {
                expr: Box::new(BoundExpr::bind(expr, columns)?),
                negated: *negated,
            }),

            Expr::InList {
                expr,
                list,
                negated,
            } => {
                let bound_list = list
                    .iter()
                    .map(|e| BoundExpr::bind(e, columns))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(BoundExpr::InList {
                    expr: Box::new(BoundExpr::bind(expr, columns)?),
                    list: bound_list,
                    negated: *negated,
                })
            }

            Expr::Between {
                expr,
                low,
                high,
                negated,
            } => Ok(BoundExpr::Between {
                expr: Box::new(BoundExpr::bind(expr, columns)?),
                low: Box::new(BoundExpr::bind(low, columns)?),
                high: Box::new(BoundExpr::bind(high, columns)?),
                negated: *negated,
            }),

            Expr::Like {
                expr,
                pattern,
                escape,
                negated,
                case_insensitive,
            } => {
                let bound_escape = match escape {
                    Some(e) => Some(Box::new(BoundExpr::bind(e, columns)?)),
                    None => None,
                };
                Ok(BoundExpr::Like {
                    expr: Box::new(BoundExpr::bind(expr, columns)?),
                    pattern: Box::new(BoundExpr::bind(pattern, columns)?),
                    escape: bound_escape,
                    negated: *negated,
                    case_insensitive: *case_insensitive,
                })
            }

            Expr::Case {
                operand,
                when_clauses,
                else_result,
            } => {
                let bound_operand = match operand {
                    Some(op) => Some(Box::new(BoundExpr::bind(op, columns)?)),
                    None => None,
                };
                let bound_whens = when_clauses
                    .iter()
                    .map(|wc| {
                        Ok(BoundWhenClause {
                            condition: BoundExpr::bind(&wc.condition, columns)?,
                            result: BoundExpr::bind(&wc.result, columns)?,
                        })
                    })
                    .collect::<Result<Vec<_>, ExecutorError>>()?;
                let bound_else = match else_result {
                    Some(e) => Some(Box::new(BoundExpr::bind(e, columns)?)),
                    None => None,
                };
                Ok(BoundExpr::Case {
                    operand: bound_operand,
                    when_clauses: bound_whens,
                    else_result: bound_else,
                })
            }

            Expr::Cast { expr, data_type } => Ok(BoundExpr::Cast {
                expr: Box::new(BoundExpr::bind(expr, columns)?),
                data_type: data_type.to_type(),
            }),

            Expr::Parameter(_) => Err(ExecutorError::Unsupported(
                "parameter placeholders are not yet supported".to_string(),
            )),

            Expr::Function { .. } => Err(ExecutorError::Unsupported(
                "function calls are not yet supported".to_string(),
            )),

            Expr::InSubquery { .. } | Expr::Exists { .. } | Expr::Subquery(_) => Err(
                ExecutorError::Unsupported("subqueries are not yet supported".to_string()),
            ),
        }
    }
}

impl fmt::Display for BoundExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BoundExpr::Null => write!(f, "NULL"),
            BoundExpr::Boolean(b) => write!(f, "{}", b),
            BoundExpr::Integer(n) => write!(f, "{}", n),
            BoundExpr::Float(n) => write!(f, "{}", n),
            BoundExpr::String(s) => write!(f, "'{}'", s),
            BoundExpr::Column { index, name } => match name {
                Some(n) => write!(f, "$col{} ({})", index, n),
                None => write!(f, "$col{}", index),
            },
            BoundExpr::BinaryOp { left, op, right } => {
                write!(f, "({} {} {})", left, op.as_str(), right)
            }
            BoundExpr::UnaryOp { op, operand } => match op {
                UnaryOperator::Not => write!(f, "(NOT {})", operand),
                _ => write!(f, "({}{})", op.as_str(), operand),
            },
            BoundExpr::IsNull { expr, negated } => {
                if *negated {
                    write!(f, "({} IS NOT NULL)", expr)
                } else {
                    write!(f, "({} IS NULL)", expr)
                }
            }
            BoundExpr::InList {
                expr,
                list,
                negated,
            } => {
                let items: Vec<String> = list.iter().map(|e| e.to_string()).collect();
                let neg = if *negated { " NOT" } else { "" };
                write!(f, "({}{} IN ({}))", expr, neg, items.join(", "))
            }
            BoundExpr::Between {
                expr,
                low,
                high,
                negated,
            } => {
                let neg = if *negated { " NOT" } else { "" };
                write!(f, "({}{} BETWEEN {} AND {})", expr, neg, low, high)
            }
            BoundExpr::Like {
                expr,
                pattern,
                negated,
                case_insensitive,
                ..
            } => {
                let op = if *case_insensitive { "ILIKE" } else { "LIKE" };
                let neg = if *negated { " NOT" } else { "" };
                write!(f, "({}{} {} {})", expr, neg, op, pattern)
            }
            BoundExpr::Case {
                operand,
                when_clauses,
                else_result,
            } => {
                write!(f, "CASE")?;
                if let Some(op) = operand {
                    write!(f, " {}", op)?;
                }
                for clause in when_clauses {
                    write!(f, " WHEN {} THEN {}", clause.condition, clause.result)?;
                }
                if let Some(e) = else_result {
                    write!(f, " ELSE {}", e)?;
                }
                write!(f, " END")
            }
            BoundExpr::Cast { expr, data_type } => {
                write!(f, "CAST({} AS {})", expr, data_type.display_name())
            }
        }
    }
}

/// Resolves a column name (optionally table-qualified) to a positional index.
///
/// Uses case-insensitive matching. Returns [`ExecutorError::AmbiguousColumn`]
/// if multiple columns match an unqualified name.
pub(super) fn resolve_column_index(
    table: Option<&str>,
    column: &str,
    columns: &[ColumnDesc],
) -> Result<usize, ExecutorError> {
    let mut matched_idx = None;

    for (i, desc) in columns.iter().enumerate() {
        if !desc.name.eq_ignore_ascii_case(column) {
            continue;
        }

        // Qualified reference: table must match
        if let Some(t) = table {
            if let Some(ref source) = desc.source
                && source.table_name.eq_ignore_ascii_case(t)
            {
                return Ok(i); // Early return: exact match found
            }
            continue;
        }

        // Unqualified reference: check for ambiguity
        if matched_idx.is_some() {
            return Err(ExecutorError::AmbiguousColumn {
                name: column.to_string(),
            });
        }
        matched_idx = Some(i);
    }

    matched_idx.ok_or_else(|| ExecutorError::ColumnNotFound {
        name: table
            .map(|t| format!("{}.{}", t, column))
            .unwrap_or_else(|| column.to_string()),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sql::Parser;

    /// Parses a SQL expression string into an AST Expr.
    fn parse_expr(sql: &str) -> Expr {
        Parser::new(sql).parse_expr().expect("parse error")
    }

    fn make_columns() -> Vec<ColumnDesc> {
        use crate::executor::ColumnSource;
        vec![
            ColumnDesc {
                name: "id".to_string(),
                source: Some(ColumnSource {
                    table_name: "users".to_string(),
                    table_oid: 1,
                    column_id: 1,
                }),
                data_type: Type::Int8,
            },
            ColumnDesc {
                name: "name".to_string(),
                source: Some(ColumnSource {
                    table_name: "users".to_string(),
                    table_oid: 1,
                    column_id: 2,
                }),
                data_type: Type::Text,
            },
            ColumnDesc {
                name: "id".to_string(),
                source: Some(ColumnSource {
                    table_name: "orders".to_string(),
                    table_oid: 2,
                    column_id: 1,
                }),
                data_type: Type::Int8,
            },
            ColumnDesc {
                name: "user_id".to_string(),
                source: Some(ColumnSource {
                    table_name: "orders".to_string(),
                    table_oid: 2,
                    column_id: 2,
                }),
                data_type: Type::Int8,
            },
        ]
    }

    #[test]
    fn test_display_literals() {
        assert_eq!(BoundExpr::Null.to_string(), "NULL");
        assert_eq!(BoundExpr::Boolean(true).to_string(), "true");
        assert_eq!(BoundExpr::Integer(42).to_string(), "42");
        assert_eq!(BoundExpr::Float(3.14).to_string(), "3.14");
        assert_eq!(BoundExpr::String("hello".into()).to_string(), "'hello'");
    }

    #[test]
    fn test_display_column() {
        assert_eq!(
            BoundExpr::Column {
                index: 0,
                name: None
            }
            .to_string(),
            "$col0"
        );
        assert_eq!(
            BoundExpr::Column {
                index: 1,
                name: Some("id".into())
            }
            .to_string(),
            "$col1 (id)"
        );
    }

    #[test]
    fn test_display_binary_op() {
        let expr = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Column {
                index: 0,
                name: Some("age".into()),
            }),
            op: BinaryOperator::Gt,
            right: Box::new(BoundExpr::Integer(18)),
        };
        assert_eq!(expr.to_string(), "($col0 (age) > 18)");
    }

    #[test]
    fn test_bind_literals() {
        let columns = vec![];

        let bound = BoundExpr::bind(&parse_expr("NULL"), &columns).unwrap();
        assert!(matches!(bound, BoundExpr::Null));

        let bound = BoundExpr::bind(&parse_expr("TRUE"), &columns).unwrap();
        assert!(matches!(bound, BoundExpr::Boolean(true)));

        let bound = BoundExpr::bind(&parse_expr("42"), &columns).unwrap();
        assert!(matches!(bound, BoundExpr::Integer(42)));

        let bound = BoundExpr::bind(&parse_expr("3.14"), &columns).unwrap();
        assert!(matches!(bound, BoundExpr::Float(v) if (v - 3.14).abs() < f64::EPSILON));

        let bound = BoundExpr::bind(&parse_expr("'hello'"), &columns).unwrap();
        assert!(matches!(bound, BoundExpr::String(s) if s == "hello"));
    }

    #[test]
    fn test_bind_column_unqualified_unique() {
        let columns = make_columns();

        // "name" is unique, should resolve to index 1 with qualified display name
        let bound = BoundExpr::bind(&parse_expr("name"), &columns).unwrap();
        assert!(
            matches!(bound, BoundExpr::Column { index: 1, name: Some(ref n) } if n == "users.name")
        );

        // "user_id" is unique, should resolve to index 3
        let bound = BoundExpr::bind(&parse_expr("user_id"), &columns).unwrap();
        assert!(
            matches!(bound, BoundExpr::Column { index: 3, name: Some(ref n) } if n == "orders.user_id")
        );
    }

    #[test]
    fn test_bind_column_unqualified_ambiguous() {
        let columns = make_columns();

        // "id" exists in both tables, should be ambiguous
        let err = BoundExpr::bind(&parse_expr("id"), &columns).unwrap_err();
        assert!(matches!(err, ExecutorError::AmbiguousColumn { name } if name == "id"));
    }

    #[test]
    fn test_bind_column_qualified() {
        let columns = make_columns();

        // "users.id" should resolve to index 0
        let bound = BoundExpr::bind(&parse_expr("users.id"), &columns).unwrap();
        assert!(
            matches!(bound, BoundExpr::Column { index: 0, name: Some(ref n) } if n == "users.id")
        );

        // "orders.id" should resolve to index 2
        let bound = BoundExpr::bind(&parse_expr("orders.id"), &columns).unwrap();
        assert!(
            matches!(bound, BoundExpr::Column { index: 2, name: Some(ref n) } if n == "orders.id")
        );
    }

    #[test]
    fn test_bind_column_case_insensitive() {
        let columns = make_columns();

        // Case-insensitive matching
        let bound = BoundExpr::bind(&parse_expr("NAME"), &columns).unwrap();
        assert!(matches!(bound, BoundExpr::Column { index: 1, .. }));

        let bound = BoundExpr::bind(&parse_expr("USERS.ID"), &columns).unwrap();
        assert!(matches!(bound, BoundExpr::Column { index: 0, .. }));
    }

    #[test]
    fn test_bind_column_not_found() {
        let columns = make_columns();

        // Non-existent column
        let err = BoundExpr::bind(&parse_expr("nonexistent"), &columns).unwrap_err();
        assert!(matches!(err, ExecutorError::ColumnNotFound { name } if name == "nonexistent"));

        // Non-existent qualified column
        let err = BoundExpr::bind(&parse_expr("users.nonexistent"), &columns).unwrap_err();
        assert!(
            matches!(err, ExecutorError::ColumnNotFound { name } if name == "users.nonexistent")
        );

        // Wrong table qualification
        let err = BoundExpr::bind(&parse_expr("products.id"), &columns).unwrap_err();
        assert!(matches!(err, ExecutorError::ColumnNotFound { name } if name == "products.id"));
    }

    #[test]
    fn test_bind_binary_op() {
        let columns = make_columns();

        // name = 'alice'
        let bound = BoundExpr::bind(&parse_expr("name = 'alice'"), &columns).unwrap();
        let BoundExpr::BinaryOp { left, right, op } = bound else {
            panic!("expected BinaryOp");
        };
        assert_eq!(op, BinaryOperator::Eq);
        assert!(matches!(*left, BoundExpr::Column { index: 1, .. }));
        assert!(matches!(*right, BoundExpr::String(ref s) if s == "alice"));
    }

    #[test]
    fn test_bind_unary_op() {
        let columns = vec![];

        // -42
        let bound = BoundExpr::bind(&parse_expr("-42"), &columns).unwrap();
        let BoundExpr::UnaryOp { operand, op } = bound else {
            panic!("expected UnaryOp");
        };
        assert_eq!(op, UnaryOperator::Minus);
        assert!(matches!(*operand, BoundExpr::Integer(42)));
    }

    #[test]
    fn test_bind_is_null() {
        let columns = make_columns();

        let bound = BoundExpr::bind(&parse_expr("name IS NULL"), &columns).unwrap();
        let BoundExpr::IsNull { expr, negated } = bound else {
            panic!("expected IsNull");
        };
        assert!(!negated);
        assert!(matches!(*expr, BoundExpr::Column { index: 1, .. }));
    }

    #[test]
    fn test_bind_in_list() {
        let columns = make_columns();

        // user_id IN (1, 2, 3)
        let bound = BoundExpr::bind(&parse_expr("user_id IN (1, 2, 3)"), &columns).unwrap();
        let BoundExpr::InList {
            expr,
            list,
            negated,
        } = bound
        else {
            panic!("expected InList");
        };
        assert!(!negated);
        assert!(matches!(*expr, BoundExpr::Column { index: 3, .. }));
        assert_eq!(list.len(), 3);
    }

    #[test]
    fn test_bind_between() {
        let columns = make_columns();

        // user_id BETWEEN 1 AND 10
        let bound = BoundExpr::bind(&parse_expr("user_id BETWEEN 1 AND 10"), &columns).unwrap();
        let BoundExpr::Between {
            expr,
            low,
            high,
            negated,
        } = bound
        else {
            panic!("expected Between");
        };
        assert!(!negated);
        assert!(matches!(*expr, BoundExpr::Column { index: 3, .. }));
        assert!(matches!(*low, BoundExpr::Integer(1)));
        assert!(matches!(*high, BoundExpr::Integer(10)));
    }

    #[test]
    fn test_bind_like() {
        let columns = make_columns();

        // name LIKE 'a%'
        let bound = BoundExpr::bind(&parse_expr("name LIKE 'a%'"), &columns).unwrap();
        let BoundExpr::Like {
            expr,
            pattern,
            negated,
            case_insensitive,
            ..
        } = bound
        else {
            panic!("expected Like");
        };
        assert!(!negated);
        assert!(!case_insensitive);
        assert!(matches!(*expr, BoundExpr::Column { index: 1, .. }));
        assert!(matches!(*pattern, BoundExpr::String(ref s) if s == "a%"));
    }

    #[test]
    fn test_bind_case() {
        let columns = make_columns();

        // CASE WHEN user_id = 1 THEN 'one' ELSE 'other' END
        let bound = BoundExpr::bind(
            &parse_expr("CASE WHEN user_id = 1 THEN 'one' ELSE 'other' END"),
            &columns,
        )
        .unwrap();
        let BoundExpr::Case {
            operand,
            when_clauses,
            else_result,
        } = bound
        else {
            panic!("expected Case");
        };
        assert!(operand.is_none());
        assert!(else_result.is_some());
        assert_eq!(when_clauses.len(), 1);
    }

    #[test]
    fn test_bind_cast() {
        let columns = make_columns();

        // CAST(user_id AS TEXT)
        let bound = BoundExpr::bind(&parse_expr("CAST(user_id AS TEXT)"), &columns).unwrap();
        let BoundExpr::Cast { expr, data_type } = bound else {
            panic!("expected Cast");
        };
        assert_eq!(data_type, Type::Text);
        assert!(matches!(*expr, BoundExpr::Column { index: 3, .. }));
    }

    #[test]
    fn test_bind_unsupported() {
        let columns = vec![];

        // Parameter
        let err = BoundExpr::bind(&parse_expr("$1"), &columns).unwrap_err();
        assert!(matches!(err, ExecutorError::Unsupported(_)));

        // Function
        let err = BoundExpr::bind(&parse_expr("count()"), &columns).unwrap_err();
        assert!(matches!(err, ExecutorError::Unsupported(_)));
    }
}
