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
/// `ColumnRef { table, column }` with `Column { index, name, ty }`, enabling O(1) column
/// access during evaluation instead of O(n) name matching on every row.
/// Each variant carries enough information to compute its output [`Type`] via [`BoundExpr::ty()`].
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
        /// Output type of the referenced column.
        ty: Type,
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
    Cast { expr: Box<BoundExpr>, ty: Type },
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
    /// Returns the output type of this expression.
    ///
    /// Every variant carries enough structural information to determine
    /// its output type without consulting external metadata.
    pub fn ty(&self) -> Type {
        match self {
            // NOTE: NULL has no inherent type. Type::Text is a fallback similar to
            // PostgreSQL's "unknown" type. Callers that need type-aware NULL handling
            // (e.g., coerce()) should short-circuit on BoundExpr::Null before calling ty().
            BoundExpr::Null => Type::Text,
            BoundExpr::Boolean(_) => Type::Bool,
            BoundExpr::Integer(_) => Type::Bigint,
            BoundExpr::Float(_) => Type::Double,
            BoundExpr::String(_) => Type::Text,
            BoundExpr::Column { ty, .. } => *ty,
            BoundExpr::BinaryOp { op, left, right } => binary_op_type(*op, left.ty(), right.ty()),
            BoundExpr::UnaryOp { op, operand } => match op {
                UnaryOperator::Not => Type::Bool,
                UnaryOperator::Minus | UnaryOperator::Plus => operand.ty(),
            },
            BoundExpr::IsNull { .. }
            | BoundExpr::InList { .. }
            | BoundExpr::Between { .. }
            | BoundExpr::Like { .. } => Type::Bool,
            BoundExpr::Case {
                when_clauses,
                else_result,
                ..
            } => {
                if let Some(clause) = when_clauses.first() {
                    clause.result.ty()
                } else if let Some(e) = else_result {
                    e.ty()
                } else {
                    Type::Text
                }
            }
            BoundExpr::Cast { ty, .. } => *ty,
        }
    }

    /// Wraps this expression in a [`BoundExpr::Cast`] if its type doesn't match
    /// the target type.
    ///
    /// NULL values and expressions already matching the target type pass through
    /// unchanged.
    pub fn coerce(self, target_type: Type) -> BoundExpr {
        if matches!(&self, BoundExpr::Null) {
            return self;
        }
        if self.ty() == target_type {
            return self;
        }
        BoundExpr::Cast {
            expr: Box::new(self),
            ty: target_type,
        }
    }
}

/// Computes the output type of a binary operation from its operator and operand types.
fn binary_op_type(op: BinaryOperator, left: Type, right: Type) -> Type {
    match op {
        BinaryOperator::Eq
        | BinaryOperator::Neq
        | BinaryOperator::Lt
        | BinaryOperator::LtEq
        | BinaryOperator::Gt
        | BinaryOperator::GtEq
        | BinaryOperator::And
        | BinaryOperator::Or => Type::Bool,
        BinaryOperator::Concat => Type::Text,
        BinaryOperator::Add
        | BinaryOperator::Sub
        | BinaryOperator::Mul
        | BinaryOperator::Div
        | BinaryOperator::Mod => {
            let (Some(left), Some(right)) = (left.to_wide_numeric(), right.to_wide_numeric())
            else {
                // Non-numeric operand: keep the inferred type and let eval report the error.
                return left;
            };
            match (left, right) {
                (Type::Bigint, Type::Bigint) => Type::Bigint,
                _ => Type::Double,
            }
        }
    }
}

impl Expr {
    /// Converts this AST [`Expr`] into a [`BoundExpr`] by resolving column names
    /// to positional indices via the provided column descriptors.
    ///
    /// Unsupported AST variants (Parameter, Function, Subquery, InSubquery, Exists)
    /// return [`ExecutorError::Unsupported`].
    pub fn bind(&self, columns: &[ColumnDesc]) -> Result<BoundExpr, ExecutorError> {
        match self {
            Expr::Null => Ok(BoundExpr::Null),
            Expr::Boolean(b) => Ok(BoundExpr::Boolean(*b)),
            Expr::Integer(n) => Ok(BoundExpr::Integer(*n)),
            Expr::Float(f) => Ok(BoundExpr::Float(*f)),
            Expr::String(s) => Ok(BoundExpr::String(s.clone())),

            Expr::ColumnRef { table, column } => {
                let idx = resolve_column_index(table.as_deref(), column, columns)?;
                Ok(BoundExpr::Column {
                    index: idx,
                    name: Some(columns[idx].display_name()),
                    ty: columns[idx].ty,
                })
            }

            Expr::BinaryOp { left, op, right } => Ok(BoundExpr::BinaryOp {
                left: Box::new(left.bind(columns)?),
                op: *op,
                right: Box::new(right.bind(columns)?),
            }),

            Expr::UnaryOp { op, operand } => Ok(BoundExpr::UnaryOp {
                op: *op,
                operand: Box::new(operand.bind(columns)?),
            }),

            Expr::IsNull { expr, negated } => Ok(BoundExpr::IsNull {
                expr: Box::new(expr.bind(columns)?),
                negated: *negated,
            }),

            Expr::InList {
                expr,
                list,
                negated,
            } => {
                let bound_list = list
                    .iter()
                    .map(|e| e.bind(columns))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(BoundExpr::InList {
                    expr: Box::new(expr.bind(columns)?),
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
                expr: Box::new(expr.bind(columns)?),
                low: Box::new(low.bind(columns)?),
                high: Box::new(high.bind(columns)?),
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
                    Some(e) => Some(Box::new(e.bind(columns)?)),
                    None => None,
                };
                Ok(BoundExpr::Like {
                    expr: Box::new(expr.bind(columns)?),
                    pattern: Box::new(pattern.bind(columns)?),
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
                    Some(op) => Some(Box::new(op.bind(columns)?)),
                    None => None,
                };
                let bound_whens = when_clauses
                    .iter()
                    .map(|wc| {
                        Ok(BoundWhenClause {
                            condition: wc.condition.bind(columns)?,
                            result: wc.result.bind(columns)?,
                        })
                    })
                    .collect::<Result<Vec<_>, ExecutorError>>()?;
                let bound_else = match else_result {
                    Some(e) => Some(Box::new(e.bind(columns)?)),
                    None => None,
                };
                Ok(BoundExpr::Case {
                    operand: bound_operand,
                    when_clauses: bound_whens,
                    else_result: bound_else,
                })
            }

            Expr::Cast { expr, data_type } => Ok(BoundExpr::Cast {
                expr: Box::new(expr.bind(columns)?),
                ty: data_type.to_type(),
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
            BoundExpr::Column { index, name, .. } => match name {
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
            BoundExpr::Cast { expr, ty } => {
                write!(f, "CAST({} AS {})", expr, ty.display_name())
            }
        }
    }
}

/// Resolves a column name (optionally table-qualified) to a positional index.
///
/// Uses case-insensitive matching. Returns [`ExecutorError::AmbiguousColumn`]
/// if multiple columns match an unqualified name.
fn resolve_column_index(
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

    /// Parses and binds a SQL expression against the given column descriptors.
    fn bind_expr(sql: &str, columns: &[ColumnDesc]) -> BoundExpr {
        parse_expr(sql).bind(columns).expect("bind error")
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
                ty: Type::Bigint,
            },
            ColumnDesc {
                name: "name".to_string(),
                source: Some(ColumnSource {
                    table_name: "users".to_string(),
                    table_oid: 1,
                    column_id: 2,
                }),
                ty: Type::Text,
            },
            ColumnDesc {
                name: "id".to_string(),
                source: Some(ColumnSource {
                    table_name: "orders".to_string(),
                    table_oid: 2,
                    column_id: 1,
                }),
                ty: Type::Bigint,
            },
            ColumnDesc {
                name: "user_id".to_string(),
                source: Some(ColumnSource {
                    table_name: "orders".to_string(),
                    table_oid: 2,
                    column_id: 2,
                }),
                ty: Type::Bigint,
            },
        ]
    }

    #[test]
    fn test_display_literals() {
        let columns = vec![];
        assert_eq!(bind_expr("NULL", &columns).to_string(), "NULL");
        assert_eq!(bind_expr("TRUE", &columns).to_string(), "true");
        assert_eq!(bind_expr("42", &columns).to_string(), "42");
        assert_eq!(bind_expr("3.14", &columns).to_string(), "3.14");
        assert_eq!(bind_expr("'hello'", &columns).to_string(), "'hello'");
    }

    #[test]
    fn test_display_column() {
        let columns = make_columns();
        assert_eq!(
            bind_expr("name", &columns).to_string(),
            "$col1 (users.name)"
        );
        assert_eq!(
            bind_expr("orders.id", &columns).to_string(),
            "$col2 (orders.id)"
        );
    }

    #[test]
    fn test_display_binary_op() {
        let columns = make_columns();
        assert_eq!(
            bind_expr("users.id > 18", &columns).to_string(),
            "($col0 (users.id) > 18)"
        );
    }

    #[test]
    fn test_bind_literals() {
        let columns = vec![];

        assert!(matches!(bind_expr("NULL", &columns), BoundExpr::Null));
        assert!(matches!(
            bind_expr("TRUE", &columns),
            BoundExpr::Boolean(true)
        ));
        assert!(matches!(bind_expr("42", &columns), BoundExpr::Integer(42)));
        assert!(
            matches!(bind_expr("3.14", &columns), BoundExpr::Float(v) if (v - 3.14).abs() < f64::EPSILON)
        );
        assert!(matches!(bind_expr("'hello'", &columns), BoundExpr::String(s) if s == "hello"));
    }

    #[test]
    fn test_bind_column_unqualified_unique() {
        let columns = make_columns();

        // "name" is unique, should resolve to index 1 with qualified display name
        let bound = bind_expr("name", &columns);
        assert!(
            matches!(&bound, BoundExpr::Column { index: 1, name: Some(n), ty: Type::Text } if n == "users.name")
        );

        // "user_id" is unique, should resolve to index 3
        let bound = bind_expr("user_id", &columns);
        assert!(
            matches!(&bound, BoundExpr::Column { index: 3, name: Some(n), ty: Type::Bigint } if n == "orders.user_id")
        );
    }

    #[test]
    fn test_bind_column_unqualified_ambiguous() {
        let columns = make_columns();

        // "id" exists in both tables, should be ambiguous
        let err = parse_expr("id").bind(&columns).unwrap_err();
        assert!(matches!(err, ExecutorError::AmbiguousColumn { name } if name == "id"));
    }

    #[test]
    fn test_bind_column_qualified() {
        let columns = make_columns();

        // "users.id" should resolve to index 0
        let bound = bind_expr("users.id", &columns);
        assert!(
            matches!(&bound, BoundExpr::Column { index: 0, name: Some(n), ty: Type::Bigint } if n == "users.id")
        );

        // "orders.id" should resolve to index 2
        let bound = bind_expr("orders.id", &columns);
        assert!(
            matches!(&bound, BoundExpr::Column { index: 2, name: Some(n), ty: Type::Bigint } if n == "orders.id")
        );
    }

    #[test]
    fn test_bind_column_case_insensitive() {
        let columns = make_columns();

        // Case-insensitive matching
        assert!(matches!(
            bind_expr("NAME", &columns),
            BoundExpr::Column { index: 1, .. }
        ));
        assert!(matches!(
            bind_expr("USERS.ID", &columns),
            BoundExpr::Column { index: 0, .. }
        ));
    }

    #[test]
    fn test_bind_column_not_found() {
        let columns = make_columns();

        // Non-existent column
        let err = parse_expr("nonexistent").bind(&columns).unwrap_err();
        assert!(matches!(err, ExecutorError::ColumnNotFound { name } if name == "nonexistent"));

        // Non-existent qualified column
        let err = parse_expr("users.nonexistent").bind(&columns).unwrap_err();
        assert!(
            matches!(err, ExecutorError::ColumnNotFound { name } if name == "users.nonexistent")
        );

        // Wrong table qualification
        let err = parse_expr("products.id").bind(&columns).unwrap_err();
        assert!(matches!(err, ExecutorError::ColumnNotFound { name } if name == "products.id"));
    }

    #[test]
    fn test_bind_binary_op() {
        let columns = make_columns();

        let BoundExpr::BinaryOp { left, right, op } = bind_expr("name = 'alice'", &columns) else {
            panic!("expected BinaryOp");
        };
        assert_eq!(op, BinaryOperator::Eq);
        assert!(matches!(*left, BoundExpr::Column { index: 1, .. }));
        assert!(matches!(*right, BoundExpr::String(ref s) if s == "alice"));
    }

    #[test]
    fn test_bind_unary_op() {
        let columns = vec![];

        let BoundExpr::UnaryOp { operand, op } = bind_expr("-42", &columns) else {
            panic!("expected UnaryOp");
        };
        assert_eq!(op, UnaryOperator::Minus);
        assert!(matches!(*operand, BoundExpr::Integer(42)));
    }

    #[test]
    fn test_bind_is_null() {
        let columns = make_columns();

        let BoundExpr::IsNull { expr, negated } = bind_expr("name IS NULL", &columns) else {
            panic!("expected IsNull");
        };
        assert!(!negated);
        assert!(matches!(*expr, BoundExpr::Column { index: 1, .. }));
    }

    #[test]
    fn test_bind_in_list() {
        let columns = make_columns();

        let BoundExpr::InList {
            expr,
            list,
            negated,
        } = bind_expr("user_id IN (1, 2, 3)", &columns)
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

        let BoundExpr::Between {
            expr,
            low,
            high,
            negated,
        } = bind_expr("user_id BETWEEN 1 AND 10", &columns)
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

        let BoundExpr::Like {
            expr,
            pattern,
            negated,
            case_insensitive,
            ..
        } = bind_expr("name LIKE 'a%'", &columns)
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

        let BoundExpr::Case {
            operand,
            when_clauses,
            else_result,
        } = bind_expr(
            "CASE WHEN user_id = 1 THEN 'one' ELSE 'other' END",
            &columns,
        )
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

        let BoundExpr::Cast { expr, ty } = bind_expr("CAST(user_id AS TEXT)", &columns) else {
            panic!("expected Cast");
        };
        assert_eq!(ty, Type::Text);
        assert!(matches!(*expr, BoundExpr::Column { index: 3, .. }));
    }

    #[test]
    fn test_bind_unsupported() {
        let columns = vec![];

        let err = parse_expr("$1").bind(&columns).unwrap_err();
        assert!(matches!(err, ExecutorError::Unsupported(_)));

        let err = parse_expr("count()").bind(&columns).unwrap_err();
        assert!(matches!(err, ExecutorError::Unsupported(_)));
    }

    #[test]
    fn test_coerce_null_passthrough() {
        assert!(matches!(
            BoundExpr::Null.coerce(Type::Integer),
            BoundExpr::Null
        ));
    }

    #[test]
    fn test_coerce_matching_type_no_cast() {
        let expr = BoundExpr::String("hello".to_string());
        let coerced = expr.coerce(Type::Text);
        assert!(matches!(coerced, BoundExpr::String(s) if s == "hello"));
    }

    #[test]
    fn test_coerce_already_cast_to_target() {
        let expr = BoundExpr::Cast {
            expr: Box::new(BoundExpr::Integer(1)),
            ty: Type::Smallint,
        };
        let coerced = expr.coerce(Type::Smallint);
        // Should not double-wrap
        let BoundExpr::Cast { ty, .. } = &coerced else {
            panic!("expected Cast");
        };
        assert_eq!(*ty, Type::Smallint);
    }

    #[test]
    fn test_coerce_wraps_in_cast() {
        let expr = BoundExpr::Integer(42);
        let coerced = expr.coerce(Type::Smallint);
        let BoundExpr::Cast { ty, expr } = &coerced else {
            panic!("expected Cast, got {:?}", coerced);
        };
        assert_eq!(*ty, Type::Smallint);
        assert!(matches!(expr.as_ref(), BoundExpr::Integer(42)));
    }
}
