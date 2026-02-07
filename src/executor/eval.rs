//! Expression evaluator for SQL expressions.
//!
//! Evaluates [`Expr`] AST nodes against a row of values, producing a single
//! [`Value`] result. Supports arithmetic, comparison, logical, string, NULL,
//! LIKE, CASE, and CAST operations.

use crate::datum::Value;
use crate::heap::Record;
use crate::sql::{BinaryOperator, DataType, Expr, UnaryOperator};

use super::error::ExecutorError;
use super::types::ColumnDesc;

// ---------------------------------------------------------------------------
// BoundExpr: compile-time resolved expression tree
// ---------------------------------------------------------------------------

/// An expression tree with column references resolved to positional indices.
///
/// Unlike the AST [`Expr`], `BoundExpr` replaces `ColumnRef { table, column }`
/// with `Column(usize)`, enabling O(1) column access during evaluation instead
/// of O(n) name matching on every row.
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
    Column(usize),
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
    IsNull {
        expr: Box<BoundExpr>,
        negated: bool,
    },
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
        data_type: DataType,
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

/// Converts an AST [`Expr`] into a [`BoundExpr`] by resolving column names
/// to positional indices via the provided column descriptors.
///
/// Unsupported AST variants (Parameter, Function, Subquery, InSubquery, Exists)
/// return [`ExecutorError::Unsupported`].
pub fn bind_expr(expr: &Expr, columns: &[ColumnDesc]) -> Result<BoundExpr, ExecutorError> {
    match expr {
        Expr::Null => Ok(BoundExpr::Null),
        Expr::Boolean(b) => Ok(BoundExpr::Boolean(*b)),
        Expr::Integer(n) => Ok(BoundExpr::Integer(*n)),
        Expr::Float(f) => Ok(BoundExpr::Float(*f)),
        Expr::String(s) => Ok(BoundExpr::String(s.clone())),

        Expr::ColumnRef { table, column } => {
            let idx = resolve_column_index(table.as_deref(), column, columns)?;
            Ok(BoundExpr::Column(idx))
        }

        Expr::BinaryOp { left, op, right } => Ok(BoundExpr::BinaryOp {
            left: Box::new(bind_expr(left, columns)?),
            op: *op,
            right: Box::new(bind_expr(right, columns)?),
        }),

        Expr::UnaryOp { op, operand } => Ok(BoundExpr::UnaryOp {
            op: *op,
            operand: Box::new(bind_expr(operand, columns)?),
        }),

        Expr::IsNull { expr, negated } => Ok(BoundExpr::IsNull {
            expr: Box::new(bind_expr(expr, columns)?),
            negated: *negated,
        }),

        Expr::InList {
            expr,
            list,
            negated,
        } => {
            let bound_list = list
                .iter()
                .map(|e| bind_expr(e, columns))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(BoundExpr::InList {
                expr: Box::new(bind_expr(expr, columns)?),
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
            expr: Box::new(bind_expr(expr, columns)?),
            low: Box::new(bind_expr(low, columns)?),
            high: Box::new(bind_expr(high, columns)?),
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
                Some(e) => Some(Box::new(bind_expr(e, columns)?)),
                None => None,
            };
            Ok(BoundExpr::Like {
                expr: Box::new(bind_expr(expr, columns)?),
                pattern: Box::new(bind_expr(pattern, columns)?),
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
                Some(op) => Some(Box::new(bind_expr(op, columns)?)),
                None => None,
            };
            let bound_whens = when_clauses
                .iter()
                .map(|wc| {
                    Ok(BoundWhenClause {
                        condition: bind_expr(&wc.condition, columns)?,
                        result: bind_expr(&wc.result, columns)?,
                    })
                })
                .collect::<Result<Vec<_>, ExecutorError>>()?;
            let bound_else = match else_result {
                Some(e) => Some(Box::new(bind_expr(e, columns)?)),
                None => None,
            };
            Ok(BoundExpr::Case {
                operand: bound_operand,
                when_clauses: bound_whens,
                else_result: bound_else,
            })
        }

        Expr::Cast { expr, data_type } => Ok(BoundExpr::Cast {
            expr: Box::new(bind_expr(expr, columns)?),
            data_type: data_type.clone(),
        }),

        Expr::Parameter(_) => Err(ExecutorError::Unsupported(
            "parameter placeholders are not yet supported".to_string(),
        )),

        Expr::Function { .. } => Err(ExecutorError::Unsupported(
            "function calls are not yet supported".to_string(),
        )),

        Expr::InSubquery { .. } | Expr::Exists { .. } | Expr::Subquery(_) => {
            Err(ExecutorError::Unsupported(
                "subqueries are not yet supported".to_string(),
            ))
        }
    }
}

/// Resolves a column name (optionally table-qualified) to a positional index.
///
/// Uses case-insensitive matching. Returns [`ExecutorError::AmbiguousColumn`]
/// if multiple columns match an unqualified name.
pub fn resolve_column_index(
    table: Option<&str>,
    column: &str,
    columns: &[ColumnDesc],
) -> Result<usize, ExecutorError> {
    let mut matched_idx = None;
    for (i, desc) in columns.iter().enumerate() {
        let name_matches = desc.name.eq_ignore_ascii_case(column);
        let table_matches = match table {
            Some(_t) => name_matches,
            None => name_matches,
        };
        if table_matches {
            if matched_idx.is_some() && table.is_none() {
                return Err(ExecutorError::AmbiguousColumn {
                    name: column.to_string(),
                });
            }
            matched_idx = Some(i);
            if table.is_some() {
                break;
            }
        }
    }
    matched_idx.ok_or_else(|| ExecutorError::ColumnNotFound {
        name: column.to_string(),
    })
}

impl BoundExpr {
    /// Evaluates the bound expression against a record, producing a [`Value`].
    ///
    /// Column references are resolved via positional index (O(1)) instead
    /// of name matching.
    pub fn evaluate(&self, record: &Record) -> Result<Value, ExecutorError> {
        match self {
            BoundExpr::Null => Ok(Value::Null),
            BoundExpr::Boolean(b) => Ok(Value::Boolean(*b)),
            BoundExpr::Integer(n) => Ok(Value::Int64(*n)),
            BoundExpr::Float(f) => Ok(Value::Float64(*f)),
            BoundExpr::String(s) => Ok(Value::Text(s.clone())),

            BoundExpr::Column(idx) => {
                if *idx < record.values.len() {
                    Ok(record.values[*idx].clone())
                } else {
                    Err(ExecutorError::ColumnIndexOutOfBounds {
                        index: *idx,
                        len: record.values.len(),
                    })
                }
            }

            BoundExpr::BinaryOp { left, op, right } => {
                let l = left.evaluate(record)?;
                let r = right.evaluate(record)?;
                eval_binary_op(&l, *op, &r)
            }

            BoundExpr::UnaryOp { op, operand } => {
                let v = operand.evaluate(record)?;
                eval_unary_op(*op, &v)
            }

            BoundExpr::IsNull { expr, negated } => {
                let v = expr.evaluate(record)?;
                let is_null = v.is_null();
                Ok(Value::Boolean(if *negated { !is_null } else { is_null }))
            }

            BoundExpr::InList {
                expr,
                list,
                negated,
            } => {
                let v = expr.evaluate(record)?;
                if v.is_null() {
                    return Ok(Value::Null);
                }
                let mut found = false;
                let mut has_null = false;
                for item in list {
                    let item_val = item.evaluate(record)?;
                    if item_val.is_null() {
                        has_null = true;
                        continue;
                    }
                    if compare_values(&v, &item_val)? == std::cmp::Ordering::Equal {
                        found = true;
                        break;
                    }
                }
                let result = if found {
                    Value::Boolean(!*negated)
                } else if has_null {
                    Value::Null
                } else {
                    Value::Boolean(*negated)
                };
                Ok(result)
            }

            BoundExpr::Between {
                expr,
                low,
                high,
                negated,
            } => {
                let v = expr.evaluate(record)?;
                let lo = low.evaluate(record)?;
                let hi = high.evaluate(record)?;
                if v.is_null() || lo.is_null() || hi.is_null() {
                    return Ok(Value::Null);
                }
                let ge_low = compare_values(&v, &lo)? != std::cmp::Ordering::Less;
                let le_high = compare_values(&v, &hi)? != std::cmp::Ordering::Greater;
                let in_range = ge_low && le_high;
                Ok(Value::Boolean(if *negated { !in_range } else { in_range }))
            }

            BoundExpr::Like {
                expr,
                pattern,
                escape,
                negated,
                case_insensitive,
            } => {
                let v = expr.evaluate(record)?;
                let p = pattern.evaluate(record)?;
                if v.is_null() || p.is_null() {
                    return Ok(Value::Null);
                }
                let escape_char = match escape {
                    Some(e) => {
                        let e_val = e.evaluate(record)?;
                        match e_val {
                            Value::Text(s) if s.len() == 1 => Some(s.chars().next().unwrap()),
                            _ => {
                                return Err(ExecutorError::Unsupported(
                                    "ESCAPE must be a single character".to_string(),
                                ))
                            }
                        }
                    }
                    None => None,
                };
                let (s, pat) = match (&v, &p) {
                    (Value::Text(s), Value::Text(p)) => (s.as_str(), p.as_str()),
                    _ => {
                        return Err(ExecutorError::TypeMismatch {
                            expected: "text".to_string(),
                            found: format!("{:?}", v),
                        })
                    }
                };
                let matched = like_match(s, pat, escape_char, *case_insensitive);
                Ok(Value::Boolean(if *negated { !matched } else { matched }))
            }

            BoundExpr::Case {
                operand,
                when_clauses,
                else_result,
            } => {
                if let Some(op) = operand {
                    let op_val = op.evaluate(record)?;
                    for clause in when_clauses {
                        let when_val = clause.condition.evaluate(record)?;
                        if !op_val.is_null()
                            && !when_val.is_null()
                            && compare_values(&op_val, &when_val)? == std::cmp::Ordering::Equal
                        {
                            return clause.result.evaluate(record);
                        }
                    }
                } else {
                    for clause in when_clauses {
                        let cond = clause.condition.evaluate(record)?;
                        if matches!(cond, Value::Boolean(true)) {
                            return clause.result.evaluate(record);
                        }
                    }
                }
                match else_result {
                    Some(e) => e.evaluate(record),
                    None => Ok(Value::Null),
                }
            }

            BoundExpr::Cast { expr, data_type } => {
                let v = expr.evaluate(record)?;
                eval_cast(v, data_type)
            }
        }
    }
}

/// Formats a [`BoundExpr`] as a human-readable SQL-like string for EXPLAIN output.
///
/// Column references are displayed as `$col{idx}` (e.g., `$col0`).
pub fn format_bound_expr(expr: &BoundExpr) -> String {
    match expr {
        BoundExpr::Null => "NULL".to_string(),
        BoundExpr::Boolean(b) => b.to_string(),
        BoundExpr::Integer(n) => n.to_string(),
        BoundExpr::Float(f) => f.to_string(),
        BoundExpr::String(s) => format!("'{}'", s),
        BoundExpr::Column(idx) => format!("$col{}", idx),
        BoundExpr::BinaryOp { left, op, right } => {
            format!(
                "({} {} {})",
                format_bound_expr(left),
                op.as_str(),
                format_bound_expr(right)
            )
        }
        BoundExpr::UnaryOp { op, operand } => match op {
            UnaryOperator::Not => format!("(NOT {})", format_bound_expr(operand)),
            _ => format!("({}{})", op.as_str(), format_bound_expr(operand)),
        },
        BoundExpr::IsNull { expr, negated } => {
            if *negated {
                format!("({} IS NOT NULL)", format_bound_expr(expr))
            } else {
                format!("({} IS NULL)", format_bound_expr(expr))
            }
        }
        BoundExpr::InList {
            expr,
            list,
            negated,
        } => {
            let items: Vec<String> = list.iter().map(format_bound_expr).collect();
            let neg = if *negated { " NOT" } else { "" };
            format!(
                "({}{} IN ({}))",
                format_bound_expr(expr),
                neg,
                items.join(", ")
            )
        }
        BoundExpr::Between {
            expr,
            low,
            high,
            negated,
        } => {
            let neg = if *negated { " NOT" } else { "" };
            format!(
                "({}{} BETWEEN {} AND {})",
                format_bound_expr(expr),
                neg,
                format_bound_expr(low),
                format_bound_expr(high)
            )
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
            format!(
                "({}{} {} {})",
                format_bound_expr(expr),
                neg,
                op,
                format_bound_expr(pattern)
            )
        }
        BoundExpr::Case {
            operand,
            when_clauses,
            else_result,
        } => {
            let mut s = "CASE".to_string();
            if let Some(op) = operand {
                s.push_str(&format!(" {}", format_bound_expr(op)));
            }
            for clause in when_clauses {
                s.push_str(&format!(
                    " WHEN {} THEN {}",
                    format_bound_expr(&clause.condition),
                    format_bound_expr(&clause.result)
                ));
            }
            if let Some(e) = else_result {
                s.push_str(&format!(" ELSE {}", format_bound_expr(e)));
            }
            s.push_str(" END");
            s
        }
        BoundExpr::Cast { expr, data_type } => {
            format!("CAST({} AS {})", format_bound_expr(expr), data_type.display_name())
        }
    }
}

/// Formats a [`BoundExpr`] with column names resolved from the provided descriptors.
///
/// Column indices are resolved back to their human-readable names using `columns`.
/// Falls back to `$col{idx}` if the index is out of bounds.
pub fn format_bound_expr_with_columns(expr: &BoundExpr, columns: &[ColumnDesc]) -> String {
    match expr {
        BoundExpr::Column(idx) => {
            if *idx < columns.len() {
                columns[*idx].name.clone()
            } else {
                format!("$col{}", idx)
            }
        }
        BoundExpr::BinaryOp { left, op, right } => {
            format!(
                "({} {} {})",
                format_bound_expr_with_columns(left, columns),
                op.as_str(),
                format_bound_expr_with_columns(right, columns)
            )
        }
        BoundExpr::UnaryOp { op, operand } => match op {
            UnaryOperator::Not => {
                format!("(NOT {})", format_bound_expr_with_columns(operand, columns))
            }
            _ => format!(
                "({}{})",
                op.as_str(),
                format_bound_expr_with_columns(operand, columns)
            ),
        },
        BoundExpr::IsNull { expr, negated } => {
            if *negated {
                format!(
                    "({} IS NOT NULL)",
                    format_bound_expr_with_columns(expr, columns)
                )
            } else {
                format!(
                    "({} IS NULL)",
                    format_bound_expr_with_columns(expr, columns)
                )
            }
        }
        BoundExpr::InList {
            expr,
            list,
            negated,
        } => {
            let items: Vec<String> = list
                .iter()
                .map(|e| format_bound_expr_with_columns(e, columns))
                .collect();
            let neg = if *negated { " NOT" } else { "" };
            format!(
                "({}{} IN ({}))",
                format_bound_expr_with_columns(expr, columns),
                neg,
                items.join(", ")
            )
        }
        BoundExpr::Between {
            expr,
            low,
            high,
            negated,
        } => {
            let neg = if *negated { " NOT" } else { "" };
            format!(
                "({}{} BETWEEN {} AND {})",
                format_bound_expr_with_columns(expr, columns),
                neg,
                format_bound_expr_with_columns(low, columns),
                format_bound_expr_with_columns(high, columns)
            )
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
            format!(
                "({}{} {} {})",
                format_bound_expr_with_columns(expr, columns),
                neg,
                op,
                format_bound_expr_with_columns(pattern, columns)
            )
        }
        BoundExpr::Case {
            operand,
            when_clauses,
            else_result,
        } => {
            let mut s = "CASE".to_string();
            if let Some(op) = operand {
                s.push_str(&format!(
                    " {}",
                    format_bound_expr_with_columns(op, columns)
                ));
            }
            for clause in when_clauses {
                s.push_str(&format!(
                    " WHEN {} THEN {}",
                    format_bound_expr_with_columns(&clause.condition, columns),
                    format_bound_expr_with_columns(&clause.result, columns)
                ));
            }
            if let Some(e) = else_result {
                s.push_str(&format!(
                    " ELSE {}",
                    format_bound_expr_with_columns(e, columns)
                ));
            }
            s.push_str(" END");
            s
        }
        // Delegate non-column variants to the plain formatter
        other => format_bound_expr(other),
    }
}

/// Evaluates a binary operation.
fn eval_binary_op(
    left: &Value,
    op: BinaryOperator,
    right: &Value,
) -> Result<Value, ExecutorError> {
    // Logical operators with 3-value NULL logic
    match op {
        BinaryOperator::And => return eval_and(left, right),
        BinaryOperator::Or => return eval_or(left, right),
        _ => {}
    }

    // String concatenation
    if op == BinaryOperator::Concat {
        return eval_concat(left, right);
    }

    // NULL propagation for all other operators
    if left.is_null() || right.is_null() {
        return Ok(Value::Null);
    }

    // Comparison operators
    match op {
        BinaryOperator::Eq => {
            return Ok(Value::Boolean(
                compare_values(left, right)? == std::cmp::Ordering::Equal,
            ));
        }
        BinaryOperator::Neq => {
            return Ok(Value::Boolean(
                compare_values(left, right)? != std::cmp::Ordering::Equal,
            ));
        }
        BinaryOperator::Lt => {
            return Ok(Value::Boolean(
                compare_values(left, right)? == std::cmp::Ordering::Less,
            ));
        }
        BinaryOperator::LtEq => {
            return Ok(Value::Boolean(
                compare_values(left, right)? != std::cmp::Ordering::Greater,
            ));
        }
        BinaryOperator::Gt => {
            return Ok(Value::Boolean(
                compare_values(left, right)? == std::cmp::Ordering::Greater,
            ));
        }
        BinaryOperator::GtEq => {
            return Ok(Value::Boolean(
                compare_values(left, right)? != std::cmp::Ordering::Less,
            ));
        }
        _ => {}
    }

    // Arithmetic operators
    eval_arithmetic(left, op, right)
}

/// Evaluates AND with 3-value NULL logic.
fn eval_and(left: &Value, right: &Value) -> Result<Value, ExecutorError> {
    let l = value_to_bool_nullable(left)?;
    let r = value_to_bool_nullable(right)?;
    match (l, r) {
        (Some(false), _) | (_, Some(false)) => Ok(Value::Boolean(false)),
        (Some(true), Some(true)) => Ok(Value::Boolean(true)),
        _ => Ok(Value::Null),
    }
}

/// Evaluates OR with 3-value NULL logic.
fn eval_or(left: &Value, right: &Value) -> Result<Value, ExecutorError> {
    let l = value_to_bool_nullable(left)?;
    let r = value_to_bool_nullable(right)?;
    match (l, r) {
        (Some(true), _) | (_, Some(true)) => Ok(Value::Boolean(true)),
        (Some(false), Some(false)) => Ok(Value::Boolean(false)),
        _ => Ok(Value::Null),
    }
}

/// Converts a Value to an optional boolean (None for NULL).
fn value_to_bool_nullable(v: &Value) -> Result<Option<bool>, ExecutorError> {
    match v {
        Value::Null => Ok(None),
        Value::Boolean(b) => Ok(Some(*b)),
        _ => Err(ExecutorError::TypeMismatch {
            expected: "boolean".to_string(),
            found: value_type_name(v),
        }),
    }
}

/// Evaluates string concatenation (||).
fn eval_concat(left: &Value, right: &Value) -> Result<Value, ExecutorError> {
    if left.is_null() || right.is_null() {
        return Ok(Value::Null);
    }
    let l = left.to_text();
    let r = right.to_text();
    Ok(Value::Text(format!("{}{}", l, r)))
}

/// Evaluates arithmetic operators (+, -, *, /, %).
fn eval_arithmetic(
    left: &Value,
    op: BinaryOperator,
    right: &Value,
) -> Result<Value, ExecutorError> {
    // Promote to common numeric type
    let (l, r) = promote_numeric(left, right)?;

    match (&l, &r) {
        (Value::Int64(a), Value::Int64(b)) => {
            let result = match op {
                BinaryOperator::Add => a.checked_add(*b).ok_or(ExecutorError::Unsupported(
                    "integer overflow".to_string(),
                ))?,
                BinaryOperator::Sub => a.checked_sub(*b).ok_or(ExecutorError::Unsupported(
                    "integer overflow".to_string(),
                ))?,
                BinaryOperator::Mul => a.checked_mul(*b).ok_or(ExecutorError::Unsupported(
                    "integer overflow".to_string(),
                ))?,
                BinaryOperator::Div => {
                    if *b == 0 {
                        return Err(ExecutorError::DivisionByZero);
                    }
                    a / b
                }
                BinaryOperator::Mod => {
                    if *b == 0 {
                        return Err(ExecutorError::DivisionByZero);
                    }
                    a % b
                }
                _ => unreachable!(),
            };
            Ok(Value::Int64(result))
        }
        (Value::Float64(a), Value::Float64(b)) => {
            let result = match op {
                BinaryOperator::Add => a + b,
                BinaryOperator::Sub => a - b,
                BinaryOperator::Mul => a * b,
                BinaryOperator::Div => {
                    if *b == 0.0 {
                        return Err(ExecutorError::DivisionByZero);
                    }
                    a / b
                }
                BinaryOperator::Mod => {
                    if *b == 0.0 {
                        return Err(ExecutorError::DivisionByZero);
                    }
                    a % b
                }
                _ => unreachable!(),
            };
            Ok(Value::Float64(result))
        }
        _ => Err(ExecutorError::TypeMismatch {
            expected: "numeric".to_string(),
            found: format!("{:?}", left),
        }),
    }
}

/// Promotes two numeric values to a common type for arithmetic.
///
/// - Int16/Int32 are promoted to Int64.
/// - If either operand is Float, both are promoted to Float64.
fn promote_numeric(left: &Value, right: &Value) -> Result<(Value, Value), ExecutorError> {
    let l = promote_to_int64(left)?;
    let r = promote_to_int64(right)?;

    // If either is float, promote both to float
    match (&l, &r) {
        (Value::Float64(_), Value::Float64(_)) => Ok((l, r)),
        (Value::Float64(_), Value::Int64(n)) => Ok((l, Value::Float64(*n as f64))),
        (Value::Int64(n), Value::Float64(_)) => Ok((Value::Float64(*n as f64), r)),
        (Value::Int64(_), Value::Int64(_)) => Ok((l, r)),
        _ => Err(ExecutorError::TypeMismatch {
            expected: "numeric".to_string(),
            found: format!("{}, {}", value_type_name(left), value_type_name(right)),
        }),
    }
}

/// Promotes Int16/Int32 to Int64, passes Float32 to Float64.
fn promote_to_int64(v: &Value) -> Result<Value, ExecutorError> {
    match v {
        Value::Int16(n) => Ok(Value::Int64(*n as i64)),
        Value::Int32(n) => Ok(Value::Int64(*n as i64)),
        Value::Int64(_) => Ok(v.clone()),
        Value::Float32(n) => Ok(Value::Float64(*n as f64)),
        Value::Float64(_) => Ok(v.clone()),
        _ => Err(ExecutorError::TypeMismatch {
            expected: "numeric".to_string(),
            found: value_type_name(v),
        }),
    }
}

/// Compares two values, returning their ordering.
///
/// Values are promoted to a common type before comparison.
/// Boolean ordering: false < true.
fn compare_values(
    left: &Value,
    right: &Value,
) -> Result<std::cmp::Ordering, ExecutorError> {
    match (left, right) {
        (Value::Boolean(a), Value::Boolean(b)) => Ok(a.cmp(b)),
        (Value::Text(a), Value::Text(b)) => Ok(a.cmp(b)),
        (Value::Bytea(a), Value::Bytea(b)) => Ok(a.cmp(b)),
        _ => {
            // Try numeric comparison
            let l = promote_to_int64(left)?;
            let r = promote_to_int64(right)?;
            match (&l, &r) {
                (Value::Int64(a), Value::Int64(b)) => Ok(a.cmp(b)),
                (Value::Float64(a), Value::Float64(b)) => {
                    Ok(a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
                }
                (Value::Float64(a), Value::Int64(b)) => {
                    let b_f = *b as f64;
                    Ok(a.partial_cmp(&b_f).unwrap_or(std::cmp::Ordering::Equal))
                }
                (Value::Int64(a), Value::Float64(b)) => {
                    let a_f = *a as f64;
                    Ok(a_f.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
                }
                _ => Err(ExecutorError::TypeMismatch {
                    expected: "comparable types".to_string(),
                    found: format!("{}, {}", value_type_name(left), value_type_name(right)),
                }),
            }
        }
    }
}

/// Evaluates a unary operation.
fn eval_unary_op(op: UnaryOperator, val: &Value) -> Result<Value, ExecutorError> {
    if val.is_null() {
        return Ok(Value::Null);
    }
    match op {
        UnaryOperator::Not => match val {
            Value::Boolean(b) => Ok(Value::Boolean(!b)),
            _ => Err(ExecutorError::TypeMismatch {
                expected: "boolean".to_string(),
                found: value_type_name(val),
            }),
        },
        UnaryOperator::Minus => match val {
            Value::Int16(n) => Ok(Value::Int64(-(*n as i64))),
            Value::Int32(n) => Ok(Value::Int64(-(*n as i64))),
            Value::Int64(n) => Ok(Value::Int64(-n)),
            Value::Float32(n) => Ok(Value::Float64(-(*n as f64))),
            Value::Float64(n) => Ok(Value::Float64(-n)),
            _ => Err(ExecutorError::TypeMismatch {
                expected: "numeric".to_string(),
                found: value_type_name(val),
            }),
        },
        UnaryOperator::Plus => match val {
            Value::Int16(_) | Value::Int32(_) | Value::Int64(_)
            | Value::Float32(_) | Value::Float64(_) => Ok(val.clone()),
            _ => Err(ExecutorError::TypeMismatch {
                expected: "numeric".to_string(),
                found: value_type_name(val),
            }),
        },
    }
}

/// Evaluates a type cast (CAST(expr AS type)).
fn eval_cast(v: Value, target: &DataType) -> Result<Value, ExecutorError> {
    if v.is_null() {
        return Ok(Value::Null);
    }
    match target {
        DataType::Boolean => match &v {
            Value::Boolean(_) => Ok(v),
            Value::Text(s) => match s.to_lowercase().as_str() {
                "true" | "t" | "yes" | "y" | "1" | "on" => Ok(Value::Boolean(true)),
                "false" | "f" | "no" | "n" | "0" | "off" => Ok(Value::Boolean(false)),
                _ => Err(ExecutorError::InvalidCast {
                    from: format!("'{}'", s),
                    to: "boolean".to_string(),
                }),
            },
            Value::Int16(n) => Ok(Value::Boolean(*n != 0)),
            Value::Int32(n) => Ok(Value::Boolean(*n != 0)),
            Value::Int64(n) => Ok(Value::Boolean(*n != 0)),
            _ => Err(ExecutorError::InvalidCast {
                from: value_type_name(&v),
                to: "boolean".to_string(),
            }),
        },
        DataType::Smallint => match &v {
            Value::Int16(_) => Ok(v),
            Value::Int32(n) => Ok(Value::Int16(*n as i16)),
            Value::Int64(n) => Ok(Value::Int16(*n as i16)),
            Value::Float32(n) => Ok(Value::Int16(*n as i16)),
            Value::Float64(n) => Ok(Value::Int16(*n as i16)),
            Value::Text(s) => s
                .trim()
                .parse::<i16>()
                .map(Value::Int16)
                .map_err(|_| ExecutorError::InvalidCast {
                    from: format!("'{}'", s),
                    to: "smallint".to_string(),
                }),
            Value::Boolean(b) => Ok(Value::Int16(if *b { 1 } else { 0 })),
            _ => Err(ExecutorError::InvalidCast {
                from: value_type_name(&v),
                to: "smallint".to_string(),
            }),
        },
        DataType::Integer | DataType::Serial => match &v {
            Value::Int32(_) => Ok(v),
            Value::Int16(n) => Ok(Value::Int32(*n as i32)),
            Value::Int64(n) => Ok(Value::Int32(*n as i32)),
            Value::Float32(n) => Ok(Value::Int32(*n as i32)),
            Value::Float64(n) => Ok(Value::Int32(*n as i32)),
            Value::Text(s) => s
                .trim()
                .parse::<i32>()
                .map(Value::Int32)
                .map_err(|_| ExecutorError::InvalidCast {
                    from: format!("'{}'", s),
                    to: "integer".to_string(),
                }),
            Value::Boolean(b) => Ok(Value::Int32(if *b { 1 } else { 0 })),
            _ => Err(ExecutorError::InvalidCast {
                from: value_type_name(&v),
                to: "integer".to_string(),
            }),
        },
        DataType::Bigint => match &v {
            Value::Int64(_) => Ok(v),
            Value::Int16(n) => Ok(Value::Int64(*n as i64)),
            Value::Int32(n) => Ok(Value::Int64(*n as i64)),
            Value::Float32(n) => Ok(Value::Int64(*n as i64)),
            Value::Float64(n) => Ok(Value::Int64(*n as i64)),
            Value::Text(s) => s
                .trim()
                .parse::<i64>()
                .map(Value::Int64)
                .map_err(|_| ExecutorError::InvalidCast {
                    from: format!("'{}'", s),
                    to: "bigint".to_string(),
                }),
            Value::Boolean(b) => Ok(Value::Int64(if *b { 1 } else { 0 })),
            _ => Err(ExecutorError::InvalidCast {
                from: value_type_name(&v),
                to: "bigint".to_string(),
            }),
        },
        DataType::Real => match &v {
            Value::Float32(_) => Ok(v),
            Value::Float64(n) => Ok(Value::Float32(*n as f32)),
            Value::Int16(n) => Ok(Value::Float32(*n as f32)),
            Value::Int32(n) => Ok(Value::Float32(*n as f32)),
            Value::Int64(n) => Ok(Value::Float32(*n as f32)),
            Value::Text(s) => s
                .trim()
                .parse::<f32>()
                .map(Value::Float32)
                .map_err(|_| ExecutorError::InvalidCast {
                    from: format!("'{}'", s),
                    to: "real".to_string(),
                }),
            _ => Err(ExecutorError::InvalidCast {
                from: value_type_name(&v),
                to: "real".to_string(),
            }),
        },
        DataType::DoublePrecision => match &v {
            Value::Float64(_) => Ok(v),
            Value::Float32(n) => Ok(Value::Float64(*n as f64)),
            Value::Int16(n) => Ok(Value::Float64(*n as f64)),
            Value::Int32(n) => Ok(Value::Float64(*n as f64)),
            Value::Int64(n) => Ok(Value::Float64(*n as f64)),
            Value::Text(s) => s
                .trim()
                .parse::<f64>()
                .map(Value::Float64)
                .map_err(|_| ExecutorError::InvalidCast {
                    from: format!("'{}'", s),
                    to: "double precision".to_string(),
                }),
            _ => Err(ExecutorError::InvalidCast {
                from: value_type_name(&v),
                to: "double precision".to_string(),
            }),
        },
        DataType::Text | DataType::Varchar(_) => Ok(Value::Text(v.to_text())),
        DataType::Bytea => match &v {
            Value::Bytea(_) => Ok(v),
            Value::Text(s) => Ok(Value::Bytea(s.as_bytes().to_vec())),
            _ => Err(ExecutorError::InvalidCast {
                from: value_type_name(&v),
                to: "bytea".to_string(),
            }),
        },
    }
}

/// Returns a human-readable type name for a value.
fn value_type_name(v: &Value) -> String {
    match v {
        Value::Null => "null".to_string(),
        Value::Boolean(_) => "boolean".to_string(),
        Value::Int16(_) => "smallint".to_string(),
        Value::Int32(_) => "integer".to_string(),
        Value::Int64(_) => "bigint".to_string(),
        Value::Float32(_) => "real".to_string(),
        Value::Float64(_) => "double precision".to_string(),
        Value::Text(_) => "text".to_string(),
        Value::Bytea(_) => "bytea".to_string(),
    }
}

/// LIKE pattern matching with support for % and _ wildcards.
fn like_match(s: &str, pattern: &str, escape: Option<char>, case_insensitive: bool) -> bool {
    let s_chars: Vec<char> = if case_insensitive {
        s.to_lowercase().chars().collect()
    } else {
        s.chars().collect()
    };
    let p_chars: Vec<char> = if case_insensitive {
        pattern.to_lowercase().chars().collect()
    } else {
        pattern.chars().collect()
    };
    like_match_recursive(&s_chars, &p_chars, escape)
}

/// Recursive LIKE matching implementation.
fn like_match_recursive(s: &[char], p: &[char], escape: Option<char>) -> bool {
    if p.is_empty() {
        return s.is_empty();
    }

    // Check for escape character
    if let Some(esc) = escape
        && p[0] == esc
        && p.len() > 1
    {
        // Next character is literal
        if s.is_empty() || s[0] != p[1] {
            return false;
        }
        return like_match_recursive(&s[1..], &p[2..], escape);
    }

    match p[0] {
        '%' => {
            // % matches zero or more characters
            // Try matching rest of pattern starting from each position
            for i in 0..=s.len() {
                if like_match_recursive(&s[i..], &p[1..], escape) {
                    return true;
                }
            }
            false
        }
        '_' => {
            // _ matches exactly one character
            if s.is_empty() {
                return false;
            }
            like_match_recursive(&s[1..], &p[1..], escape)
        }
        c => {
            if s.is_empty() || s[0] != c {
                return false;
            }
            like_match_recursive(&s[1..], &p[1..], escape)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::datum::Type;

    // --- BoundExpr tests ---

    fn make_record(cols: &[(&str, Value)]) -> (Record, Vec<ColumnDesc>) {
        let values: Vec<Value> = cols.iter().map(|(_, v)| v.clone()).collect();
        let descs: Vec<ColumnDesc> = cols
            .iter()
            .map(|(name, v)| ColumnDesc {
                name: name.to_string(),
                table_oid: 0,
                column_id: 0,
                data_type: v.data_type().unwrap_or(Type::Text),
            })
            .collect();
        (Record::new(values), descs)
    }

    #[test]
    fn test_bind_expr_literals() {
        let cols: Vec<ColumnDesc> = vec![];
        let bound = bind_expr(&Expr::Integer(42), &cols).unwrap();
        assert!(matches!(bound, BoundExpr::Integer(42)));

        let bound = bind_expr(&Expr::String("hello".into()), &cols).unwrap();
        assert!(matches!(bound, BoundExpr::String(ref s) if s == "hello"));
    }

    #[test]
    fn test_bind_expr_column_resolution() {
        let cols = vec![
            ColumnDesc {
                name: "id".to_string(),
                table_oid: 0,
                column_id: 0,
                data_type: Type::Int8,
            },
            ColumnDesc {
                name: "name".to_string(),
                table_oid: 0,
                column_id: 0,
                data_type: Type::Text,
            },
        ];
        let expr = Expr::ColumnRef {
            table: None,
            column: "name".to_string(),
        };
        let bound = bind_expr(&expr, &cols).unwrap();
        assert!(matches!(bound, BoundExpr::Column(1)));
    }

    #[test]
    fn test_bind_expr_column_not_found() {
        let cols: Vec<ColumnDesc> = vec![];
        let expr = Expr::ColumnRef {
            table: None,
            column: "missing".to_string(),
        };
        assert!(matches!(
            bind_expr(&expr, &cols),
            Err(ExecutorError::ColumnNotFound { .. })
        ));
    }

    #[test]
    fn test_bound_expr_evaluate_literals() {
        let record = Record::new(vec![]);
        assert_eq!(BoundExpr::Null.evaluate(&record).unwrap(), Value::Null);
        assert_eq!(
            BoundExpr::Integer(42).evaluate(&record).unwrap(),
            Value::Int64(42)
        );
        assert_eq!(
            BoundExpr::Boolean(true).evaluate(&record).unwrap(),
            Value::Boolean(true)
        );
    }

    #[test]
    fn test_bound_expr_evaluate_column() {
        let (record, _) = make_record(&[
            ("id", Value::Int64(1)),
            ("name", Value::Text("alice".into())),
        ]);
        assert_eq!(
            BoundExpr::Column(0).evaluate(&record).unwrap(),
            Value::Int64(1)
        );
        assert_eq!(
            BoundExpr::Column(1).evaluate(&record).unwrap(),
            Value::Text("alice".into())
        );
    }

    #[test]
    fn test_bound_expr_evaluate_column_out_of_bounds() {
        let record = Record::new(vec![Value::Int64(1)]);
        assert!(matches!(
            BoundExpr::Column(5).evaluate(&record),
            Err(ExecutorError::ColumnIndexOutOfBounds { index: 5, len: 1 })
        ));
    }

    #[test]
    fn test_bound_expr_evaluate_binary_op() {
        let record = Record::new(vec![Value::Int64(10)]);
        let expr = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Column(0)),
            op: BinaryOperator::Gt,
            right: Box::new(BoundExpr::Integer(5)),
        };
        assert_eq!(expr.evaluate(&record).unwrap(), Value::Boolean(true));
    }

    #[test]
    fn test_format_bound_expr_basic() {
        assert_eq!(format_bound_expr(&BoundExpr::Integer(42)), "42");
        assert_eq!(format_bound_expr(&BoundExpr::Column(0)), "$col0");
        assert_eq!(
            format_bound_expr(&BoundExpr::BinaryOp {
                left: Box::new(BoundExpr::Column(0)),
                op: BinaryOperator::Gt,
                right: Box::new(BoundExpr::Integer(5)),
            }),
            "($col0 > 5)"
        );
    }

    #[test]
    fn test_format_bound_expr_with_columns() {
        let cols = vec![
            ColumnDesc {
                name: "id".to_string(),
                table_oid: 0,
                column_id: 0,
                data_type: Type::Int8,
            },
            ColumnDesc {
                name: "name".to_string(),
                table_oid: 0,
                column_id: 0,
                data_type: Type::Text,
            },
        ];
        let expr = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Column(0)),
            op: BinaryOperator::Gt,
            right: Box::new(BoundExpr::Integer(5)),
        };
        assert_eq!(
            format_bound_expr_with_columns(&expr, &cols),
            "(id > 5)"
        );
    }
}
