//! Expression evaluator for SQL expressions.
//!
//! Evaluates [`BoundExpr`] nodes against a row of values, producing a single
//! [`Value`] result. Supports arithmetic, comparison, logical, string, NULL,
//! LIKE, CASE, and CAST operations.

use crate::datum::{CastError, Type, Value, WideNumeric, to_wide_numeric};
use crate::heap::Record;
use crate::sql::{BinaryOperator, UnaryOperator};

use super::error::ExecutorError;
use super::expr::BoundExpr;

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

            BoundExpr::Column { index, .. } => {
                if *index < record.values.len() {
                    Ok(record.values[*index].clone())
                } else {
                    Err(ExecutorError::ColumnIndexOutOfBounds {
                        index: *index,
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
                                ));
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
                        });
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
                v.cast(data_type).map_err(|(original, err)| match err {
                    CastError::Invalid => ExecutorError::InvalidCast {
                        from: match &original {
                            Value::Text(s) => format!("'{}'", s),
                            _ => original
                                .data_type()
                                .map_or("NULL", Type::display_name)
                                .to_string(),
                        },
                        to: data_type.display_name().to_string(),
                    },
                    CastError::NumericOutOfRange => ExecutorError::NumericOutOfRange {
                        type_name: data_type.display_name().to_string(),
                    },
                })
            }
        }
    }
}

/// Evaluates a binary operation.
fn eval_binary_op(left: &Value, op: BinaryOperator, right: &Value) -> Result<Value, ExecutorError> {
    match op {
        // Logical operators with 3-value NULL logic
        BinaryOperator::And => eval_and(left, right),
        BinaryOperator::Or => eval_or(left, right),

        // String concatenation (has its own NULL handling)
        BinaryOperator::Concat => eval_concat(left, right),

        // NULL propagation for all remaining operators
        _ if left.is_null() || right.is_null() => Ok(Value::Null),

        // Comparison operators
        BinaryOperator::Eq => Ok(Value::Boolean(
            compare_values(left, right)? == std::cmp::Ordering::Equal,
        )),
        BinaryOperator::Neq => Ok(Value::Boolean(
            compare_values(left, right)? != std::cmp::Ordering::Equal,
        )),
        BinaryOperator::Lt => Ok(Value::Boolean(
            compare_values(left, right)? == std::cmp::Ordering::Less,
        )),
        BinaryOperator::LtEq => Ok(Value::Boolean(
            compare_values(left, right)? != std::cmp::Ordering::Greater,
        )),
        BinaryOperator::Gt => Ok(Value::Boolean(
            compare_values(left, right)? == std::cmp::Ordering::Greater,
        )),
        BinaryOperator::GtEq => Ok(Value::Boolean(
            compare_values(left, right)? != std::cmp::Ordering::Less,
        )),

        BinaryOperator::Add => eval_arithmetic(
            left,
            right,
            |a, b| a.checked_add(b).ok_or(ExecutorError::IntegerOverflow),
            |a, b| Ok(a + b),
        ),
        BinaryOperator::Sub => eval_arithmetic(
            left,
            right,
            |a, b| a.checked_sub(b).ok_or(ExecutorError::IntegerOverflow),
            |a, b| Ok(a - b),
        ),
        BinaryOperator::Mul => eval_arithmetic(
            left,
            right,
            |a, b| a.checked_mul(b).ok_or(ExecutorError::IntegerOverflow),
            |a, b| Ok(a * b),
        ),
        BinaryOperator::Div => eval_arithmetic(
            left,
            right,
            |a, b| match b {
                0 => Err(ExecutorError::DivisionByZero),
                _ => Ok(a / b),
            },
            |a, b| {
                if b == 0.0 {
                    Err(ExecutorError::DivisionByZero)
                } else {
                    Ok(a / b)
                }
            },
        ),
        BinaryOperator::Mod => eval_arithmetic(
            left,
            right,
            |a, b| match b {
                0 => Err(ExecutorError::DivisionByZero),
                _ => Ok(a % b),
            },
            |a, b| {
                if b == 0.0 {
                    Err(ExecutorError::DivisionByZero)
                } else {
                    Ok(a % b)
                }
            },
        ),
    }
}

/// Converts a value to a nullable boolean, mapping type errors to [`ExecutorError::TypeMismatch`].
fn to_bool_or_type_error(v: &Value) -> Result<Option<bool>, ExecutorError> {
    v.to_bool_nullable().map_err(|()| ExecutorError::TypeMismatch {
        expected: "boolean".to_string(),
        found: v
            .data_type()
            .map_or("NULL", Type::display_name)
            .to_string(),
    })
}

/// Evaluates AND with 3-value NULL logic.
fn eval_and(left: &Value, right: &Value) -> Result<Value, ExecutorError> {
    match (to_bool_or_type_error(left)?, to_bool_or_type_error(right)?) {
        (Some(false), _) | (_, Some(false)) => Ok(Value::Boolean(false)),
        (Some(true), Some(true)) => Ok(Value::Boolean(true)),
        _ => Ok(Value::Null),
    }
}

/// Evaluates OR with 3-value NULL logic.
fn eval_or(left: &Value, right: &Value) -> Result<Value, ExecutorError> {
    match (to_bool_or_type_error(left)?, to_bool_or_type_error(right)?) {
        (Some(true), _) | (_, Some(true)) => Ok(Value::Boolean(true)),
        (Some(false), Some(false)) => Ok(Value::Boolean(false)),
        _ => Ok(Value::Null),
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

/// Evaluates an arithmetic operation by promoting operands to a common numeric type.
fn eval_arithmetic(
    left: &Value,
    right: &Value,
    int_op: impl FnOnce(i64, i64) -> Result<i64, ExecutorError>,
    float_op: impl FnOnce(f64, f64) -> Result<f64, ExecutorError>,
) -> Result<Value, ExecutorError> {
    match (to_wide_numeric(left), to_wide_numeric(right)) {
        (Some(WideNumeric::Int64(a)), Some(WideNumeric::Int64(b))) => {
            Ok(Value::Int64(int_op(a, b)?))
        }
        (Some(WideNumeric::Float64(a)), Some(WideNumeric::Float64(b))) => {
            Ok(Value::Float64(float_op(a, b)?))
        }
        (Some(WideNumeric::Float64(a)), Some(WideNumeric::Int64(b))) => {
            Ok(Value::Float64(float_op(a, b as f64)?))
        }
        (Some(WideNumeric::Int64(a)), Some(WideNumeric::Float64(b))) => {
            Ok(Value::Float64(float_op(a as f64, b)?))
        }
        _ => Err(ExecutorError::TypeMismatch {
            expected: "numeric".to_string(),
            found: format!(
                "{}, {}",
                left.data_type().map_or("NULL", Type::display_name),
                right.data_type().map_or("NULL", Type::display_name)
            ),
        }),
    }
}

/// Compares two values, returning their ordering.
///
/// Delegates to [`Value::partial_cmp`] and converts incomparable types to
/// a [`ExecutorError::TypeMismatch`] error.
fn compare_values(left: &Value, right: &Value) -> Result<std::cmp::Ordering, ExecutorError> {
    left.partial_cmp(right).ok_or_else(|| ExecutorError::TypeMismatch {
        expected: "comparable types".to_string(),
        found: format!(
            "{}, {}",
            left.data_type().map_or("NULL", Type::display_name),
            right.data_type().map_or("NULL", Type::display_name)
        ),
    })
}

/// Evaluates a unary operation.
fn eval_unary_op(op: UnaryOperator, val: &Value) -> Result<Value, ExecutorError> {
    if val.is_null() {
        return Ok(Value::Null);
    }
    let type_name = || {
        val.data_type()
            .map_or("NULL", Type::display_name)
            .to_string()
    };
    match op {
        UnaryOperator::Not => match val {
            Value::Boolean(b) => Ok(Value::Boolean(!b)),
            _ => Err(ExecutorError::TypeMismatch {
                expected: "boolean".to_string(),
                found: type_name(),
            }),
        },
        UnaryOperator::Minus => match val {
            Value::Int16(n) => Ok(Value::Int64(-(*n as i64))),
            Value::Int32(n) => Ok(Value::Int64(-(*n as i64))),
            Value::Int64(n) => n
                .checked_neg()
                .map(Value::Int64)
                .ok_or(ExecutorError::IntegerOverflow),
            Value::Float32(n) => Ok(Value::Float64(-(*n as f64))),
            Value::Float64(n) => Ok(Value::Float64(-n)),
            _ => Err(ExecutorError::TypeMismatch {
                expected: "numeric".to_string(),
                found: type_name(),
            }),
        },
        UnaryOperator::Plus => match val {
            Value::Int16(_)
            | Value::Int32(_)
            | Value::Int64(_)
            | Value::Float32(_)
            | Value::Float64(_) => Ok(val.clone()),
            _ => Err(ExecutorError::TypeMismatch {
                expected: "numeric".to_string(),
                found: type_name(),
            }),
        },
    }
}

/// LIKE pattern matching with support for % and _ wildcards.
///
/// NOTE: The recursive backtracking implementation has worst-case O(n*m)
/// complexity for patterns with multiple `%` wildcards (e.g., `%a%b%c%d%`).
/// Production systems compile patterns into NFAs for linear-time matching.
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
    use crate::sql::Parser;

    /// Parses, binds, and evaluates a SQL expression with no columns and an empty record.
    fn eval(sql: &str) -> Result<Value, ExecutorError> {
        let expr = Parser::new(sql).parse_expr().expect("parse error");
        let bound = expr.bind(&[]).expect("bind error");
        bound.evaluate(&Record::new(vec![]))
    }

    // ========================================================================
    // BoundExpr::evaluate – literal & column
    // ========================================================================

    #[test]
    fn test_evaluate_literals() {
        assert!(eval("NULL").unwrap().is_null());
        assert_eq!(eval("42").unwrap(), Value::Int64(42));
        assert_eq!(eval("TRUE").unwrap(), Value::Boolean(true));
    }

    #[test]
    fn test_evaluate_float_literal() {
        assert_eq!(eval("3.14").unwrap(), Value::Float64(3.14));
        assert_eq!(eval("0.0").unwrap(), Value::Float64(0.0));
    }

    #[test]
    fn test_evaluate_string_literal() {
        assert_eq!(eval("'hello'").unwrap(), Value::Text("hello".into()));
        assert_eq!(eval("''").unwrap(), Value::Text("".into()));
    }

    #[test]
    fn test_evaluate_column() {
        let record = Record::new(vec![Value::Int64(1), Value::Text("alice".into())]);
        assert_eq!(
            BoundExpr::Column {
                index: 0,
                name: None
            }
            .evaluate(&record)
            .unwrap(),
            Value::Int64(1)
        );
        assert_eq!(
            BoundExpr::Column {
                index: 1,
                name: Some("name".into())
            }
            .evaluate(&record)
            .unwrap(),
            Value::Text("alice".into())
        );
    }

    #[test]
    fn test_evaluate_column_out_of_bounds() {
        let record = Record::new(vec![Value::Int64(1)]);
        assert!(matches!(
            BoundExpr::Column {
                index: 5,
                name: None
            }
            .evaluate(&record),
            Err(ExecutorError::ColumnIndexOutOfBounds { index: 5, len: 1 })
        ));
    }

    // ========================================================================
    // eval_binary_op – AND / OR  (3-value NULL logic)
    // ========================================================================

    #[test]
    fn test_and_null_propagation() {
        // TRUE AND NULL = NULL
        assert!(eval("TRUE AND NULL").unwrap().is_null());
        // NULL AND TRUE = NULL
        assert!(eval("NULL AND TRUE").unwrap().is_null());
        // FALSE AND NULL = FALSE (short-circuit)
        assert_eq!(eval("FALSE AND NULL").unwrap(), Value::Boolean(false));
        // NULL AND FALSE = FALSE (short-circuit)
        assert_eq!(eval("NULL AND FALSE").unwrap(), Value::Boolean(false));
        // NULL AND NULL = NULL
        assert!(eval("NULL AND NULL").unwrap().is_null());
    }

    #[test]
    fn test_or_null_propagation() {
        // TRUE OR NULL = TRUE (short-circuit)
        assert_eq!(eval("TRUE OR NULL").unwrap(), Value::Boolean(true));
        // NULL OR TRUE = TRUE (short-circuit)
        assert_eq!(eval("NULL OR TRUE").unwrap(), Value::Boolean(true));
        // FALSE OR NULL = NULL
        assert!(eval("FALSE OR NULL").unwrap().is_null());
        // NULL OR FALSE = NULL
        assert!(eval("NULL OR FALSE").unwrap().is_null());
        // NULL OR NULL = NULL
        assert!(eval("NULL OR NULL").unwrap().is_null());
    }

    // ========================================================================
    // eval_binary_op – string concatenation (||)
    // ========================================================================

    #[test]
    fn test_concat_strings() {
        assert_eq!(
            eval("'hello' || ' ' || 'world'").unwrap(),
            Value::Text("hello world".into())
        );
        assert_eq!(eval("'' || 'a'").unwrap(), Value::Text("a".into()));
    }

    #[test]
    fn test_concat_type_coercion() {
        // Non-string values are converted via to_text()
        assert_eq!(eval("'id=' || 42").unwrap(), Value::Text("id=42".into()));
        assert_eq!(
            eval("'flag=' || TRUE").unwrap(),
            Value::Text("flag=t".into())
        );
    }

    #[test]
    fn test_concat_null_propagation() {
        // String concatenation with NULL returns NULL
        assert!(eval("'hello' || NULL").unwrap().is_null());
        assert!(eval("NULL || 'world'").unwrap().is_null());
    }

    // ========================================================================
    // eval_binary_op – comparison operators  (Eq, Neq, Lt, LtEq, Gt, GtEq)
    // ========================================================================

    #[test]
    fn test_comparison_operators() {
        // Eq
        assert_eq!(eval("5 = 5").unwrap(), Value::Boolean(true));
        assert_eq!(eval("5 = 6").unwrap(), Value::Boolean(false));
        // Neq
        assert_eq!(eval("5 <> 6").unwrap(), Value::Boolean(true));
        assert_eq!(eval("5 <> 5").unwrap(), Value::Boolean(false));
        // Lt
        assert_eq!(eval("3 < 5").unwrap(), Value::Boolean(true));
        assert_eq!(eval("5 < 5").unwrap(), Value::Boolean(false));
        // LtEq
        assert_eq!(eval("5 <= 5").unwrap(), Value::Boolean(true));
        assert_eq!(eval("6 <= 5").unwrap(), Value::Boolean(false));
        // Gt
        assert_eq!(eval("6 > 5").unwrap(), Value::Boolean(true));
        assert_eq!(eval("5 > 5").unwrap(), Value::Boolean(false));
        // GtEq
        assert_eq!(eval("5 >= 5").unwrap(), Value::Boolean(true));
        assert_eq!(eval("4 >= 5").unwrap(), Value::Boolean(false));
    }

    #[test]
    fn test_comparison_null_propagation() {
        // Any comparison with NULL returns NULL
        assert!(eval("1 = NULL").unwrap().is_null());
        assert!(eval("NULL < 1").unwrap().is_null());
        assert!(eval("NULL <> NULL").unwrap().is_null());
    }

    // ========================================================================
    // eval_binary_op – arithmetic  (Add, Sub, Mul, Div, Mod)
    // ========================================================================

    #[test]
    fn test_arithmetic_basic() {
        assert_eq!(eval("3 + 4").unwrap(), Value::Int64(7));
        assert_eq!(eval("10 - 3").unwrap(), Value::Int64(7));
        assert_eq!(eval("6 * 7").unwrap(), Value::Int64(42));
        assert_eq!(eval("15 / 4").unwrap(), Value::Int64(3));
        assert_eq!(eval("17 % 5").unwrap(), Value::Int64(2));
    }

    #[test]
    fn test_arithmetic_float() {
        assert_eq!(eval("1.5 + 2.5").unwrap(), Value::Float64(4.0));
        assert_eq!(eval("5.0 - 1.5").unwrap(), Value::Float64(3.5));
        assert_eq!(eval("2.0 * 3.0").unwrap(), Value::Float64(6.0));
        assert_eq!(eval("7.0 / 2.0").unwrap(), Value::Float64(3.5));
    }

    #[test]
    fn test_arithmetic_mixed_int_float() {
        // int + float promotes to float
        assert_eq!(eval("1 + 2.5").unwrap(), Value::Float64(3.5));
        assert_eq!(eval("2.5 + 1").unwrap(), Value::Float64(3.5));
        assert_eq!(eval("10 * 0.5").unwrap(), Value::Float64(5.0));
    }

    #[test]
    fn test_arithmetic_null_propagation() {
        // Any arithmetic with NULL returns NULL
        assert!(eval("1 + NULL").unwrap().is_null());
        assert!(eval("NULL * 2").unwrap().is_null());
    }

    #[test]
    fn test_integer_overflow() {
        assert!(matches!(
            eval("9223372036854775807 + 1"),
            Err(ExecutorError::IntegerOverflow)
        ));
        assert!(matches!(
            eval("-9223372036854775807 - 2"),
            Err(ExecutorError::IntegerOverflow)
        ));
        assert!(matches!(
            eval("9223372036854775807 * 2"),
            Err(ExecutorError::IntegerOverflow)
        ));
    }

    #[test]
    fn test_division_by_zero() {
        assert!(matches!(eval("1 / 0"), Err(ExecutorError::DivisionByZero)));
        assert!(matches!(eval("1 % 0"), Err(ExecutorError::DivisionByZero)));
        assert!(matches!(
            eval("1.0 / 0.0"),
            Err(ExecutorError::DivisionByZero)
        ));
    }

    // ========================================================================
    // eval_unary_op  (Not, Minus, Plus)
    // ========================================================================

    #[test]
    fn test_unary_not() {
        assert_eq!(eval("NOT TRUE").unwrap(), Value::Boolean(false));
        assert_eq!(eval("NOT FALSE").unwrap(), Value::Boolean(true));
        // NOT NULL = NULL
        assert!(eval("NOT NULL").unwrap().is_null());
    }

    #[test]
    fn test_unary_not_type_error() {
        assert!(matches!(
            eval("NOT 42"),
            Err(ExecutorError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn test_unary_minus() {
        assert_eq!(eval("-42").unwrap(), Value::Int64(-42));
        assert_eq!(eval("-3.14").unwrap(), Value::Float64(-3.14));
        // -NULL = NULL
        assert!(eval("-NULL").unwrap().is_null());
    }

    #[test]
    fn test_unary_minus_integer_overflow() {
        // -i64::MIN overflows because i64::MIN.abs() > i64::MAX
        let bound = BoundExpr::UnaryOp {
            op: UnaryOperator::Minus,
            operand: Box::new(BoundExpr::Integer(i64::MIN)),
        };
        assert!(matches!(
            bound.evaluate(&Record::new(vec![])),
            Err(ExecutorError::IntegerOverflow)
        ));
    }

    #[test]
    fn test_unary_minus_type_error() {
        assert!(matches!(
            eval("-'text'"),
            Err(ExecutorError::TypeMismatch { .. })
        ));
        assert!(matches!(
            eval("-TRUE"),
            Err(ExecutorError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn test_unary_plus() {
        assert_eq!(eval("+42").unwrap(), Value::Int64(42));
        assert_eq!(eval("+3.14").unwrap(), Value::Float64(3.14));
        // +NULL = NULL
        assert!(eval("+NULL").unwrap().is_null());
    }

    // ========================================================================
    // IS [NOT] NULL
    // ========================================================================

    #[test]
    fn test_is_null() {
        // NULL IS NULL = TRUE
        assert_eq!(eval("NULL IS NULL").unwrap(), Value::Boolean(true));
        // 1 IS NULL = FALSE
        assert_eq!(eval("1 IS NULL").unwrap(), Value::Boolean(false));
        // NULL IS NOT NULL = FALSE
        assert_eq!(eval("NULL IS NOT NULL").unwrap(), Value::Boolean(false));
    }

    // ========================================================================
    // [NOT] IN list
    // ========================================================================

    #[test]
    fn test_in_list() {
        assert_eq!(eval("1 IN (1, 2, 3)").unwrap(), Value::Boolean(true));
        assert_eq!(eval("4 IN (1, 2, 3)").unwrap(), Value::Boolean(false));
        assert_eq!(eval("'a' IN ('a', 'b')").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'c' IN ('a', 'b')").unwrap(), Value::Boolean(false));
    }

    #[test]
    fn test_not_in_list() {
        assert_eq!(eval("4 NOT IN (1, 2, 3)").unwrap(), Value::Boolean(true));
        assert_eq!(eval("1 NOT IN (1, 2, 3)").unwrap(), Value::Boolean(false));
    }

    #[test]
    fn test_in_list_null_propagation() {
        // NULL IN (1, 2) = NULL
        assert!(eval("NULL IN (1, 2)").unwrap().is_null());
        // 1 IN (1, NULL) = TRUE (found before NULL)
        assert_eq!(eval("1 IN (1, NULL)").unwrap(), Value::Boolean(true));
        // 3 IN (1, NULL) = NULL (not found, has NULL)
        assert!(eval("3 IN (1, NULL)").unwrap().is_null());
        // 3 NOT IN (1, 2) = TRUE (not found, no NULL)
        assert_eq!(eval("3 NOT IN (1, 2)").unwrap(), Value::Boolean(true));
        // 3 NOT IN (1, NULL) = NULL (not found, has NULL)
        assert!(eval("3 NOT IN (1, NULL)").unwrap().is_null());
    }

    // ========================================================================
    // [NOT] BETWEEN
    // ========================================================================

    #[test]
    fn test_between() {
        assert_eq!(eval("5 BETWEEN 1 AND 10").unwrap(), Value::Boolean(true));
        assert_eq!(eval("0 BETWEEN 1 AND 10").unwrap(), Value::Boolean(false));
        assert_eq!(eval("11 BETWEEN 1 AND 10").unwrap(), Value::Boolean(false));
        // Boundary values are inclusive
        assert_eq!(eval("1 BETWEEN 1 AND 10").unwrap(), Value::Boolean(true));
        assert_eq!(eval("10 BETWEEN 1 AND 10").unwrap(), Value::Boolean(true));
    }

    #[test]
    fn test_not_between() {
        assert_eq!(eval("5 NOT BETWEEN 1 AND 3").unwrap(), Value::Boolean(true));
        assert_eq!(
            eval("2 NOT BETWEEN 1 AND 3").unwrap(),
            Value::Boolean(false)
        );
    }

    #[test]
    fn test_between_strings() {
        assert_eq!(
            eval("'b' BETWEEN 'a' AND 'c'").unwrap(),
            Value::Boolean(true)
        );
        assert_eq!(
            eval("'z' BETWEEN 'a' AND 'c'").unwrap(),
            Value::Boolean(false)
        );
    }

    #[test]
    fn test_between_null_propagation() {
        // NULL BETWEEN 1 AND 10 = NULL
        assert!(eval("NULL BETWEEN 1 AND 10").unwrap().is_null());
        // 5 BETWEEN NULL AND 10 = NULL
        assert!(eval("5 BETWEEN NULL AND 10").unwrap().is_null());
        // 5 BETWEEN 1 AND NULL = NULL
        assert!(eval("5 BETWEEN 1 AND NULL").unwrap().is_null());
    }

    // ========================================================================
    // [NOT] LIKE / ILIKE  (like_match, like_match_recursive)
    // ========================================================================

    #[test]
    fn test_like_exact_match() {
        assert_eq!(eval("'hello' LIKE 'hello'").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'hello' LIKE 'world'").unwrap(), Value::Boolean(false));
    }

    #[test]
    fn test_like_percent_wildcard() {
        // % matches zero or more characters
        assert_eq!(eval("'hello' LIKE 'h%'").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'hello' LIKE '%lo'").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'hello' LIKE '%ell%'").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'hello' LIKE '%'").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'' LIKE '%'").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'hello' LIKE 'x%'").unwrap(), Value::Boolean(false));
    }

    #[test]
    fn test_like_underscore_wildcard() {
        // _ matches exactly one character
        assert_eq!(eval("'abc' LIKE 'a_c'").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'abc' LIKE '___'").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'ab' LIKE '___'").unwrap(), Value::Boolean(false));
        assert_eq!(eval("'abcd' LIKE '___'").unwrap(), Value::Boolean(false));
    }

    #[test]
    fn test_like_combined_wildcards() {
        assert_eq!(eval("'abcdef' LIKE 'a%f'").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'abcdef' LIKE '_b%e_'").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'a' LIKE '_%'").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'' LIKE '_%'").unwrap(), Value::Boolean(false));
    }

    #[test]
    fn test_like_empty_string() {
        assert_eq!(eval("'' LIKE ''").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'a' LIKE ''").unwrap(), Value::Boolean(false));
        assert_eq!(eval("'' LIKE 'a'").unwrap(), Value::Boolean(false));
    }

    #[test]
    fn test_not_like() {
        assert_eq!(
            eval("'hello' NOT LIKE 'world'").unwrap(),
            Value::Boolean(true)
        );
        assert_eq!(
            eval("'hello' NOT LIKE 'h%'").unwrap(),
            Value::Boolean(false)
        );
    }

    #[test]
    fn test_ilike() {
        assert_eq!(eval("'Hello' ILIKE 'hello'").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'HELLO' ILIKE 'h%'").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'ABC' ILIKE '%b%'").unwrap(), Value::Boolean(true));
        assert_eq!(eval("'ABC' ILIKE 'x%'").unwrap(), Value::Boolean(false));
    }

    #[test]
    fn test_like_escape() {
        // Escape the % wildcard so it matches a literal %
        assert_eq!(
            eval(r"'100%' LIKE '100\%' ESCAPE '\'").unwrap(),
            Value::Boolean(true)
        );
        assert_eq!(
            eval(r"'100x' LIKE '100\%' ESCAPE '\'").unwrap(),
            Value::Boolean(false)
        );
        // Escape the _ wildcard
        assert_eq!(
            eval(r"'a_b' LIKE 'a\_b' ESCAPE '\'").unwrap(),
            Value::Boolean(true)
        );
        assert_eq!(
            eval(r"'axb' LIKE 'a\_b' ESCAPE '\'").unwrap(),
            Value::Boolean(false)
        );
    }

    #[test]
    fn test_like_null_propagation() {
        // NULL LIKE '%' = NULL
        assert!(eval("NULL LIKE '%'").unwrap().is_null());
        // 'abc' LIKE NULL = NULL
        assert!(eval("'abc' LIKE NULL").unwrap().is_null());
    }

    // ========================================================================
    // CASE expression  (searched & simple)
    // ========================================================================

    #[test]
    fn test_searched_case() {
        assert_eq!(
            eval("CASE WHEN TRUE THEN 'yes' ELSE 'no' END").unwrap(),
            Value::Text("yes".into())
        );
        assert_eq!(
            eval("CASE WHEN FALSE THEN 'yes' ELSE 'no' END").unwrap(),
            Value::Text("no".into())
        );
    }

    #[test]
    fn test_searched_case_multiple_when() {
        assert_eq!(
            eval("CASE WHEN FALSE THEN 'a' WHEN TRUE THEN 'b' ELSE 'c' END").unwrap(),
            Value::Text("b".into())
        );
        // First match wins
        assert_eq!(
            eval("CASE WHEN TRUE THEN 'first' WHEN TRUE THEN 'second' END").unwrap(),
            Value::Text("first".into())
        );
    }

    #[test]
    fn test_searched_case_no_else() {
        // No ELSE and no match → NULL
        assert!(eval("CASE WHEN FALSE THEN 'a' END").unwrap().is_null());
    }

    #[test]
    fn test_searched_case_null_condition() {
        // NULL condition is not true
        assert_eq!(
            eval("CASE WHEN NULL THEN 'a' ELSE 'b' END").unwrap(),
            Value::Text("b".into())
        );
    }

    #[test]
    fn test_simple_case() {
        assert_eq!(
            eval("CASE 1 WHEN 1 THEN 'one' WHEN 2 THEN 'two' ELSE 'other' END").unwrap(),
            Value::Text("one".into())
        );
        assert_eq!(
            eval("CASE 2 WHEN 1 THEN 'one' WHEN 2 THEN 'two' ELSE 'other' END").unwrap(),
            Value::Text("two".into())
        );
        assert_eq!(
            eval("CASE 3 WHEN 1 THEN 'one' WHEN 2 THEN 'two' ELSE 'other' END").unwrap(),
            Value::Text("other".into())
        );
    }

    #[test]
    fn test_simple_case_no_match_no_else() {
        assert!(eval("CASE 99 WHEN 1 THEN 'one' END").unwrap().is_null());
    }

    #[test]
    fn test_simple_case_null_operand() {
        // NULL operand never matches (NULL != anything)
        assert_eq!(
            eval("CASE NULL WHEN 1 THEN 'a' ELSE 'b' END").unwrap(),
            Value::Text("b".into())
        );
    }

    #[test]
    fn test_simple_case_null_when_value() {
        // NULL in WHEN value never matches
        assert_eq!(
            eval("CASE 1 WHEN NULL THEN 'a' ELSE 'b' END").unwrap(),
            Value::Text("b".into())
        );
    }

}
