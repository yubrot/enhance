//! Expression evaluator for SQL expressions.
//!
//! Evaluates [`BoundExpr`] nodes against a row of values, producing a single
//! [`Value`] result. Supports arithmetic, comparison, logical, string, NULL,
//! LIKE, CASE, and CAST operations.

use crate::datum::{Type, Value};
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
                eval_cast(v, data_type)
            }
        }
    }
}

/// Evaluates a binary operation.
fn eval_binary_op(left: &Value, op: BinaryOperator, right: &Value) -> Result<Value, ExecutorError> {
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
                BinaryOperator::Add => a
                    .checked_add(*b)
                    .ok_or(ExecutorError::Unsupported("integer overflow".to_string()))?,
                BinaryOperator::Sub => a
                    .checked_sub(*b)
                    .ok_or(ExecutorError::Unsupported("integer overflow".to_string()))?,
                BinaryOperator::Mul => a
                    .checked_mul(*b)
                    .ok_or(ExecutorError::Unsupported("integer overflow".to_string()))?,
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
/// Float ordering: NaN is greater than all non-NaN values; NaN == NaN.
fn compare_values(left: &Value, right: &Value) -> Result<std::cmp::Ordering, ExecutorError> {
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
                (Value::Float64(a), Value::Float64(b)) => Ok(compare_f64(*a, *b)),
                (Value::Float64(a), Value::Int64(b)) => Ok(compare_f64(*a, *b as f64)),
                (Value::Int64(a), Value::Float64(b)) => Ok(compare_f64(*a as f64, *b)),
                _ => Err(ExecutorError::TypeMismatch {
                    expected: "comparable types".to_string(),
                    found: format!("{}, {}", value_type_name(left), value_type_name(right)),
                }),
            }
        }
    }
}

/// Compares two f64 values with NaN-aware total ordering.
///
/// NaN is treated as greater than all non-NaN values, and NaN == NaN.
fn compare_f64(a: f64, b: f64) -> std::cmp::Ordering {
    match a.partial_cmp(&b) {
        Some(ord) => ord,
        None => match (a.is_nan(), b.is_nan()) {
            (true, true) => std::cmp::Ordering::Equal,
            (true, false) => std::cmp::Ordering::Greater,
            (false, true) => std::cmp::Ordering::Less,
            (false, false) => unreachable!(),
        },
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
            Value::Int16(_)
            | Value::Int32(_)
            | Value::Int64(_)
            | Value::Float32(_)
            | Value::Float64(_) => Ok(val.clone()),
            _ => Err(ExecutorError::TypeMismatch {
                expected: "numeric".to_string(),
                found: value_type_name(val),
            }),
        },
    }
}

/// Evaluates a type cast (CAST(expr AS type)).
fn eval_cast(v: Value, target: &Type) -> Result<Value, ExecutorError> {
    if v.is_null() {
        return Ok(Value::Null);
    }
    match target {
        Type::Bool => match &v {
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
        Type::Int2 => {
            match &v {
                Value::Int16(_) => Ok(v),
                Value::Int32(n) => Ok(Value::Int16(*n as i16)),
                Value::Int64(n) => Ok(Value::Int16(*n as i16)),
                Value::Float32(n) => Ok(Value::Int16(*n as i16)),
                Value::Float64(n) => Ok(Value::Int16(*n as i16)),
                Value::Text(s) => s.trim().parse::<i16>().map(Value::Int16).map_err(|_| {
                    ExecutorError::InvalidCast {
                        from: format!("'{}'", s),
                        to: "smallint".to_string(),
                    }
                }),
                Value::Boolean(b) => Ok(Value::Int16(if *b { 1 } else { 0 })),
                _ => Err(ExecutorError::InvalidCast {
                    from: value_type_name(&v),
                    to: "smallint".to_string(),
                }),
            }
        }
        Type::Int4 => {
            match &v {
                Value::Int32(_) => Ok(v),
                Value::Int16(n) => Ok(Value::Int32(*n as i32)),
                Value::Int64(n) => Ok(Value::Int32(*n as i32)),
                Value::Float32(n) => Ok(Value::Int32(*n as i32)),
                Value::Float64(n) => Ok(Value::Int32(*n as i32)),
                Value::Text(s) => s.trim().parse::<i32>().map(Value::Int32).map_err(|_| {
                    ExecutorError::InvalidCast {
                        from: format!("'{}'", s),
                        to: "integer".to_string(),
                    }
                }),
                Value::Boolean(b) => Ok(Value::Int32(if *b { 1 } else { 0 })),
                _ => Err(ExecutorError::InvalidCast {
                    from: value_type_name(&v),
                    to: "integer".to_string(),
                }),
            }
        }
        Type::Int8 => {
            match &v {
                Value::Int64(_) => Ok(v),
                Value::Int16(n) => Ok(Value::Int64(*n as i64)),
                Value::Int32(n) => Ok(Value::Int64(*n as i64)),
                Value::Float32(n) => Ok(Value::Int64(*n as i64)),
                Value::Float64(n) => Ok(Value::Int64(*n as i64)),
                Value::Text(s) => s.trim().parse::<i64>().map(Value::Int64).map_err(|_| {
                    ExecutorError::InvalidCast {
                        from: format!("'{}'", s),
                        to: "bigint".to_string(),
                    }
                }),
                Value::Boolean(b) => Ok(Value::Int64(if *b { 1 } else { 0 })),
                _ => Err(ExecutorError::InvalidCast {
                    from: value_type_name(&v),
                    to: "bigint".to_string(),
                }),
            }
        }
        Type::Float4 => match &v {
            Value::Float32(_) => Ok(v),
            Value::Float64(n) => Ok(Value::Float32(*n as f32)),
            Value::Int16(n) => Ok(Value::Float32(*n as f32)),
            Value::Int32(n) => Ok(Value::Float32(*n as f32)),
            Value::Int64(n) => Ok(Value::Float32(*n as f32)),
            Value::Text(s) => s.trim().parse::<f32>().map(Value::Float32).map_err(|_| {
                ExecutorError::InvalidCast {
                    from: format!("'{}'", s),
                    to: "real".to_string(),
                }
            }),
            _ => Err(ExecutorError::InvalidCast {
                from: value_type_name(&v),
                to: "real".to_string(),
            }),
        },
        Type::Float8 => match &v {
            Value::Float64(_) => Ok(v),
            Value::Float32(n) => Ok(Value::Float64(*n as f64)),
            Value::Int16(n) => Ok(Value::Float64(*n as f64)),
            Value::Int32(n) => Ok(Value::Float64(*n as f64)),
            Value::Int64(n) => Ok(Value::Float64(*n as f64)),
            Value::Text(s) => s.trim().parse::<f64>().map(Value::Float64).map_err(|_| {
                ExecutorError::InvalidCast {
                    from: format!("'{}'", s),
                    to: "double precision".to_string(),
                }
            }),
            _ => Err(ExecutorError::InvalidCast {
                from: value_type_name(&v),
                to: "double precision".to_string(),
            }),
        },
        Type::Text | Type::Varchar | Type::Bpchar => Ok(Value::Text(v.to_text())),
        Type::Bytea => match &v {
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

    // --- BoundExpr tests ---

    fn make_record(cols: &[(&str, Value)]) -> Record {
        let values: Vec<Value> = cols.iter().map(|(_, v)| v.clone()).collect();
        Record::new(values)
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
        let record = make_record(&[
            ("id", Value::Int64(1)),
            ("name", Value::Text("alice".into())),
        ]);
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
    fn test_bound_expr_evaluate_column_out_of_bounds() {
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

    #[test]
    fn test_bound_expr_evaluate_binary_op() {
        let record = Record::new(vec![Value::Int64(10)]);
        let expr = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Column {
                index: 0,
                name: None,
            }),
            op: BinaryOperator::Gt,
            right: Box::new(BoundExpr::Integer(5)),
        };
        assert_eq!(expr.evaluate(&record).unwrap(), Value::Boolean(true));
    }

    // --- 3-value NULL logic tests ---

    fn eval_binop(left: Value, op: BinaryOperator, right: Value) -> Result<Value, ExecutorError> {
        eval_binary_op(&left, op, &right)
    }

    #[test]
    fn test_and_null_propagation() {
        // TRUE AND NULL = NULL
        assert_eq!(
            eval_binop(Value::Boolean(true), BinaryOperator::And, Value::Null).unwrap(),
            Value::Null
        );
        // NULL AND TRUE = NULL
        assert_eq!(
            eval_binop(Value::Null, BinaryOperator::And, Value::Boolean(true)).unwrap(),
            Value::Null
        );
        // FALSE AND NULL = FALSE (short-circuit)
        assert_eq!(
            eval_binop(Value::Boolean(false), BinaryOperator::And, Value::Null).unwrap(),
            Value::Boolean(false)
        );
        // NULL AND FALSE = FALSE (short-circuit)
        assert_eq!(
            eval_binop(Value::Null, BinaryOperator::And, Value::Boolean(false)).unwrap(),
            Value::Boolean(false)
        );
        // NULL AND NULL = NULL
        assert_eq!(
            eval_binop(Value::Null, BinaryOperator::And, Value::Null).unwrap(),
            Value::Null
        );
    }

    #[test]
    fn test_or_null_propagation() {
        // TRUE OR NULL = TRUE (short-circuit)
        assert_eq!(
            eval_binop(Value::Boolean(true), BinaryOperator::Or, Value::Null).unwrap(),
            Value::Boolean(true)
        );
        // NULL OR TRUE = TRUE (short-circuit)
        assert_eq!(
            eval_binop(Value::Null, BinaryOperator::Or, Value::Boolean(true)).unwrap(),
            Value::Boolean(true)
        );
        // FALSE OR NULL = NULL
        assert_eq!(
            eval_binop(Value::Boolean(false), BinaryOperator::Or, Value::Null).unwrap(),
            Value::Null
        );
        // NULL OR FALSE = NULL
        assert_eq!(
            eval_binop(Value::Null, BinaryOperator::Or, Value::Boolean(false)).unwrap(),
            Value::Null
        );
        // NULL OR NULL = NULL
        assert_eq!(
            eval_binop(Value::Null, BinaryOperator::Or, Value::Null).unwrap(),
            Value::Null
        );
    }

    #[test]
    fn test_comparison_null_propagation() {
        // Any comparison with NULL returns NULL
        assert_eq!(
            eval_binop(Value::Int64(1), BinaryOperator::Eq, Value::Null).unwrap(),
            Value::Null
        );
        assert_eq!(
            eval_binop(Value::Null, BinaryOperator::Lt, Value::Int64(1)).unwrap(),
            Value::Null
        );
        assert_eq!(
            eval_binop(Value::Null, BinaryOperator::Neq, Value::Null).unwrap(),
            Value::Null
        );
    }

    #[test]
    fn test_in_list_null_propagation() {
        let record = Record::new(vec![]);
        // NULL IN (1, 2) = NULL
        let expr = BoundExpr::InList {
            expr: Box::new(BoundExpr::Null),
            list: vec![BoundExpr::Integer(1), BoundExpr::Integer(2)],
            negated: false,
        };
        assert_eq!(expr.evaluate(&record).unwrap(), Value::Null);

        // 1 IN (1, NULL) = TRUE (found before NULL)
        let expr = BoundExpr::InList {
            expr: Box::new(BoundExpr::Integer(1)),
            list: vec![BoundExpr::Integer(1), BoundExpr::Null],
            negated: false,
        };
        assert_eq!(expr.evaluate(&record).unwrap(), Value::Boolean(true));

        // 3 IN (1, NULL) = NULL (not found, has NULL)
        let expr = BoundExpr::InList {
            expr: Box::new(BoundExpr::Integer(3)),
            list: vec![BoundExpr::Integer(1), BoundExpr::Null],
            negated: false,
        };
        assert_eq!(expr.evaluate(&record).unwrap(), Value::Null);

        // 3 NOT IN (1, 2) = TRUE (not found, no NULL)
        let expr = BoundExpr::InList {
            expr: Box::new(BoundExpr::Integer(3)),
            list: vec![BoundExpr::Integer(1), BoundExpr::Integer(2)],
            negated: true,
        };
        assert_eq!(expr.evaluate(&record).unwrap(), Value::Boolean(true));

        // 3 NOT IN (1, NULL) = NULL (not found, has NULL)
        let expr = BoundExpr::InList {
            expr: Box::new(BoundExpr::Integer(3)),
            list: vec![BoundExpr::Integer(1), BoundExpr::Null],
            negated: true,
        };
        assert_eq!(expr.evaluate(&record).unwrap(), Value::Null);
    }

    #[test]
    fn test_between_null_propagation() {
        let record = Record::new(vec![]);
        // NULL BETWEEN 1 AND 10 = NULL
        let expr = BoundExpr::Between {
            expr: Box::new(BoundExpr::Null),
            low: Box::new(BoundExpr::Integer(1)),
            high: Box::new(BoundExpr::Integer(10)),
            negated: false,
        };
        assert_eq!(expr.evaluate(&record).unwrap(), Value::Null);

        // 5 BETWEEN NULL AND 10 = NULL
        let expr = BoundExpr::Between {
            expr: Box::new(BoundExpr::Integer(5)),
            low: Box::new(BoundExpr::Null),
            high: Box::new(BoundExpr::Integer(10)),
            negated: false,
        };
        assert_eq!(expr.evaluate(&record).unwrap(), Value::Null);

        // 5 BETWEEN 1 AND NULL = NULL
        let expr = BoundExpr::Between {
            expr: Box::new(BoundExpr::Integer(5)),
            low: Box::new(BoundExpr::Integer(1)),
            high: Box::new(BoundExpr::Null),
            negated: false,
        };
        assert_eq!(expr.evaluate(&record).unwrap(), Value::Null);
    }

    #[test]
    fn test_is_null_expr() {
        let record = Record::new(vec![]);
        // NULL IS NULL = TRUE
        let expr = BoundExpr::IsNull {
            expr: Box::new(BoundExpr::Null),
            negated: false,
        };
        assert_eq!(expr.evaluate(&record).unwrap(), Value::Boolean(true));

        // 1 IS NULL = FALSE
        let expr = BoundExpr::IsNull {
            expr: Box::new(BoundExpr::Integer(1)),
            negated: false,
        };
        assert_eq!(expr.evaluate(&record).unwrap(), Value::Boolean(false));

        // NULL IS NOT NULL = FALSE
        let expr = BoundExpr::IsNull {
            expr: Box::new(BoundExpr::Null),
            negated: true,
        };
        assert_eq!(expr.evaluate(&record).unwrap(), Value::Boolean(false));
    }

    // --- Cast boundary tests ---

    #[test]
    fn test_cast_int64_to_int16_truncation() {
        // Large Int64 value truncates when cast to Int16
        let result = eval_cast(Value::Int64(70000), &Type::Int2).unwrap();
        // 70000 = 0x11170, truncated to i16 = 0x1170 = 4464
        assert!(matches!(result, Value::Int16(_)));
    }

    #[test]
    fn test_cast_float_to_int_truncation() {
        // Float truncates toward zero
        let result = eval_cast(Value::Float64(3.9), &Type::Int8).unwrap();
        assert_eq!(result, Value::Int64(3));

        let result = eval_cast(Value::Float64(-3.9), &Type::Int8).unwrap();
        assert_eq!(result, Value::Int64(-3));
    }

    #[test]
    fn test_cast_text_to_numeric() {
        assert_eq!(
            eval_cast(Value::Text("42".into()), &Type::Int4).unwrap(),
            Value::Int32(42)
        );
        assert_eq!(
            eval_cast(Value::Text(" -7 ".into()), &Type::Int8).unwrap(),
            Value::Int64(-7)
        );
        assert_eq!(
            eval_cast(Value::Text("3.14".into()), &Type::Float8).unwrap(),
            Value::Float64(3.14)
        );
    }

    #[test]
    fn test_cast_text_to_numeric_invalid() {
        assert!(matches!(
            eval_cast(Value::Text("abc".into()), &Type::Int4),
            Err(ExecutorError::InvalidCast { .. })
        ));
        assert!(matches!(
            eval_cast(Value::Text("".into()), &Type::Int8),
            Err(ExecutorError::InvalidCast { .. })
        ));
    }

    #[test]
    fn test_cast_null_passthrough() {
        // CAST(NULL AS <any type>) = NULL
        for ty in [
            Type::Bool,
            Type::Int2,
            Type::Int4,
            Type::Int8,
            Type::Float4,
            Type::Float8,
            Type::Text,
        ] {
            assert_eq!(eval_cast(Value::Null, &ty).unwrap(), Value::Null);
        }
    }

    #[test]
    fn test_cast_bool_from_text() {
        for (input, expected) in [
            ("true", true),
            ("t", true),
            ("yes", true),
            ("1", true),
            ("on", true),
            ("false", false),
            ("f", false),
            ("no", false),
            ("0", false),
            ("off", false),
        ] {
            assert_eq!(
                eval_cast(Value::Text(input.into()), &Type::Bool).unwrap(),
                Value::Boolean(expected),
                "CAST('{}' AS BOOL)",
                input
            );
        }
    }

    #[test]
    fn test_arithmetic_null_propagation() {
        // Any arithmetic with NULL returns NULL
        assert_eq!(
            eval_binop(Value::Int64(1), BinaryOperator::Add, Value::Null).unwrap(),
            Value::Null
        );
        assert_eq!(
            eval_binop(Value::Null, BinaryOperator::Mul, Value::Int64(2)).unwrap(),
            Value::Null
        );
    }

    #[test]
    fn test_concat_null_propagation() {
        // String concatenation with NULL returns NULL
        assert_eq!(
            eval_binop(
                Value::Text("hello".into()),
                BinaryOperator::Concat,
                Value::Null
            )
            .unwrap(),
            Value::Null
        );
        assert_eq!(
            eval_binop(
                Value::Null,
                BinaryOperator::Concat,
                Value::Text("world".into())
            )
            .unwrap(),
            Value::Null
        );
    }

    #[test]
    fn test_like_null_propagation() {
        let record = Record::new(vec![]);
        // NULL LIKE '%' = NULL
        let expr = BoundExpr::Like {
            expr: Box::new(BoundExpr::Null),
            pattern: Box::new(BoundExpr::String("%".into())),
            escape: None,
            negated: false,
            case_insensitive: false,
        };
        assert_eq!(expr.evaluate(&record).unwrap(), Value::Null);

        // 'abc' LIKE NULL = NULL
        let expr = BoundExpr::Like {
            expr: Box::new(BoundExpr::String("abc".into())),
            pattern: Box::new(BoundExpr::Null),
            escape: None,
            negated: false,
            case_insensitive: false,
        };
        assert_eq!(expr.evaluate(&record).unwrap(), Value::Null);
    }

    #[test]
    fn test_integer_overflow() {
        assert!(matches!(
            eval_binop(Value::Int64(i64::MAX), BinaryOperator::Add, Value::Int64(1)),
            Err(ExecutorError::Unsupported(_))
        ));
        assert!(matches!(
            eval_binop(Value::Int64(i64::MIN), BinaryOperator::Sub, Value::Int64(1)),
            Err(ExecutorError::Unsupported(_))
        ));
        assert!(matches!(
            eval_binop(Value::Int64(i64::MAX), BinaryOperator::Mul, Value::Int64(2)),
            Err(ExecutorError::Unsupported(_))
        ));
    }

    #[test]
    fn test_division_by_zero() {
        assert!(matches!(
            eval_binop(Value::Int64(1), BinaryOperator::Div, Value::Int64(0)),
            Err(ExecutorError::DivisionByZero)
        ));
        assert!(matches!(
            eval_binop(Value::Int64(1), BinaryOperator::Mod, Value::Int64(0)),
            Err(ExecutorError::DivisionByZero)
        ));
        assert!(matches!(
            eval_binop(Value::Float64(1.0), BinaryOperator::Div, Value::Float64(0.0)),
            Err(ExecutorError::DivisionByZero)
        ));
    }

    // --- NaN ordering tests ---

    #[test]
    fn test_compare_f64_nan_ordering() {
        use std::cmp::Ordering;

        // NaN > any non-NaN value
        assert_eq!(compare_f64(f64::NAN, 0.0), Ordering::Greater);
        assert_eq!(compare_f64(f64::NAN, f64::INFINITY), Ordering::Greater);
        assert_eq!(compare_f64(f64::NAN, f64::NEG_INFINITY), Ordering::Greater);

        // any non-NaN value < NaN
        assert_eq!(compare_f64(0.0, f64::NAN), Ordering::Less);
        assert_eq!(compare_f64(f64::INFINITY, f64::NAN), Ordering::Less);
        assert_eq!(compare_f64(f64::NEG_INFINITY, f64::NAN), Ordering::Less);

        // NaN == NaN
        assert_eq!(compare_f64(f64::NAN, f64::NAN), Ordering::Equal);

        // Normal comparisons still work
        assert_eq!(compare_f64(1.0, 2.0), Ordering::Less);
        assert_eq!(compare_f64(2.0, 1.0), Ordering::Greater);
        assert_eq!(compare_f64(1.0, 1.0), Ordering::Equal);
    }

    #[test]
    fn test_compare_values_nan_ordering() {
        use std::cmp::Ordering;

        // NaN > regular float
        assert_eq!(
            compare_values(&Value::Float64(f64::NAN), &Value::Float64(1.0)).unwrap(),
            Ordering::Greater
        );
        // regular float < NaN
        assert_eq!(
            compare_values(&Value::Float64(1.0), &Value::Float64(f64::NAN)).unwrap(),
            Ordering::Less
        );
        // NaN == NaN
        assert_eq!(
            compare_values(&Value::Float64(f64::NAN), &Value::Float64(f64::NAN)).unwrap(),
            Ordering::Equal
        );

        // NaN > integer (cross-type comparison via promotion)
        assert_eq!(
            compare_values(&Value::Float64(f64::NAN), &Value::Int64(100)).unwrap(),
            Ordering::Greater
        );
        assert_eq!(
            compare_values(&Value::Int64(100), &Value::Float64(f64::NAN)).unwrap(),
            Ordering::Less
        );
    }
}
