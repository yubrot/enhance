//! Expression evaluation for query execution.
//!
//! This module implements SQL expression evaluation with proper NULL handling
//! following SQL's three-valued logic.

use crate::catalog::ColumnInfo;
use crate::executor::ExecutorError;
use crate::heap::Value;
use crate::sql::{BinaryOperator, Expr, UnaryOperator};

/// Evaluates an expression against a tuple.
///
/// # Arguments
///
/// * `expr` - The expression to evaluate.
/// * `tuple` - The current tuple values.
/// * `columns` - Column metadata for resolving column references.
///
/// # Errors
///
/// Returns an error if a column is not found or an operation is invalid.
pub fn evaluate(
    expr: &Expr,
    tuple: &[Value],
    columns: &[ColumnInfo],
) -> Result<Value, ExecutorError> {
    match expr {
        // Literals
        Expr::Null => Ok(Value::Null),
        Expr::Boolean(b) => Ok(Value::Boolean(*b)),
        Expr::Integer(n) => {
            // Fit into smallest type
            if *n >= i32::MIN as i64 && *n <= i32::MAX as i64 {
                Ok(Value::Int32(*n as i32))
            } else {
                Ok(Value::Int64(*n))
            }
        }
        Expr::Float(f) => Ok(Value::Float64(*f)),
        Expr::String(s) => Ok(Value::Text(s.clone())),

        // Column reference
        Expr::ColumnRef { table, column } => {
            resolve_column(table.as_deref(), column, tuple, columns)
        }

        // Binary operations
        Expr::BinaryOp { left, op, right } => {
            let left_val = evaluate(left, tuple, columns)?;
            let right_val = evaluate(right, tuple, columns)?;
            eval_binary_op(&left_val, op, &right_val)
        }

        // Unary operations
        Expr::UnaryOp { op, operand } => {
            let val = evaluate(operand, tuple, columns)?;
            eval_unary_op(op, &val)
        }

        // IS NULL / IS NOT NULL
        Expr::IsNull { expr, negated } => {
            let val = evaluate(expr, tuple, columns)?;
            let is_null = val.is_null();
            Ok(Value::Boolean(if *negated { !is_null } else { is_null }))
        }

        // Parameters not supported yet (Step 11 with DML)
        Expr::Parameter(_) => Err(ExecutorError::Unsupported {
            feature: "parameters".to_string(),
        }),

        // Subqueries not supported yet (Step 19)
        Expr::Subquery(_) | Expr::Exists { .. } | Expr::InSubquery { .. } => {
            Err(ExecutorError::Unsupported {
                feature: "subqueries".to_string(),
            })
        }

        // BETWEEN: expr BETWEEN low AND high -> expr >= low AND expr <= high
        Expr::Between {
            expr: e,
            low,
            high,
            negated,
        } => {
            let val = evaluate(e, tuple, columns)?;
            let low_val = evaluate(low, tuple, columns)?;
            let high_val = evaluate(high, tuple, columns)?;

            let ge_low = eval_binary_op(&val, &BinaryOperator::GtEq, &low_val)?;
            let le_high = eval_binary_op(&val, &BinaryOperator::LtEq, &high_val)?;
            let result = eval_binary_op(&ge_low, &BinaryOperator::And, &le_high)?;

            if *negated {
                eval_unary_op(&UnaryOperator::Not, &result)
            } else {
                Ok(result)
            }
        }

        // IN list: expr IN (v1, v2, ...)
        Expr::InList {
            expr: e,
            list,
            negated,
        } => {
            let val = evaluate(e, tuple, columns)?;
            if val.is_null() {
                return Ok(Value::Null);
            }

            let mut has_null = false;
            for item in list {
                let item_val = evaluate(item, tuple, columns)?;
                if item_val.is_null() {
                    has_null = true;
                    continue;
                }
                let eq = eval_binary_op(&val, &BinaryOperator::Eq, &item_val)?;
                if matches!(eq, Value::Boolean(true)) {
                    return Ok(Value::Boolean(!*negated));
                }
            }

            // Not found: if we saw NULLs, result is NULL; otherwise FALSE
            if has_null {
                Ok(Value::Null)
            } else {
                Ok(Value::Boolean(*negated))
            }
        }

        // LIKE not supported yet
        Expr::Like { .. } => Err(ExecutorError::Unsupported {
            feature: "LIKE".to_string(),
        }),

        // CASE not supported yet
        Expr::Case { .. } => Err(ExecutorError::Unsupported {
            feature: "CASE".to_string(),
        }),

        // CAST not supported yet
        Expr::Cast { .. } => Err(ExecutorError::Unsupported {
            feature: "CAST".to_string(),
        }),

        // Functions not supported yet (Step 12)
        Expr::Function { .. } => Err(ExecutorError::Unsupported {
            feature: "functions".to_string(),
        }),
    }
}

/// Resolves a column reference to its value in the tuple.
fn resolve_column(
    table: Option<&str>,
    column: &str,
    tuple: &[Value],
    columns: &[ColumnInfo],
) -> Result<Value, ExecutorError> {
    // Find matching column(s)
    let matches: Vec<(usize, &ColumnInfo)> = columns
        .iter()
        .enumerate()
        .filter(|(_, col)| {
            // Match column name
            if col.column_name != column {
                return false;
            }
            // If table qualifier is given, we can't check it here
            // (would need table name in ColumnInfo, deferred to planner)
            let _ = table;
            true
        })
        .collect();

    match matches.len() {
        0 => Err(ExecutorError::ColumnNotFound {
            name: column.to_string(),
        }),
        1 => {
            let (idx, _) = matches[0];
            Ok(tuple.get(idx).cloned().unwrap_or(Value::Null))
        }
        _ => {
            // For now, if there's ambiguity, take the first match
            // Real implementation would need table qualifier support
            let (idx, _) = matches[0];
            Ok(tuple.get(idx).cloned().unwrap_or(Value::Null))
        }
    }
}

/// Evaluates a binary operation with SQL NULL semantics.
fn eval_binary_op(
    left: &Value,
    op: &BinaryOperator,
    right: &Value,
) -> Result<Value, ExecutorError> {
    // Handle NULL propagation for most operators
    // Exceptions: AND, OR have special NULL handling
    match op {
        BinaryOperator::And => return eval_and(left, right),
        BinaryOperator::Or => return eval_or(left, right),
        _ => {}
    }

    // For all other operators, NULL propagates
    if left.is_null() || right.is_null() {
        return Ok(Value::Null);
    }

    match op {
        // Comparison operators
        BinaryOperator::Eq => eval_comparison(left, right, |ord| ord == std::cmp::Ordering::Equal),
        BinaryOperator::Neq => {
            eval_comparison(left, right, |ord| ord != std::cmp::Ordering::Equal)
        }
        BinaryOperator::Lt => eval_comparison(left, right, |ord| ord == std::cmp::Ordering::Less),
        BinaryOperator::LtEq => {
            eval_comparison(left, right, |ord| ord != std::cmp::Ordering::Greater)
        }
        BinaryOperator::Gt => {
            eval_comparison(left, right, |ord| ord == std::cmp::Ordering::Greater)
        }
        BinaryOperator::GtEq => {
            eval_comparison(left, right, |ord| ord != std::cmp::Ordering::Less)
        }

        // Arithmetic operators
        BinaryOperator::Add => eval_arithmetic(left, right, |a, b| a + b, |a, b| a + b),
        BinaryOperator::Sub => eval_arithmetic(left, right, |a, b| a - b, |a, b| a - b),
        BinaryOperator::Mul => eval_arithmetic(left, right, |a, b| a * b, |a, b| a * b),
        BinaryOperator::Div => eval_division(left, right),
        BinaryOperator::Mod => eval_modulo(left, right),

        // String concatenation
        BinaryOperator::Concat => eval_concat(left, right),

        // AND/OR handled above
        BinaryOperator::And | BinaryOperator::Or => unreachable!(),
    }
}

/// Evaluates AND with SQL NULL semantics.
///
/// SQL three-valued logic:
/// - FALSE AND anything = FALSE
/// - TRUE AND NULL = NULL
/// - NULL AND NULL = NULL
fn eval_and(left: &Value, right: &Value) -> Result<Value, ExecutorError> {
    let left_bool = to_bool_or_null(left)?;
    let right_bool = to_bool_or_null(right)?;

    match (left_bool, right_bool) {
        (Some(false), _) | (_, Some(false)) => Ok(Value::Boolean(false)),
        (Some(true), Some(true)) => Ok(Value::Boolean(true)),
        _ => Ok(Value::Null),
    }
}

/// Evaluates OR with SQL NULL semantics.
///
/// SQL three-valued logic:
/// - TRUE OR anything = TRUE
/// - FALSE OR NULL = NULL
/// - NULL OR NULL = NULL
fn eval_or(left: &Value, right: &Value) -> Result<Value, ExecutorError> {
    let left_bool = to_bool_or_null(left)?;
    let right_bool = to_bool_or_null(right)?;

    match (left_bool, right_bool) {
        (Some(true), _) | (_, Some(true)) => Ok(Value::Boolean(true)),
        (Some(false), Some(false)) => Ok(Value::Boolean(false)),
        _ => Ok(Value::Null),
    }
}

/// Converts a value to bool, returning None for NULL.
fn to_bool_or_null(val: &Value) -> Result<Option<bool>, ExecutorError> {
    match val {
        Value::Null => Ok(None),
        Value::Boolean(b) => Ok(Some(*b)),
        _ => Err(ExecutorError::TypeMismatch {
            expected: "BOOLEAN".to_string(),
            found: type_name(val),
        }),
    }
}

/// Evaluates a comparison operation.
fn eval_comparison<F>(left: &Value, right: &Value, pred: F) -> Result<Value, ExecutorError>
where
    F: Fn(std::cmp::Ordering) -> bool,
{
    let ord = compare_values(left, right)?;
    Ok(Value::Boolean(pred(ord)))
}

/// Compares two values, returning their ordering.
fn compare_values(left: &Value, right: &Value) -> Result<std::cmp::Ordering, ExecutorError> {
    use std::cmp::Ordering;

    match (left, right) {
        // Integer comparisons (promote to largest type)
        (Value::Int16(a), Value::Int16(b)) => Ok(a.cmp(b)),
        (Value::Int16(a), Value::Int32(b)) => Ok((*a as i32).cmp(b)),
        (Value::Int16(a), Value::Int64(b)) => Ok((*a as i64).cmp(b)),
        (Value::Int32(a), Value::Int16(b)) => Ok(a.cmp(&(*b as i32))),
        (Value::Int32(a), Value::Int32(b)) => Ok(a.cmp(b)),
        (Value::Int32(a), Value::Int64(b)) => Ok((*a as i64).cmp(b)),
        (Value::Int64(a), Value::Int16(b)) => Ok(a.cmp(&(*b as i64))),
        (Value::Int64(a), Value::Int32(b)) => Ok(a.cmp(&(*b as i64))),
        (Value::Int64(a), Value::Int64(b)) => Ok(a.cmp(b)),

        // Float comparisons
        (Value::Float32(a), Value::Float32(b)) => Ok(a.partial_cmp(b).unwrap_or(Ordering::Equal)),
        (Value::Float64(a), Value::Float64(b)) => Ok(a.partial_cmp(b).unwrap_or(Ordering::Equal)),
        (Value::Float32(a), Value::Float64(b)) => {
            Ok((*a as f64).partial_cmp(b).unwrap_or(Ordering::Equal))
        }
        (Value::Float64(a), Value::Float32(b)) => {
            Ok(a.partial_cmp(&(*b as f64)).unwrap_or(Ordering::Equal))
        }

        // Integer-float comparisons (promote integer to float)
        (Value::Int16(a), Value::Float32(b)) => {
            Ok((*a as f32).partial_cmp(b).unwrap_or(Ordering::Equal))
        }
        (Value::Int16(a), Value::Float64(b)) => {
            Ok((*a as f64).partial_cmp(b).unwrap_or(Ordering::Equal))
        }
        (Value::Int32(a), Value::Float32(b)) => {
            Ok((*a as f32).partial_cmp(b).unwrap_or(Ordering::Equal))
        }
        (Value::Int32(a), Value::Float64(b)) => {
            Ok((*a as f64).partial_cmp(b).unwrap_or(Ordering::Equal))
        }
        (Value::Int64(a), Value::Float32(b)) => {
            Ok((*a as f32).partial_cmp(b).unwrap_or(Ordering::Equal))
        }
        (Value::Int64(a), Value::Float64(b)) => {
            Ok((*a as f64).partial_cmp(b).unwrap_or(Ordering::Equal))
        }
        (Value::Float32(a), Value::Int16(b)) => {
            Ok(a.partial_cmp(&(*b as f32)).unwrap_or(Ordering::Equal))
        }
        (Value::Float64(a), Value::Int16(b)) => {
            Ok(a.partial_cmp(&(*b as f64)).unwrap_or(Ordering::Equal))
        }
        (Value::Float32(a), Value::Int32(b)) => {
            Ok(a.partial_cmp(&(*b as f32)).unwrap_or(Ordering::Equal))
        }
        (Value::Float64(a), Value::Int32(b)) => {
            Ok(a.partial_cmp(&(*b as f64)).unwrap_or(Ordering::Equal))
        }
        (Value::Float32(a), Value::Int64(b)) => {
            Ok(a.partial_cmp(&(*b as f32)).unwrap_or(Ordering::Equal))
        }
        (Value::Float64(a), Value::Int64(b)) => {
            Ok(a.partial_cmp(&(*b as f64)).unwrap_or(Ordering::Equal))
        }

        // Boolean comparison
        (Value::Boolean(a), Value::Boolean(b)) => Ok(a.cmp(b)),

        // Text comparison
        (Value::Text(a), Value::Text(b)) => Ok(a.cmp(b)),

        // Bytea comparison
        (Value::Bytea(a), Value::Bytea(b)) => Ok(a.cmp(b)),

        _ => Err(ExecutorError::TypeMismatch {
            expected: type_name(left),
            found: type_name(right),
        }),
    }
}

/// Evaluates an arithmetic operation.
fn eval_arithmetic<F, G>(
    left: &Value,
    right: &Value,
    int_op: F,
    float_op: G,
) -> Result<Value, ExecutorError>
where
    F: Fn(i64, i64) -> i64,
    G: Fn(f64, f64) -> f64,
{
    match (left, right) {
        // Integer arithmetic (promote to i64 for safety)
        (Value::Int16(a), Value::Int16(b)) => Ok(Value::Int64(int_op(*a as i64, *b as i64))),
        (Value::Int16(a), Value::Int32(b)) => Ok(Value::Int64(int_op(*a as i64, *b as i64))),
        (Value::Int16(a), Value::Int64(b)) => Ok(Value::Int64(int_op(*a as i64, *b))),
        (Value::Int32(a), Value::Int16(b)) => Ok(Value::Int64(int_op(*a as i64, *b as i64))),
        (Value::Int32(a), Value::Int32(b)) => Ok(Value::Int64(int_op(*a as i64, *b as i64))),
        (Value::Int32(a), Value::Int64(b)) => Ok(Value::Int64(int_op(*a as i64, *b))),
        (Value::Int64(a), Value::Int16(b)) => Ok(Value::Int64(int_op(*a, *b as i64))),
        (Value::Int64(a), Value::Int32(b)) => Ok(Value::Int64(int_op(*a, *b as i64))),
        (Value::Int64(a), Value::Int64(b)) => Ok(Value::Int64(int_op(*a, *b))),

        // Float arithmetic
        (Value::Float32(a), Value::Float32(b)) => {
            Ok(Value::Float64(float_op(*a as f64, *b as f64)))
        }
        (Value::Float64(a), Value::Float64(b)) => Ok(Value::Float64(float_op(*a, *b))),
        (Value::Float32(a), Value::Float64(b)) => Ok(Value::Float64(float_op(*a as f64, *b))),
        (Value::Float64(a), Value::Float32(b)) => Ok(Value::Float64(float_op(*a, *b as f64))),

        // Integer-float arithmetic
        (Value::Int16(a), Value::Float32(b)) => {
            Ok(Value::Float64(float_op(*a as f64, *b as f64)))
        }
        (Value::Int16(a), Value::Float64(b)) => Ok(Value::Float64(float_op(*a as f64, *b))),
        (Value::Int32(a), Value::Float32(b)) => {
            Ok(Value::Float64(float_op(*a as f64, *b as f64)))
        }
        (Value::Int32(a), Value::Float64(b)) => Ok(Value::Float64(float_op(*a as f64, *b))),
        (Value::Int64(a), Value::Float32(b)) => {
            Ok(Value::Float64(float_op(*a as f64, *b as f64)))
        }
        (Value::Int64(a), Value::Float64(b)) => Ok(Value::Float64(float_op(*a as f64, *b))),
        (Value::Float32(a), Value::Int16(b)) => {
            Ok(Value::Float64(float_op(*a as f64, *b as f64)))
        }
        (Value::Float64(a), Value::Int16(b)) => Ok(Value::Float64(float_op(*a, *b as f64))),
        (Value::Float32(a), Value::Int32(b)) => {
            Ok(Value::Float64(float_op(*a as f64, *b as f64)))
        }
        (Value::Float64(a), Value::Int32(b)) => Ok(Value::Float64(float_op(*a, *b as f64))),
        (Value::Float32(a), Value::Int64(b)) => {
            Ok(Value::Float64(float_op(*a as f64, *b as f64)))
        }
        (Value::Float64(a), Value::Int64(b)) => Ok(Value::Float64(float_op(*a, *b as f64))),

        _ => Err(ExecutorError::TypeMismatch {
            expected: "numeric".to_string(),
            found: format!("{} and {}", type_name(left), type_name(right)),
        }),
    }
}

/// Evaluates division with division-by-zero check.
fn eval_division(left: &Value, right: &Value) -> Result<Value, ExecutorError> {
    // Check for division by zero
    let is_zero = match right {
        Value::Int16(0) | Value::Int32(0) | Value::Int64(0) => true,
        Value::Float32(f) if *f == 0.0 => true,
        Value::Float64(f) if *f == 0.0 => true,
        _ => false,
    };

    if is_zero {
        return Err(ExecutorError::InvalidOperation {
            message: "division by zero".to_string(),
        });
    }

    eval_arithmetic(left, right, |a, b| a / b, |a, b| a / b)
}

/// Evaluates modulo with division-by-zero check.
fn eval_modulo(left: &Value, right: &Value) -> Result<Value, ExecutorError> {
    // Check for modulo by zero
    let is_zero = matches!(right, Value::Int16(0) | Value::Int32(0) | Value::Int64(0));

    if is_zero {
        return Err(ExecutorError::InvalidOperation {
            message: "division by zero".to_string(),
        });
    }

    match (left, right) {
        // Integer modulo only
        (Value::Int16(a), Value::Int16(b)) => Ok(Value::Int64(*a as i64 % *b as i64)),
        (Value::Int16(a), Value::Int32(b)) => Ok(Value::Int64(*a as i64 % *b as i64)),
        (Value::Int16(a), Value::Int64(b)) => Ok(Value::Int64(*a as i64 % *b)),
        (Value::Int32(a), Value::Int16(b)) => Ok(Value::Int64(*a as i64 % *b as i64)),
        (Value::Int32(a), Value::Int32(b)) => Ok(Value::Int64(*a as i64 % *b as i64)),
        (Value::Int32(a), Value::Int64(b)) => Ok(Value::Int64(*a as i64 % *b)),
        (Value::Int64(a), Value::Int16(b)) => Ok(Value::Int64(*a % *b as i64)),
        (Value::Int64(a), Value::Int32(b)) => Ok(Value::Int64(*a % *b as i64)),
        (Value::Int64(a), Value::Int64(b)) => Ok(Value::Int64(*a % *b)),
        _ => Err(ExecutorError::TypeMismatch {
            expected: "integer".to_string(),
            found: format!("{} and {}", type_name(left), type_name(right)),
        }),
    }
}

/// Evaluates string concatenation.
fn eval_concat(left: &Value, right: &Value) -> Result<Value, ExecutorError> {
    match (left, right) {
        (Value::Text(a), Value::Text(b)) => Ok(Value::Text(format!("{}{}", a, b))),
        _ => Err(ExecutorError::TypeMismatch {
            expected: "TEXT".to_string(),
            found: format!("{} and {}", type_name(left), type_name(right)),
        }),
    }
}

/// Evaluates a unary operation.
fn eval_unary_op(op: &UnaryOperator, val: &Value) -> Result<Value, ExecutorError> {
    if val.is_null() {
        return Ok(Value::Null);
    }

    match op {
        UnaryOperator::Not => match val {
            Value::Boolean(b) => Ok(Value::Boolean(!b)),
            _ => Err(ExecutorError::TypeMismatch {
                expected: "BOOLEAN".to_string(),
                found: type_name(val),
            }),
        },
        UnaryOperator::Minus => match val {
            Value::Int16(n) => Ok(Value::Int16(-n)),
            Value::Int32(n) => Ok(Value::Int32(-n)),
            Value::Int64(n) => Ok(Value::Int64(-n)),
            Value::Float32(n) => Ok(Value::Float32(-n)),
            Value::Float64(n) => Ok(Value::Float64(-n)),
            _ => Err(ExecutorError::TypeMismatch {
                expected: "numeric".to_string(),
                found: type_name(val),
            }),
        },
        UnaryOperator::Plus => match val {
            Value::Int16(_) | Value::Int32(_) | Value::Int64(_) => Ok(val.clone()),
            Value::Float32(_) | Value::Float64(_) => Ok(val.clone()),
            _ => Err(ExecutorError::TypeMismatch {
                expected: "numeric".to_string(),
                found: type_name(val),
            }),
        },
    }
}

/// Returns a human-readable type name for a value.
fn type_name(val: &Value) -> String {
    match val {
        Value::Null => "NULL".to_string(),
        Value::Boolean(_) => "BOOLEAN".to_string(),
        Value::Int16(_) => "SMALLINT".to_string(),
        Value::Int32(_) => "INTEGER".to_string(),
        Value::Int64(_) => "BIGINT".to_string(),
        Value::Float32(_) => "REAL".to_string(),
        Value::Float64(_) => "DOUBLE PRECISION".to_string(),
        Value::Text(_) => "TEXT".to_string(),
        Value::Bytea(_) => "BYTEA".to_string(),
    }
}

/// Checks if a value is "truthy" for WHERE clause evaluation.
///
/// Returns true only if the value is Boolean(true).
/// NULL and false both result in the row being filtered out.
pub fn is_truthy(val: &Value) -> bool {
    matches!(val, Value::Boolean(true))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_evaluate_literals() {
        let columns = vec![];
        let tuple = vec![];

        assert_eq!(
            evaluate(&Expr::Null, &tuple, &columns).unwrap(),
            Value::Null
        );
        assert_eq!(
            evaluate(&Expr::Boolean(true), &tuple, &columns).unwrap(),
            Value::Boolean(true)
        );
        assert_eq!(
            evaluate(&Expr::Integer(42), &tuple, &columns).unwrap(),
            Value::Int32(42)
        );
        assert_eq!(
            evaluate(&Expr::Float(3.14), &tuple, &columns).unwrap(),
            Value::Float64(3.14)
        );
        assert_eq!(
            evaluate(&Expr::String("hello".to_string()), &tuple, &columns).unwrap(),
            Value::Text("hello".to_string())
        );
    }

    #[test]
    fn test_evaluate_column_ref() {
        let columns = vec![
            ColumnInfo::new(1, 0, "id".to_string(), 23, 0),
            ColumnInfo::new(1, 1, "name".to_string(), 25, 0),
        ];
        let tuple = vec![Value::Int32(1), Value::Text("Alice".to_string())];

        let expr = Expr::ColumnRef {
            table: None,
            column: "id".to_string(),
        };
        assert_eq!(evaluate(&expr, &tuple, &columns).unwrap(), Value::Int32(1));

        let expr = Expr::ColumnRef {
            table: None,
            column: "name".to_string(),
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Text("Alice".to_string())
        );
    }

    #[test]
    fn test_evaluate_column_not_found() {
        let columns = vec![];
        let tuple = vec![];

        let expr = Expr::ColumnRef {
            table: None,
            column: "missing".to_string(),
        };
        assert!(matches!(
            evaluate(&expr, &tuple, &columns),
            Err(ExecutorError::ColumnNotFound { .. })
        ));
    }

    #[test]
    fn test_comparison_operators() {
        let columns = vec![];
        let tuple = vec![];

        // Equal
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Integer(5)),
            op: BinaryOperator::Eq,
            right: Box::new(Expr::Integer(5)),
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(true)
        );

        // Not equal
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Integer(5)),
            op: BinaryOperator::Neq,
            right: Box::new(Expr::Integer(3)),
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(true)
        );

        // Less than
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Integer(3)),
            op: BinaryOperator::Lt,
            right: Box::new(Expr::Integer(5)),
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(true)
        );

        // Greater than or equal
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Integer(5)),
            op: BinaryOperator::GtEq,
            right: Box::new(Expr::Integer(5)),
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(true)
        );
    }

    #[test]
    fn test_null_comparison() {
        let columns = vec![];
        let tuple = vec![];

        // NULL = NULL -> NULL (not TRUE!)
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Null),
            op: BinaryOperator::Eq,
            right: Box::new(Expr::Null),
        };
        assert_eq!(evaluate(&expr, &tuple, &columns).unwrap(), Value::Null);

        // 5 = NULL -> NULL
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Integer(5)),
            op: BinaryOperator::Eq,
            right: Box::new(Expr::Null),
        };
        assert_eq!(evaluate(&expr, &tuple, &columns).unwrap(), Value::Null);
    }

    #[test]
    fn test_and_with_null() {
        let columns = vec![];
        let tuple = vec![];

        // NULL AND FALSE -> FALSE
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Null),
            op: BinaryOperator::And,
            right: Box::new(Expr::Boolean(false)),
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(false)
        );

        // FALSE AND NULL -> FALSE
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Boolean(false)),
            op: BinaryOperator::And,
            right: Box::new(Expr::Null),
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(false)
        );

        // NULL AND TRUE -> NULL
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Null),
            op: BinaryOperator::And,
            right: Box::new(Expr::Boolean(true)),
        };
        assert_eq!(evaluate(&expr, &tuple, &columns).unwrap(), Value::Null);
    }

    #[test]
    fn test_or_with_null() {
        let columns = vec![];
        let tuple = vec![];

        // NULL OR TRUE -> TRUE
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Null),
            op: BinaryOperator::Or,
            right: Box::new(Expr::Boolean(true)),
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(true)
        );

        // TRUE OR NULL -> TRUE
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Boolean(true)),
            op: BinaryOperator::Or,
            right: Box::new(Expr::Null),
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(true)
        );

        // NULL OR FALSE -> NULL
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Null),
            op: BinaryOperator::Or,
            right: Box::new(Expr::Boolean(false)),
        };
        assert_eq!(evaluate(&expr, &tuple, &columns).unwrap(), Value::Null);
    }

    #[test]
    fn test_is_null() {
        let columns = vec![];
        let tuple = vec![];

        // NULL IS NULL -> TRUE
        let expr = Expr::IsNull {
            expr: Box::new(Expr::Null),
            negated: false,
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(true)
        );

        // 5 IS NULL -> FALSE
        let expr = Expr::IsNull {
            expr: Box::new(Expr::Integer(5)),
            negated: false,
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(false)
        );

        // 5 IS NOT NULL -> TRUE
        let expr = Expr::IsNull {
            expr: Box::new(Expr::Integer(5)),
            negated: true,
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(true)
        );
    }

    #[test]
    fn test_arithmetic() {
        let columns = vec![];
        let tuple = vec![];

        // 10 + 5 -> 15
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Integer(10)),
            op: BinaryOperator::Add,
            right: Box::new(Expr::Integer(5)),
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Int64(15)
        );

        // 10 - 3 -> 7
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Integer(10)),
            op: BinaryOperator::Sub,
            right: Box::new(Expr::Integer(3)),
        };
        assert_eq!(evaluate(&expr, &tuple, &columns).unwrap(), Value::Int64(7));

        // 4 * 3 -> 12
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Integer(4)),
            op: BinaryOperator::Mul,
            right: Box::new(Expr::Integer(3)),
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Int64(12)
        );

        // 10 / 3 -> 3
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Integer(10)),
            op: BinaryOperator::Div,
            right: Box::new(Expr::Integer(3)),
        };
        assert_eq!(evaluate(&expr, &tuple, &columns).unwrap(), Value::Int64(3));

        // 10 % 3 -> 1
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Integer(10)),
            op: BinaryOperator::Mod,
            right: Box::new(Expr::Integer(3)),
        };
        assert_eq!(evaluate(&expr, &tuple, &columns).unwrap(), Value::Int64(1));
    }

    #[test]
    fn test_division_by_zero() {
        let columns = vec![];
        let tuple = vec![];

        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Integer(10)),
            op: BinaryOperator::Div,
            right: Box::new(Expr::Integer(0)),
        };
        assert!(matches!(
            evaluate(&expr, &tuple, &columns),
            Err(ExecutorError::InvalidOperation { .. })
        ));
    }

    #[test]
    fn test_unary_operators() {
        let columns = vec![];
        let tuple = vec![];

        // NOT TRUE -> FALSE
        let expr = Expr::UnaryOp {
            op: UnaryOperator::Not,
            operand: Box::new(Expr::Boolean(true)),
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(false)
        );

        // -5 -> -5
        let expr = Expr::UnaryOp {
            op: UnaryOperator::Minus,
            operand: Box::new(Expr::Integer(5)),
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Int32(-5)
        );

        // NOT NULL -> NULL
        let expr = Expr::UnaryOp {
            op: UnaryOperator::Not,
            operand: Box::new(Expr::Null),
        };
        assert_eq!(evaluate(&expr, &tuple, &columns).unwrap(), Value::Null);
    }

    #[test]
    fn test_string_concat() {
        let columns = vec![];
        let tuple = vec![];

        let expr = Expr::BinaryOp {
            left: Box::new(Expr::String("hello".to_string())),
            op: BinaryOperator::Concat,
            right: Box::new(Expr::String(" world".to_string())),
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Text("hello world".to_string())
        );
    }

    #[test]
    fn test_between() {
        let columns = vec![];
        let tuple = vec![];

        // 5 BETWEEN 1 AND 10 -> TRUE
        let expr = Expr::Between {
            expr: Box::new(Expr::Integer(5)),
            low: Box::new(Expr::Integer(1)),
            high: Box::new(Expr::Integer(10)),
            negated: false,
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(true)
        );

        // 15 BETWEEN 1 AND 10 -> FALSE
        let expr = Expr::Between {
            expr: Box::new(Expr::Integer(15)),
            low: Box::new(Expr::Integer(1)),
            high: Box::new(Expr::Integer(10)),
            negated: false,
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(false)
        );

        // 15 NOT BETWEEN 1 AND 10 -> TRUE
        let expr = Expr::Between {
            expr: Box::new(Expr::Integer(15)),
            low: Box::new(Expr::Integer(1)),
            high: Box::new(Expr::Integer(10)),
            negated: true,
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(true)
        );
    }

    #[test]
    fn test_in_list() {
        let columns = vec![];
        let tuple = vec![];

        // 3 IN (1, 2, 3) -> TRUE
        let expr = Expr::InList {
            expr: Box::new(Expr::Integer(3)),
            list: vec![Expr::Integer(1), Expr::Integer(2), Expr::Integer(3)],
            negated: false,
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(true)
        );

        // 5 IN (1, 2, 3) -> FALSE
        let expr = Expr::InList {
            expr: Box::new(Expr::Integer(5)),
            list: vec![Expr::Integer(1), Expr::Integer(2), Expr::Integer(3)],
            negated: false,
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(false)
        );

        // 5 NOT IN (1, 2, 3) -> TRUE
        let expr = Expr::InList {
            expr: Box::new(Expr::Integer(5)),
            list: vec![Expr::Integer(1), Expr::Integer(2), Expr::Integer(3)],
            negated: true,
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(true)
        );

        // 5 IN (1, NULL, 3) -> NULL (not found, but NULL in list)
        let expr = Expr::InList {
            expr: Box::new(Expr::Integer(5)),
            list: vec![Expr::Integer(1), Expr::Null, Expr::Integer(3)],
            negated: false,
        };
        assert_eq!(evaluate(&expr, &tuple, &columns).unwrap(), Value::Null);
    }

    #[test]
    fn test_is_truthy() {
        assert!(is_truthy(&Value::Boolean(true)));
        assert!(!is_truthy(&Value::Boolean(false)));
        assert!(!is_truthy(&Value::Null));
        assert!(!is_truthy(&Value::Int32(1)));
    }

    #[test]
    fn test_mixed_type_comparison() {
        let columns = vec![];
        let tuple = vec![];

        // Integer vs Float comparison
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::Integer(5)),
            op: BinaryOperator::Lt,
            right: Box::new(Expr::Float(5.5)),
        };
        assert_eq!(
            evaluate(&expr, &tuple, &columns).unwrap(),
            Value::Boolean(true)
        );
    }
}
