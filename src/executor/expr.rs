//! Bound expressions for query execution.
//!
//! [`BoundExpr`] represents an expression where column references have been
//! resolved to column indices. This allows efficient evaluation during
//! query execution without name lookups.

use super::error::ExecutorError;
use crate::heap::{Record, Value};
use crate::sql::{BinaryOperator, DataType, UnaryOperator};

/// A bound expression with column references resolved to indices.
///
/// Created by the planner from AST [`Expr`](crate::sql::ast::Expr) after
/// resolving column names against the input schema.
#[derive(Debug, Clone, PartialEq)]
pub enum BoundExpr {
    /// NULL literal.
    Null,
    /// Boolean literal.
    Boolean(bool),
    /// Integer literal (stored as i64).
    Integer(i64),
    /// Float literal (stored as f64).
    Float(f64),
    /// String literal.
    String(String),
    /// Column reference by index.
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
    /// IS NULL / IS NOT NULL.
    IsNull {
        expr: Box<BoundExpr>,
        negated: bool,
    },
    /// Type cast.
    Cast {
        expr: Box<BoundExpr>,
        target_type: DataType,
    },
}

impl BoundExpr {
    /// Evaluates this expression against a record.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Column index is out of bounds
    /// - Type mismatch during operation
    /// - Division by zero
    /// - Invalid cast
    pub fn evaluate(&self, record: &Record) -> Result<Value, ExecutorError> {
        match self {
            BoundExpr::Null => Ok(Value::Null),
            BoundExpr::Boolean(b) => Ok(Value::Boolean(*b)),
            BoundExpr::Integer(n) => Ok(Value::Int64(*n)),
            BoundExpr::Float(f) => Ok(Value::Float64(*f)),
            BoundExpr::String(s) => Ok(Value::Text(s.clone())),

            BoundExpr::Column(idx) => {
                if *idx >= record.values.len() {
                    return Err(ExecutorError::ColumnIndexOutOfBounds {
                        index: *idx,
                        len: record.values.len(),
                    });
                }
                Ok(record.values[*idx].clone())
            }

            BoundExpr::BinaryOp { left, op, right } => {
                let lval = left.evaluate(record)?;
                let rval = right.evaluate(record)?;
                evaluate_binary_op(&lval, *op, &rval)
            }

            BoundExpr::UnaryOp { op, operand } => {
                let val = operand.evaluate(record)?;
                evaluate_unary_op(*op, &val)
            }

            BoundExpr::IsNull { expr, negated } => {
                let val = expr.evaluate(record)?;
                let is_null = val.is_null();
                Ok(Value::Boolean(if *negated { !is_null } else { is_null }))
            }

            BoundExpr::Cast { expr, target_type } => {
                let val = expr.evaluate(record)?;
                cast_value(&val, target_type)
            }
        }
    }

    /// Returns true if this expression evaluates to a truthy value.
    ///
    /// - Boolean true is truthy
    /// - NULL is not truthy (SQL three-valued logic)
    /// - Other values are truthy if they would be true when cast to boolean
    pub fn is_truthy(&self, record: &Record) -> Result<bool, ExecutorError> {
        let val = self.evaluate(record)?;
        Ok(value_is_truthy(&val))
    }
}

/// Returns whether a value is truthy in SQL semantics.
///
/// NOTE: Standard SQL only allows boolean values in boolean contexts.
/// This implementation extends truthiness to non-boolean types for convenience,
/// similar to languages like JavaScript or Python. In production, this should
/// either reject non-boolean types or follow PostgreSQL's stricter semantics.
fn value_is_truthy(val: &Value) -> bool {
    match val {
        Value::Boolean(b) => *b,
        Value::Null => false,
        // Non-boolean values: non-zero numbers are truthy
        Value::Int16(n) => *n != 0,
        Value::Int32(n) => *n != 0,
        Value::Int64(n) => *n != 0,
        Value::Float32(f) => *f != 0.0,
        Value::Float64(f) => *f != 0.0,
        // Non-empty strings are truthy
        Value::Text(s) => !s.is_empty(),
        Value::Bytea(b) => !b.is_empty(),
    }
}

/// Evaluates a binary operation.
fn evaluate_binary_op(
    left: &Value,
    op: BinaryOperator,
    right: &Value,
) -> Result<Value, ExecutorError> {
    // NULL propagation: most operations with NULL return NULL
    if left.is_null() || right.is_null() {
        // Exception: AND with false, OR with true
        match op {
            BinaryOperator::And => {
                if matches!(left, Value::Boolean(false)) || matches!(right, Value::Boolean(false)) {
                    return Ok(Value::Boolean(false));
                }
                return Ok(Value::Null);
            }
            BinaryOperator::Or => {
                if matches!(left, Value::Boolean(true)) || matches!(right, Value::Boolean(true)) {
                    return Ok(Value::Boolean(true));
                }
                return Ok(Value::Null);
            }
            _ => return Ok(Value::Null),
        }
    }

    match op {
        // Arithmetic operations
        BinaryOperator::Add => arithmetic_op(left, right, |a, b| a + b, |a, b| a + b),
        BinaryOperator::Sub => arithmetic_op(left, right, |a, b| a - b, |a, b| a - b),
        BinaryOperator::Mul => arithmetic_op(left, right, |a, b| a * b, |a, b| a * b),
        BinaryOperator::Div => {
            // Check for division by zero
            if is_zero(right) {
                return Err(ExecutorError::DivisionByZero);
            }
            arithmetic_op(left, right, |a, b| a / b, |a, b| a / b)
        }
        BinaryOperator::Mod => {
            if is_zero(right) {
                return Err(ExecutorError::DivisionByZero);
            }
            arithmetic_op(left, right, |a, b| a % b, |a, b| a % b)
        }

        // Comparison operations
        BinaryOperator::Eq => compare_values(left, right, |o| o.is_eq()),
        BinaryOperator::Neq => compare_values(left, right, |o| o.is_ne()),
        BinaryOperator::Lt => compare_values(left, right, |o| o.is_lt()),
        BinaryOperator::LtEq => compare_values(left, right, |o| o.is_le()),
        BinaryOperator::Gt => compare_values(left, right, |o| o.is_gt()),
        BinaryOperator::GtEq => compare_values(left, right, |o| o.is_ge()),

        // Logical operations
        BinaryOperator::And => match (left, right) {
            (Value::Boolean(l), Value::Boolean(r)) => Ok(Value::Boolean(*l && *r)),
            _ => Err(ExecutorError::TypeMismatch {
                expected: "boolean".to_string(),
                actual: "non-boolean".to_string(),
            }),
        },
        BinaryOperator::Or => match (left, right) {
            (Value::Boolean(l), Value::Boolean(r)) => Ok(Value::Boolean(*l || *r)),
            _ => Err(ExecutorError::TypeMismatch {
                expected: "boolean".to_string(),
                actual: "non-boolean".to_string(),
            }),
        },

        // String concatenation
        BinaryOperator::Concat => match (left, right) {
            (Value::Text(l), Value::Text(r)) => Ok(Value::Text(format!("{}{}", l, r))),
            _ => Err(ExecutorError::TypeMismatch {
                expected: "text".to_string(),
                actual: "non-text".to_string(),
            }),
        },
    }
}

/// Checks if a value is zero.
fn is_zero(val: &Value) -> bool {
    match val {
        Value::Int16(n) => *n == 0,
        Value::Int32(n) => *n == 0,
        Value::Int64(n) => *n == 0,
        Value::Float32(f) => *f == 0.0,
        Value::Float64(f) => *f == 0.0,
        _ => false,
    }
}

/// Performs an arithmetic operation, promoting types as needed.
fn arithmetic_op<F, G>(left: &Value, right: &Value, int_op: F, float_op: G) -> Result<Value, ExecutorError>
where
    F: Fn(i64, i64) -> i64,
    G: Fn(f64, f64) -> f64,
{
    match (left, right) {
        // Integer operations (promote to i64)
        (Value::Int16(l), Value::Int16(r)) => Ok(Value::Int64(int_op(*l as i64, *r as i64))),
        (Value::Int16(l), Value::Int32(r)) => Ok(Value::Int64(int_op(*l as i64, *r as i64))),
        (Value::Int16(l), Value::Int64(r)) => Ok(Value::Int64(int_op(*l as i64, *r))),
        (Value::Int32(l), Value::Int16(r)) => Ok(Value::Int64(int_op(*l as i64, *r as i64))),
        (Value::Int32(l), Value::Int32(r)) => Ok(Value::Int64(int_op(*l as i64, *r as i64))),
        (Value::Int32(l), Value::Int64(r)) => Ok(Value::Int64(int_op(*l as i64, *r))),
        (Value::Int64(l), Value::Int16(r)) => Ok(Value::Int64(int_op(*l, *r as i64))),
        (Value::Int64(l), Value::Int32(r)) => Ok(Value::Int64(int_op(*l, *r as i64))),
        (Value::Int64(l), Value::Int64(r)) => Ok(Value::Int64(int_op(*l, *r))),

        // Float operations (promote to f64)
        (Value::Float32(l), Value::Float32(r)) => Ok(Value::Float64(float_op(*l as f64, *r as f64))),
        (Value::Float32(l), Value::Float64(r)) => Ok(Value::Float64(float_op(*l as f64, *r))),
        (Value::Float64(l), Value::Float32(r)) => Ok(Value::Float64(float_op(*l, *r as f64))),
        (Value::Float64(l), Value::Float64(r)) => Ok(Value::Float64(float_op(*l, *r))),

        // Mixed int/float (promote to f64)
        (Value::Int16(l), Value::Float32(r)) => Ok(Value::Float64(float_op(*l as f64, *r as f64))),
        (Value::Int16(l), Value::Float64(r)) => Ok(Value::Float64(float_op(*l as f64, *r))),
        (Value::Int32(l), Value::Float32(r)) => Ok(Value::Float64(float_op(*l as f64, *r as f64))),
        (Value::Int32(l), Value::Float64(r)) => Ok(Value::Float64(float_op(*l as f64, *r))),
        (Value::Int64(l), Value::Float32(r)) => Ok(Value::Float64(float_op(*l as f64, *r as f64))),
        (Value::Int64(l), Value::Float64(r)) => Ok(Value::Float64(float_op(*l as f64, *r))),
        (Value::Float32(l), Value::Int16(r)) => Ok(Value::Float64(float_op(*l as f64, *r as f64))),
        (Value::Float32(l), Value::Int32(r)) => Ok(Value::Float64(float_op(*l as f64, *r as f64))),
        (Value::Float32(l), Value::Int64(r)) => Ok(Value::Float64(float_op(*l as f64, *r as f64))),
        (Value::Float64(l), Value::Int16(r)) => Ok(Value::Float64(float_op(*l, *r as f64))),
        (Value::Float64(l), Value::Int32(r)) => Ok(Value::Float64(float_op(*l, *r as f64))),
        (Value::Float64(l), Value::Int64(r)) => Ok(Value::Float64(float_op(*l, *r as f64))),

        _ => Err(ExecutorError::TypeMismatch {
            expected: "numeric".to_string(),
            actual: format!("{:?} and {:?}", left, right),
        }),
    }
}

/// Compares two values and applies a predicate to the ordering.
///
/// This function coerces numeric types to a common type before comparing,
/// since the derived `PartialOrd` on `Value` returns `None` for different variants.
fn compare_values<F>(left: &Value, right: &Value, pred: F) -> Result<Value, ExecutorError>
where
    F: Fn(std::cmp::Ordering) -> bool,
{
    // Coerce numeric types for comparison
    let ord = match (left, right) {
        // Same type comparisons
        (Value::Boolean(l), Value::Boolean(r)) => l.partial_cmp(r),
        (Value::Text(l), Value::Text(r)) => l.partial_cmp(r),
        (Value::Bytea(l), Value::Bytea(r)) => l.partial_cmp(r),

        // Integer comparisons (coerce to i64)
        (Value::Int16(l), Value::Int16(r)) => Some((*l as i64).cmp(&(*r as i64))),
        (Value::Int16(l), Value::Int32(r)) => Some((*l as i64).cmp(&(*r as i64))),
        (Value::Int16(l), Value::Int64(r)) => Some((*l as i64).cmp(r)),
        (Value::Int32(l), Value::Int16(r)) => Some((*l as i64).cmp(&(*r as i64))),
        (Value::Int32(l), Value::Int32(r)) => Some((*l as i64).cmp(&(*r as i64))),
        (Value::Int32(l), Value::Int64(r)) => Some((*l as i64).cmp(r)),
        (Value::Int64(l), Value::Int16(r)) => Some(l.cmp(&(*r as i64))),
        (Value::Int64(l), Value::Int32(r)) => Some(l.cmp(&(*r as i64))),
        (Value::Int64(l), Value::Int64(r)) => Some(l.cmp(r)),

        // Float comparisons (coerce to f64)
        (Value::Float32(l), Value::Float32(r)) => (*l as f64).partial_cmp(&(*r as f64)),
        (Value::Float32(l), Value::Float64(r)) => (*l as f64).partial_cmp(r),
        (Value::Float64(l), Value::Float32(r)) => l.partial_cmp(&(*r as f64)),
        (Value::Float64(l), Value::Float64(r)) => l.partial_cmp(r),

        // Mixed int/float comparisons (coerce to f64)
        (Value::Int16(l), Value::Float32(r)) => (*l as f64).partial_cmp(&(*r as f64)),
        (Value::Int16(l), Value::Float64(r)) => (*l as f64).partial_cmp(r),
        (Value::Int32(l), Value::Float32(r)) => (*l as f64).partial_cmp(&(*r as f64)),
        (Value::Int32(l), Value::Float64(r)) => (*l as f64).partial_cmp(r),
        (Value::Int64(l), Value::Float32(r)) => (*l as f64).partial_cmp(&(*r as f64)),
        (Value::Int64(l), Value::Float64(r)) => (*l as f64).partial_cmp(r),
        (Value::Float32(l), Value::Int16(r)) => (*l as f64).partial_cmp(&(*r as f64)),
        (Value::Float32(l), Value::Int32(r)) => (*l as f64).partial_cmp(&(*r as f64)),
        (Value::Float32(l), Value::Int64(r)) => (*l as f64).partial_cmp(&(*r as f64)),
        (Value::Float64(l), Value::Int16(r)) => l.partial_cmp(&(*r as f64)),
        (Value::Float64(l), Value::Int32(r)) => l.partial_cmp(&(*r as f64)),
        (Value::Float64(l), Value::Int64(r)) => l.partial_cmp(&(*r as f64)),

        // Incompatible types
        _ => None,
    };

    match ord {
        Some(ord) => Ok(Value::Boolean(pred(ord))),
        None => Err(ExecutorError::TypeMismatch {
            expected: "comparable types".to_string(),
            actual: format!("{:?} and {:?}", left, right),
        }),
    }
}

/// Evaluates a unary operation.
fn evaluate_unary_op(op: UnaryOperator, val: &Value) -> Result<Value, ExecutorError> {
    if val.is_null() {
        return Ok(Value::Null);
    }

    match op {
        UnaryOperator::Not => match val {
            Value::Boolean(b) => Ok(Value::Boolean(!b)),
            _ => Err(ExecutorError::TypeMismatch {
                expected: "boolean".to_string(),
                actual: format!("{:?}", val),
            }),
        },
        UnaryOperator::Minus => match val {
            Value::Int16(n) => Ok(Value::Int16(-n)),
            Value::Int32(n) => Ok(Value::Int32(-n)),
            Value::Int64(n) => Ok(Value::Int64(-n)),
            Value::Float32(f) => Ok(Value::Float32(-f)),
            Value::Float64(f) => Ok(Value::Float64(-f)),
            _ => Err(ExecutorError::TypeMismatch {
                expected: "numeric".to_string(),
                actual: format!("{:?}", val),
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
                actual: format!("{:?}", val),
            }),
        },
    }
}

/// Casts a value to a target type.
fn cast_value(val: &Value, target: &DataType) -> Result<Value, ExecutorError> {
    if val.is_null() {
        return Ok(Value::Null);
    }

    match target {
        DataType::Boolean => match val {
            Value::Boolean(b) => Ok(Value::Boolean(*b)),
            Value::Int16(n) => Ok(Value::Boolean(*n != 0)),
            Value::Int32(n) => Ok(Value::Boolean(*n != 0)),
            Value::Int64(n) => Ok(Value::Boolean(*n != 0)),
            Value::Text(s) => match s.to_lowercase().as_str() {
                "true" | "t" | "yes" | "y" | "1" => Ok(Value::Boolean(true)),
                "false" | "f" | "no" | "n" | "0" => Ok(Value::Boolean(false)),
                _ => Err(ExecutorError::InvalidCast {
                    from: "text".to_string(),
                    to: "boolean".to_string(),
                }),
            },
            _ => Err(ExecutorError::InvalidCast {
                from: value_type_name(val),
                to: "boolean".to_string(),
            }),
        },

        DataType::Smallint => to_integer(val, |n| {
            if n >= i16::MIN as i64 && n <= i16::MAX as i64 {
                Some(Value::Int16(n as i16))
            } else {
                None
            }
        }),

        DataType::Integer | DataType::Serial => to_integer(val, |n| {
            if n >= i32::MIN as i64 && n <= i32::MAX as i64 {
                Some(Value::Int32(n as i32))
            } else {
                None
            }
        }),

        DataType::Bigint => to_integer(val, |n| Some(Value::Int64(n))),

        DataType::Real => to_float(val).map(|f| Value::Float32(f as f32)),

        DataType::DoublePrecision => to_float(val).map(Value::Float64),

        DataType::Text | DataType::Varchar(_) => Ok(Value::Text(value_to_string(val))),

        DataType::Bytea => match val {
            Value::Bytea(b) => Ok(Value::Bytea(b.clone())),
            Value::Text(s) => Ok(Value::Bytea(s.as_bytes().to_vec())),
            _ => Err(ExecutorError::InvalidCast {
                from: value_type_name(val),
                to: "bytea".to_string(),
            }),
        },
    }
}

/// Converts a value to an integer, applying a range check.
fn to_integer<F>(val: &Value, range_check: F) -> Result<Value, ExecutorError>
where
    F: Fn(i64) -> Option<Value>,
{
    let n: i64 = match val {
        Value::Int16(n) => *n as i64,
        Value::Int32(n) => *n as i64,
        Value::Int64(n) => *n,
        Value::Float32(f) => *f as i64,
        Value::Float64(f) => *f as i64,
        Value::Text(s) => s.parse::<i64>().map_err(|_| ExecutorError::InvalidCast {
            from: "text".to_string(),
            to: "integer".to_string(),
        })?,
        _ => {
            return Err(ExecutorError::InvalidCast {
                from: value_type_name(val),
                to: "integer".to_string(),
            })
        }
    };

    range_check(n).ok_or(ExecutorError::InvalidCast {
        from: value_type_name(val),
        to: "integer (out of range)".to_string(),
    })
}

/// Converts a value to a float.
fn to_float(val: &Value) -> Result<f64, ExecutorError> {
    match val {
        Value::Int16(n) => Ok(*n as f64),
        Value::Int32(n) => Ok(*n as f64),
        Value::Int64(n) => Ok(*n as f64),
        Value::Float32(f) => Ok(*f as f64),
        Value::Float64(f) => Ok(*f),
        Value::Text(s) => s.parse::<f64>().map_err(|_| ExecutorError::InvalidCast {
            from: "text".to_string(),
            to: "float".to_string(),
        }),
        _ => Err(ExecutorError::InvalidCast {
            from: value_type_name(val),
            to: "float".to_string(),
        }),
    }
}

/// Returns the type name of a value for error messages.
fn value_type_name(val: &Value) -> String {
    match val {
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

/// Converts a value to its string representation.
fn value_to_string(val: &Value) -> String {
    match val {
        Value::Null => "".to_string(),
        Value::Boolean(b) => if *b { "true" } else { "false" }.to_string(),
        Value::Int16(n) => n.to_string(),
        Value::Int32(n) => n.to_string(),
        Value::Int64(n) => n.to_string(),
        Value::Float32(f) => f.to_string(),
        Value::Float64(f) => f.to_string(),
        Value::Text(s) => s.clone(),
        Value::Bytea(b) => {
            let hex: String = b.iter().map(|byte| format!("{:02x}", byte)).collect();
            format!("\\x{}", hex)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn record(values: Vec<Value>) -> Record {
        Record::new(values)
    }

    #[test]
    fn test_literal_evaluation() {
        let r = record(vec![]);
        assert_eq!(BoundExpr::Null.evaluate(&r).unwrap(), Value::Null);
        assert_eq!(
            BoundExpr::Boolean(true).evaluate(&r).unwrap(),
            Value::Boolean(true)
        );
        assert_eq!(
            BoundExpr::Integer(42).evaluate(&r).unwrap(),
            Value::Int64(42)
        );
        assert_eq!(
            BoundExpr::Float(3.14).evaluate(&r).unwrap(),
            Value::Float64(3.14)
        );
        assert_eq!(
            BoundExpr::String("hello".to_string()).evaluate(&r).unwrap(),
            Value::Text("hello".to_string())
        );
    }

    #[test]
    fn test_column_reference() {
        let r = record(vec![Value::Int32(10), Value::Text("world".to_string())]);
        assert_eq!(
            BoundExpr::Column(0).evaluate(&r).unwrap(),
            Value::Int32(10)
        );
        assert_eq!(
            BoundExpr::Column(1).evaluate(&r).unwrap(),
            Value::Text("world".to_string())
        );
    }

    #[test]
    fn test_column_out_of_bounds() {
        let r = record(vec![Value::Int32(10)]);
        let err = BoundExpr::Column(5).evaluate(&r).unwrap_err();
        assert!(matches!(
            err,
            ExecutorError::ColumnIndexOutOfBounds { index: 5, len: 1 }
        ));
    }

    #[test]
    fn test_arithmetic_operations() {
        let r = record(vec![]);

        // Integer arithmetic
        let add = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Integer(10)),
            op: BinaryOperator::Add,
            right: Box::new(BoundExpr::Integer(5)),
        };
        assert_eq!(add.evaluate(&r).unwrap(), Value::Int64(15));

        let sub = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Integer(10)),
            op: BinaryOperator::Sub,
            right: Box::new(BoundExpr::Integer(3)),
        };
        assert_eq!(sub.evaluate(&r).unwrap(), Value::Int64(7));

        let mul = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Integer(4)),
            op: BinaryOperator::Mul,
            right: Box::new(BoundExpr::Integer(3)),
        };
        assert_eq!(mul.evaluate(&r).unwrap(), Value::Int64(12));

        let div = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Integer(10)),
            op: BinaryOperator::Div,
            right: Box::new(BoundExpr::Integer(3)),
        };
        assert_eq!(div.evaluate(&r).unwrap(), Value::Int64(3));
    }

    #[test]
    fn test_division_by_zero() {
        let r = record(vec![]);
        let div = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Integer(10)),
            op: BinaryOperator::Div,
            right: Box::new(BoundExpr::Integer(0)),
        };
        assert!(matches!(
            div.evaluate(&r).unwrap_err(),
            ExecutorError::DivisionByZero
        ));
    }

    #[test]
    fn test_comparison_operations() {
        let r = record(vec![]);

        let eq = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Integer(5)),
            op: BinaryOperator::Eq,
            right: Box::new(BoundExpr::Integer(5)),
        };
        assert_eq!(eq.evaluate(&r).unwrap(), Value::Boolean(true));

        let lt = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Integer(3)),
            op: BinaryOperator::Lt,
            right: Box::new(BoundExpr::Integer(5)),
        };
        assert_eq!(lt.evaluate(&r).unwrap(), Value::Boolean(true));
    }

    #[test]
    fn test_logical_operations() {
        let r = record(vec![]);

        let and = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Boolean(true)),
            op: BinaryOperator::And,
            right: Box::new(BoundExpr::Boolean(false)),
        };
        assert_eq!(and.evaluate(&r).unwrap(), Value::Boolean(false));

        let or = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Boolean(true)),
            op: BinaryOperator::Or,
            right: Box::new(BoundExpr::Boolean(false)),
        };
        assert_eq!(or.evaluate(&r).unwrap(), Value::Boolean(true));
    }

    #[test]
    fn test_null_propagation() {
        let r = record(vec![]);

        let add = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Integer(10)),
            op: BinaryOperator::Add,
            right: Box::new(BoundExpr::Null),
        };
        assert_eq!(add.evaluate(&r).unwrap(), Value::Null);

        // AND with false short-circuits
        let and_false = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Boolean(false)),
            op: BinaryOperator::And,
            right: Box::new(BoundExpr::Null),
        };
        assert_eq!(and_false.evaluate(&r).unwrap(), Value::Boolean(false));

        // OR with true short-circuits
        let or_true = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::Boolean(true)),
            op: BinaryOperator::Or,
            right: Box::new(BoundExpr::Null),
        };
        assert_eq!(or_true.evaluate(&r).unwrap(), Value::Boolean(true));
    }

    #[test]
    fn test_unary_operations() {
        let r = record(vec![]);

        let not = BoundExpr::UnaryOp {
            op: UnaryOperator::Not,
            operand: Box::new(BoundExpr::Boolean(true)),
        };
        assert_eq!(not.evaluate(&r).unwrap(), Value::Boolean(false));

        let neg = BoundExpr::UnaryOp {
            op: UnaryOperator::Minus,
            operand: Box::new(BoundExpr::Integer(42)),
        };
        assert_eq!(neg.evaluate(&r).unwrap(), Value::Int64(-42));
    }

    #[test]
    fn test_is_null() {
        let r = record(vec![Value::Null, Value::Int32(10)]);

        let is_null = BoundExpr::IsNull {
            expr: Box::new(BoundExpr::Column(0)),
            negated: false,
        };
        assert_eq!(is_null.evaluate(&r).unwrap(), Value::Boolean(true));

        let is_not_null = BoundExpr::IsNull {
            expr: Box::new(BoundExpr::Column(1)),
            negated: true,
        };
        assert_eq!(is_not_null.evaluate(&r).unwrap(), Value::Boolean(true));
    }

    #[test]
    fn test_cast() {
        let r = record(vec![]);

        let to_text = BoundExpr::Cast {
            expr: Box::new(BoundExpr::Integer(42)),
            target_type: DataType::Text,
        };
        assert_eq!(
            to_text.evaluate(&r).unwrap(),
            Value::Text("42".to_string())
        );

        let to_int = BoundExpr::Cast {
            expr: Box::new(BoundExpr::Float(3.7)),
            target_type: DataType::Integer,
        };
        assert_eq!(to_int.evaluate(&r).unwrap(), Value::Int32(3));
    }

    #[test]
    fn test_is_truthy() {
        let r = record(vec![]);

        assert!(BoundExpr::Boolean(true).is_truthy(&r).unwrap());
        assert!(!BoundExpr::Boolean(false).is_truthy(&r).unwrap());
        assert!(!BoundExpr::Null.is_truthy(&r).unwrap());
        assert!(BoundExpr::Integer(1).is_truthy(&r).unwrap());
        assert!(!BoundExpr::Integer(0).is_truthy(&r).unwrap());
    }

    #[test]
    fn test_string_concat() {
        let r = record(vec![]);

        let concat = BoundExpr::BinaryOp {
            left: Box::new(BoundExpr::String("hello".to_string())),
            op: BinaryOperator::Concat,
            right: Box::new(BoundExpr::String(" world".to_string())),
        };
        assert_eq!(
            concat.evaluate(&r).unwrap(),
            Value::Text("hello world".to_string())
        );
    }
}
