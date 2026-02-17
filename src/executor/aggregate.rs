//! Aggregate function definitions and accumulators.
//!
//! This module provides the building blocks for GROUP BY and aggregate query
//! processing:
//!
//! - [`AggregateFunction`] — enum of supported aggregate functions
//! - [`AggregateOp`] — a single aggregate operation (function + arguments + DISTINCT flag)
//! - [`Accumulator`] — trait for stateful aggregate computation
//! - [`GroupKey`] — HashMap key with SQL GROUP BY equality semantics (NULL=NULL, NaN=NaN)

use std::fmt;
use std::hash::{Hash, Hasher};

use crate::datum::{Type, Value};

use super::error::ExecutorError;
use super::expr::BoundExpr;

/// Supported aggregate functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AggregateFunction {
    /// COUNT — counts rows or non-NULL values.
    Count,
    /// SUM — sum of numeric values.
    Sum,
    /// AVG — average of numeric values (always returns Double).
    Avg,
    /// MIN — minimum value.
    Min,
    /// MAX — maximum value.
    Max,
}

impl AggregateFunction {
    /// Resolves a function name (case-insensitive) to an aggregate function.
    ///
    /// Returns `None` for non-aggregate function names.
    pub fn from_name(name: &str) -> Option<Self> {
        match name.to_ascii_lowercase().as_str() {
            "count" => Some(AggregateFunction::Count),
            "sum" => Some(AggregateFunction::Sum),
            "avg" => Some(AggregateFunction::Avg),
            "min" => Some(AggregateFunction::Min),
            "max" => Some(AggregateFunction::Max),
            _ => None,
        }
    }
}

impl fmt::Display for AggregateFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AggregateFunction::Count => write!(f, "COUNT"),
            AggregateFunction::Sum => write!(f, "SUM"),
            AggregateFunction::Avg => write!(f, "AVG"),
            AggregateFunction::Min => write!(f, "MIN"),
            AggregateFunction::Max => write!(f, "MAX"),
        }
    }
}

/// Computes the output type for an aggregate function given its input type.
///
/// - COUNT → Bigint
/// - SUM: Smallint/Integer/Bigint input → Bigint, Real/Double input → Double
/// - AVG → always Double (regardless of input type)
/// - MIN/MAX → same as input type
pub fn aggregate_output_type(func: AggregateFunction, input_ty: Option<Type>) -> Type {
    match func {
        AggregateFunction::Count => Type::Bigint,
        AggregateFunction::Sum => match input_ty.and_then(|t| t.to_wide_numeric()) {
            Some(t) => t,
            None => Type::Bigint, // default for NULL input
        },
        AggregateFunction::Avg => Type::Double,
        // NULL literal input defaults to Text (PostgreSQL "unknown" type resolution).
        AggregateFunction::Min | AggregateFunction::Max => input_ty.unwrap_or(Type::Text),
    }
}

/// Formats an aggregate call as `FUNC([DISTINCT ]args|*)`.
///
/// Shared by [`AggregateOp`] and [`BoundExpr::AggregateCall`] Display impls.
pub fn fmt_aggregate(
    f: &mut fmt::Formatter<'_>,
    func: &AggregateFunction,
    args: &[BoundExpr],
    distinct: bool,
) -> fmt::Result {
    write!(f, "{}(", func)?;
    if distinct {
        write!(f, "DISTINCT ")?;
    }
    if args.is_empty() {
        write!(f, "*")?;
    } else {
        for (i, arg) in args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg)?;
        }
    }
    write!(f, ")")
}

/// A single aggregate operation within an Aggregate plan node.
///
/// Pairs the function with its argument expression and optional DISTINCT flag.
/// COUNT(\*) is represented as `func: Count` with `args: vec![]`.
#[derive(Debug, Clone, PartialEq)]
pub struct AggregateOp {
    /// Aggregate function to apply.
    pub func: AggregateFunction,
    /// Argument expressions (empty for COUNT(\*)).
    pub args: Vec<BoundExpr>,
    /// Whether DISTINCT was specified.
    pub distinct: bool,
}

impl AggregateOp {
    /// Returns the output type of this aggregate operation.
    ///
    /// Delegates to [`aggregate_output_type`] using the first argument's type.
    pub fn output_type(&self) -> Type {
        let input_ty = self.args.first().and_then(|e| e.ty());
        aggregate_output_type(self.func, input_ty)
    }

    /// Creates an accumulator for this aggregate operation.
    ///
    /// DISTINCT filtering is handled by the Aggregate executor node,
    /// not by the accumulator. The executor deduplicates values before
    /// feeding them, so accumulators are always DISTINCT-unaware.
    pub fn create_accumulator(&self) -> Box<dyn Accumulator> {
        match self.func {
            AggregateFunction::Count => Box::new(CountAccumulator { count: 0 }),
            AggregateFunction::Sum => Box::new(SumAccumulator { sum: Value::Null }),
            AggregateFunction::Avg => Box::new(AvgAccumulator { sum: 0.0, count: 0 }),
            AggregateFunction::Min => Box::new(MinAccumulator { min: Value::Null }),
            AggregateFunction::Max => Box::new(MaxAccumulator { max: Value::Null }),
        }
    }
}

impl fmt::Display for AggregateOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_aggregate(f, &self.func, &self.args, self.distinct)
    }
}

/// Stateful aggregate computation.
///
/// Follows a three-phase lifecycle: creation → feed → finish.
/// Each accumulator processes one group's values.
///
/// DISTINCT filtering is handled by the Aggregate executor node,
/// not by the accumulator. The executor deduplicates values before
/// feeding them, so accumulators are always DISTINCT-unaware.
pub trait Accumulator: Send {
    /// Feeds a single value into the accumulator.
    ///
    /// For COUNT(\*), the executor calls `feed(Value::Null)` once per row
    /// (the value is ignored; only the call count matters).
    /// For all other aggregates, NULL values are skipped by the caller.
    fn feed(&mut self, value: &Value) -> Result<(), ExecutorError>;

    /// Produces the final aggregate result.
    fn finish(&self) -> Value;
}

/// COUNT(\*) and COUNT(expr) accumulator.
///
/// Simply counts the number of `feed()` calls. NULL skipping (for COUNT(expr))
/// is handled by the executor, not here.
struct CountAccumulator {
    count: i64,
}

impl Accumulator for CountAccumulator {
    fn feed(&mut self, _value: &Value) -> Result<(), ExecutorError> {
        self.count += 1;
        Ok(())
    }

    fn finish(&self) -> Value {
        Value::Bigint(self.count)
    }
}

/// SUM(expr) accumulator.
///
/// Maintains a running sum as either Bigint (for integer inputs) or Double
/// (for floating-point inputs). Uses checked arithmetic for integers to
/// detect overflow.
struct SumAccumulator {
    sum: Value,
}

impl Accumulator for SumAccumulator {
    fn feed(&mut self, value: &Value) -> Result<(), ExecutorError> {
        let Some(wide) = value.to_wide_numeric() else {
            return Err(ExecutorError::TypeMismatch {
                expected: "numeric".to_string(),
                found: value.ty(),
            });
        };
        self.sum = match (&self.sum, &wide) {
            (Value::Null, _) => wide,
            (Value::Bigint(a), Value::Bigint(b)) => {
                Value::Bigint(a.checked_add(*b).ok_or(ExecutorError::IntegerOverflow)?)
            }
            (Value::Double(a), Value::Double(b)) => Value::Double(a + b),
            (Value::Bigint(a), Value::Double(b)) => Value::Double(*a as f64 + b),
            (Value::Double(a), Value::Bigint(b)) => Value::Double(a + *b as f64),
            _ => unreachable!("to_wide_numeric only returns Bigint or Double"),
        };
        Ok(())
    }

    fn finish(&self) -> Value {
        self.sum.clone()
    }
}

/// AVG(expr) accumulator.
///
/// Tracks a running sum and count, always producing a Double result.
/// This matches PostgreSQL behavior where AVG of any numeric type returns
/// double precision (for non-decimal types).
struct AvgAccumulator {
    sum: f64,
    count: i64,
}

impl Accumulator for AvgAccumulator {
    fn feed(&mut self, value: &Value) -> Result<(), ExecutorError> {
        let f = match value.to_wide_numeric() {
            Some(Value::Bigint(n)) => n as f64,
            Some(Value::Double(n)) => n,
            _ => {
                return Err(ExecutorError::TypeMismatch {
                    expected: "numeric".to_string(),
                    found: value.ty(),
                });
            }
        };
        self.sum += f;
        self.count += 1;
        Ok(())
    }

    fn finish(&self) -> Value {
        if self.count == 0 {
            Value::Null
        } else {
            Value::Double(self.sum / self.count as f64)
        }
    }
}

/// MIN(expr) accumulator.
///
/// Keeps the smallest value seen so far using [`Value::partial_cmp`].
/// Returns NULL if no values were fed (all NULLs were skipped by the executor).
struct MinAccumulator {
    min: Value,
}

impl Accumulator for MinAccumulator {
    fn feed(&mut self, value: &Value) -> Result<(), ExecutorError> {
        if self.min.is_null() {
            self.min = value.clone();
        } else if let Some(std::cmp::Ordering::Less) = value.partial_cmp(&self.min) {
            self.min = value.clone();
        }
        Ok(())
    }

    fn finish(&self) -> Value {
        self.min.clone()
    }
}

/// MAX(expr) accumulator.
///
/// Keeps the largest value seen so far using [`Value::partial_cmp`].
/// Returns NULL if no values were fed (all NULLs were skipped by the executor).
struct MaxAccumulator {
    max: Value,
}

impl Accumulator for MaxAccumulator {
    fn feed(&mut self, value: &Value) -> Result<(), ExecutorError> {
        if self.max.is_null() {
            self.max = value.clone();
        } else if let Some(std::cmp::Ordering::Greater) = value.partial_cmp(&self.max) {
            self.max = value.clone();
        }
        Ok(())
    }

    fn finish(&self) -> Value {
        self.max.clone()
    }
}

/// HashMap key for GROUP BY grouping.
///
/// Wraps a `Vec<Value>` with SQL GROUP BY equality semantics:
/// - NULL = NULL (unlike `Value::PartialEq` which returns false)
/// - NaN = NaN (for float grouping)
///
/// This is necessary because `Value` implements neither `Eq` nor `Hash`
/// due to NULL and floating-point semantics.
///
/// Also used for DISTINCT aggregate deduplication: each DISTINCT aggregate
/// per group maintains a `HashSet<GroupKey>` where `GroupKey` wraps a
/// single-element Vec (the argument value) for dedup.
///
#[derive(Debug, Clone)]
pub struct GroupKey(pub(super) Vec<Value>);

impl PartialEq for GroupKey {
    fn eq(&self, other: &Self) -> bool {
        if self.0.len() != other.0.len() {
            return false;
        }
        self.0.iter().zip(other.0.iter()).all(|(a, b)| {
            match (a, b) {
                (Value::Null, Value::Null) => true,
                (Value::Null, _) | (_, Value::Null) => false,
                // Value::partial_cmp uses total ordering for floats (NaN == NaN),
                // satisfying GROUP BY semantics where NaN values are grouped together.
                _ => a.partial_cmp(b) == Some(std::cmp::Ordering::Equal),
            }
        })
    }
}

impl Eq for GroupKey {}

impl Hash for GroupKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.len().hash(state);
        for val in &self.0 {
            match val {
                Value::Null => 0u8.hash(state),
                Value::Boolean(b) => {
                    1u8.hash(state);
                    b.hash(state);
                }
                Value::Smallint(n) => {
                    2u8.hash(state);
                    n.hash(state);
                }
                Value::Integer(n) => {
                    3u8.hash(state);
                    n.hash(state);
                }
                Value::Bigint(n) => {
                    4u8.hash(state);
                    n.hash(state);
                }
                Value::Real(n) => {
                    5u8.hash(state);
                    n.to_bits().hash(state);
                }
                Value::Double(n) => {
                    6u8.hash(state);
                    n.to_bits().hash(state);
                }
                Value::Text(s) => {
                    7u8.hash(state);
                    s.hash(state);
                }
                Value::Bytea(b) => {
                    8u8.hash(state);
                    b.hash(state);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;

    fn hash_key(key: &GroupKey) -> u64 {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }

    // ========================================================================
    // CountAccumulator
    // ========================================================================

    #[test]
    fn test_count_basic() {
        let mut acc = CountAccumulator { count: 0 };
        acc.feed(&Value::Bigint(1)).unwrap();
        acc.feed(&Value::Bigint(2)).unwrap();
        acc.feed(&Value::Bigint(3)).unwrap();
        assert_eq!(acc.finish(), Value::Bigint(3));
    }

    #[test]
    fn test_count_empty() {
        let acc = CountAccumulator { count: 0 };
        assert_eq!(acc.finish(), Value::Bigint(0));
    }

    #[test]
    fn test_count_ignores_value() {
        let mut acc = CountAccumulator { count: 0 };
        // COUNT(*) feeds Null for each row — the value is ignored
        acc.feed(&Value::Null).unwrap();
        acc.feed(&Value::Null).unwrap();
        assert_eq!(acc.finish(), Value::Bigint(2));
    }

    // ========================================================================
    // SumAccumulator
    // ========================================================================

    #[test]
    fn test_sum_integers() {
        let mut acc = SumAccumulator { sum: Value::Null };
        acc.feed(&Value::Bigint(10)).unwrap();
        acc.feed(&Value::Bigint(20)).unwrap();
        acc.feed(&Value::Bigint(30)).unwrap();
        assert_eq!(acc.finish(), Value::Bigint(60));
    }

    #[test]
    fn test_sum_doubles() {
        let mut acc = SumAccumulator { sum: Value::Null };
        acc.feed(&Value::Double(1.5)).unwrap();
        acc.feed(&Value::Double(2.5)).unwrap();
        assert_eq!(acc.finish(), Value::Double(4.0));
    }

    #[test]
    fn test_sum_empty() {
        let acc = SumAccumulator { sum: Value::Null };
        assert!(acc.finish().is_null());
    }

    #[test]
    fn test_sum_integer_overflow() {
        let mut acc = SumAccumulator { sum: Value::Null };
        acc.feed(&Value::Bigint(i64::MAX)).unwrap();
        let err = acc.feed(&Value::Bigint(1)).unwrap_err();
        assert!(matches!(err, ExecutorError::IntegerOverflow));
    }

    #[test]
    fn test_sum_type_promotion() {
        // Smallint and Integer are promoted to Bigint via to_wide_numeric()
        let mut acc = SumAccumulator { sum: Value::Null };
        acc.feed(&Value::Smallint(10)).unwrap();
        acc.feed(&Value::Integer(20)).unwrap();
        acc.feed(&Value::Bigint(30)).unwrap();
        assert_eq!(acc.finish(), Value::Bigint(60));
    }

    #[test]
    fn test_sum_mixed_int_float() {
        // First feed is integer (Bigint), second is float (Double) → promotes to Double
        let mut acc = SumAccumulator { sum: Value::Null };
        acc.feed(&Value::Bigint(10)).unwrap();
        acc.feed(&Value::Double(2.5)).unwrap();
        assert_eq!(acc.finish(), Value::Double(12.5));
    }

    #[test]
    fn test_sum_single_value() {
        let mut acc = SumAccumulator { sum: Value::Null };
        acc.feed(&Value::Bigint(42)).unwrap();
        assert_eq!(acc.finish(), Value::Bigint(42));
    }

    // ========================================================================
    // AvgAccumulator
    // ========================================================================

    #[test]
    fn test_avg_basic() {
        let mut acc = AvgAccumulator { sum: 0.0, count: 0 };
        acc.feed(&Value::Bigint(10)).unwrap();
        acc.feed(&Value::Bigint(20)).unwrap();
        acc.feed(&Value::Bigint(30)).unwrap();
        assert_eq!(acc.finish(), Value::Double(20.0));
    }

    #[test]
    fn test_avg_empty() {
        let acc = AvgAccumulator { sum: 0.0, count: 0 };
        assert!(acc.finish().is_null());
    }

    #[test]
    fn test_avg_always_returns_double() {
        // Even for integer inputs, AVG returns Double
        let mut acc = AvgAccumulator { sum: 0.0, count: 0 };
        acc.feed(&Value::Bigint(7)).unwrap();
        acc.feed(&Value::Bigint(3)).unwrap();
        let result = acc.finish();
        assert_eq!(result, Value::Double(5.0));
    }

    #[test]
    fn test_avg_fractional() {
        let mut acc = AvgAccumulator { sum: 0.0, count: 0 };
        acc.feed(&Value::Bigint(1)).unwrap();
        acc.feed(&Value::Bigint(2)).unwrap();
        let result = acc.finish();
        assert_eq!(result, Value::Double(1.5));
    }

    // ========================================================================
    // MinAccumulator
    // ========================================================================

    #[test]
    fn test_min_basic() {
        let mut acc = MinAccumulator { min: Value::Null };
        acc.feed(&Value::Bigint(30)).unwrap();
        acc.feed(&Value::Bigint(10)).unwrap();
        acc.feed(&Value::Bigint(20)).unwrap();
        assert_eq!(acc.finish(), Value::Bigint(10));
    }

    #[test]
    fn test_min_empty() {
        let acc = MinAccumulator { min: Value::Null };
        assert!(acc.finish().is_null());
    }

    #[test]
    fn test_min_text() {
        let mut acc = MinAccumulator { min: Value::Null };
        acc.feed(&Value::Text("banana".into())).unwrap();
        acc.feed(&Value::Text("apple".into())).unwrap();
        acc.feed(&Value::Text("cherry".into())).unwrap();
        assert_eq!(acc.finish(), Value::Text("apple".into()));
    }

    #[test]
    fn test_min_single_value() {
        let mut acc = MinAccumulator { min: Value::Null };
        acc.feed(&Value::Bigint(42)).unwrap();
        assert_eq!(acc.finish(), Value::Bigint(42));
    }

    // ========================================================================
    // MaxAccumulator
    // ========================================================================

    #[test]
    fn test_max_basic() {
        let mut acc = MaxAccumulator { max: Value::Null };
        acc.feed(&Value::Bigint(10)).unwrap();
        acc.feed(&Value::Bigint(30)).unwrap();
        acc.feed(&Value::Bigint(20)).unwrap();
        assert_eq!(acc.finish(), Value::Bigint(30));
    }

    #[test]
    fn test_max_empty() {
        let acc = MaxAccumulator { max: Value::Null };
        assert!(acc.finish().is_null());
    }

    #[test]
    fn test_max_text() {
        let mut acc = MaxAccumulator { max: Value::Null };
        acc.feed(&Value::Text("banana".into())).unwrap();
        acc.feed(&Value::Text("apple".into())).unwrap();
        acc.feed(&Value::Text("cherry".into())).unwrap();
        assert_eq!(acc.finish(), Value::Text("cherry".into()));
    }

    // ========================================================================
    // AggregateOp — output_type and Display
    // ========================================================================

    #[test]
    fn test_output_type_count() {
        let op = AggregateOp {
            func: AggregateFunction::Count,
            args: vec![],
            distinct: false,
        };
        assert_eq!(op.output_type(), Type::Bigint);
    }

    #[test]
    fn test_output_type_sum_integer() {
        let op = AggregateOp {
            func: AggregateFunction::Sum,
            args: vec![BoundExpr::Column {
                index: 0,
                name: None,
                ty: Type::Integer,
            }],
            distinct: false,
        };
        assert_eq!(op.output_type(), Type::Bigint);
    }

    #[test]
    fn test_output_type_sum_double() {
        let op = AggregateOp {
            func: AggregateFunction::Sum,
            args: vec![BoundExpr::Column {
                index: 0,
                name: None,
                ty: Type::Double,
            }],
            distinct: false,
        };
        assert_eq!(op.output_type(), Type::Double);
    }

    #[test]
    fn test_output_type_avg_always_double() {
        let op = AggregateOp {
            func: AggregateFunction::Avg,
            args: vec![BoundExpr::Column {
                index: 0,
                name: None,
                ty: Type::Integer,
            }],
            distinct: false,
        };
        assert_eq!(op.output_type(), Type::Double);
    }

    #[test]
    fn test_output_type_min_preserves_type() {
        let op = AggregateOp {
            func: AggregateFunction::Min,
            args: vec![BoundExpr::Column {
                index: 0,
                name: None,
                ty: Type::Text,
            }],
            distinct: false,
        };
        assert_eq!(op.output_type(), Type::Text);
    }

    #[test]
    fn test_display_count_star() {
        let op = AggregateOp {
            func: AggregateFunction::Count,
            args: vec![],
            distinct: false,
        };
        assert_eq!(op.to_string(), "COUNT(*)");
    }

    #[test]
    fn test_display_sum() {
        let op = AggregateOp {
            func: AggregateFunction::Sum,
            args: vec![BoundExpr::Column {
                index: 0,
                name: Some("x".into()),
                ty: Type::Bigint,
            }],
            distinct: false,
        };
        assert_eq!(op.to_string(), "SUM($col0 (x))");
    }

    #[test]
    fn test_display_count_distinct() {
        let op = AggregateOp {
            func: AggregateFunction::Count,
            args: vec![BoundExpr::Column {
                index: 1,
                name: Some("name".into()),
                ty: Type::Text,
            }],
            distinct: true,
        };
        assert_eq!(op.to_string(), "COUNT(DISTINCT $col1 (name))");
    }

    // ========================================================================
    // AggregateFunction — from_name and Display
    // ========================================================================

    #[test]
    fn test_from_name_case_insensitive() {
        assert_eq!(
            AggregateFunction::from_name("COUNT"),
            Some(AggregateFunction::Count)
        );
        assert_eq!(
            AggregateFunction::from_name("sum"),
            Some(AggregateFunction::Sum)
        );
        assert_eq!(
            AggregateFunction::from_name("Avg"),
            Some(AggregateFunction::Avg)
        );
        assert_eq!(
            AggregateFunction::from_name("min"),
            Some(AggregateFunction::Min)
        );
        assert_eq!(
            AggregateFunction::from_name("MAX"),
            Some(AggregateFunction::Max)
        );
    }

    #[test]
    fn test_from_name_unknown() {
        assert_eq!(AggregateFunction::from_name("unknown"), None);
        assert_eq!(AggregateFunction::from_name("coalesce"), None);
    }

    #[test]
    fn test_aggregate_function_display() {
        assert_eq!(AggregateFunction::Count.to_string(), "COUNT");
        assert_eq!(AggregateFunction::Sum.to_string(), "SUM");
        assert_eq!(AggregateFunction::Avg.to_string(), "AVG");
        assert_eq!(AggregateFunction::Min.to_string(), "MIN");
        assert_eq!(AggregateFunction::Max.to_string(), "MAX");
    }

    // ========================================================================
    // GroupKey — PartialEq and Hash
    // ========================================================================

    #[test]
    fn test_group_key_null_equals_null() {
        let a = GroupKey(vec![Value::Null]);
        let b = GroupKey(vec![Value::Null]);
        assert_eq!(a, b);
        assert_eq!(hash_key(&a), hash_key(&b));
    }

    #[test]
    fn test_group_key_null_not_equal_to_non_null() {
        let a = GroupKey(vec![Value::Null]);
        let b = GroupKey(vec![Value::Bigint(1)]);
        assert_ne!(a, b);
    }

    #[test]
    fn test_group_key_nan_equals_nan() {
        let a = GroupKey(vec![Value::Double(f64::NAN)]);
        let b = GroupKey(vec![Value::Double(f64::NAN)]);
        assert_eq!(a, b);
        assert_eq!(hash_key(&a), hash_key(&b));
    }

    #[test]
    fn test_group_key_same_values() {
        let a = GroupKey(vec![Value::Bigint(1), Value::Text("hello".into())]);
        let b = GroupKey(vec![Value::Bigint(1), Value::Text("hello".into())]);
        assert_eq!(a, b);
        assert_eq!(hash_key(&a), hash_key(&b));
    }

    #[test]
    fn test_group_key_different_values() {
        let a = GroupKey(vec![Value::Bigint(1)]);
        let b = GroupKey(vec![Value::Bigint(2)]);
        assert_ne!(a, b);
    }

    #[test]
    fn test_group_key_different_lengths() {
        let a = GroupKey(vec![Value::Bigint(1)]);
        let b = GroupKey(vec![Value::Bigint(1), Value::Bigint(2)]);
        assert_ne!(a, b);
    }

    #[test]
    fn test_group_key_mixed_nulls() {
        let a = GroupKey(vec![Value::Bigint(1), Value::Null]);
        let b = GroupKey(vec![Value::Bigint(1), Value::Null]);
        assert_eq!(a, b);
        assert_eq!(hash_key(&a), hash_key(&b));
    }

    #[test]
    fn test_group_key_empty() {
        let a = GroupKey(vec![]);
        let b = GroupKey(vec![]);
        assert_eq!(a, b);
        assert_eq!(hash_key(&a), hash_key(&b));
    }

    #[test]
    fn test_group_key_boolean() {
        let a = GroupKey(vec![Value::Boolean(true)]);
        let b = GroupKey(vec![Value::Boolean(true)]);
        let c = GroupKey(vec![Value::Boolean(false)]);
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(hash_key(&a), hash_key(&b));
    }
}
