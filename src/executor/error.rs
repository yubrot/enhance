//! Executor-specific errors.

use crate::datum::Type;
use crate::heap::HeapError;

/// Errors that can occur during query execution.
#[derive(Debug)]
pub enum ExecutorError {
    /// Referenced table does not exist.
    TableNotFound { name: String },

    /// Referenced column does not exist.
    ColumnNotFound { name: String },

    /// Sequence not found during nextval.
    SequenceNotFound { seq_id: u32 },

    /// Column reference is ambiguous (matches multiple columns).
    AmbiguousColumn { name: String },

    /// Type mismatch in expression evaluation.
    TypeMismatch {
        expected: String,
        found: Option<Type>,
    },

    /// Integer overflow.
    IntegerOverflow,

    /// Division by zero in arithmetic expression.
    DivisionByZero,

    /// Two values have incomparable types.
    IncomparableTypes {
        lhs: Option<Type>,
        rhs: Option<Type>,
    },

    /// Invalid type cast.
    InvalidCast { from: Option<Type>, to: Type },

    /// Numeric value out of range for the target type.
    NumericOutOfRange { type_name: String },

    /// Column index exceeds the number of columns in the record.
    ColumnIndexOutOfBounds { index: usize, len: usize },

    /// Number of values does not match the number of target columns.
    ColumnCountMismatch { expected: usize, found: usize },

    /// Duplicate column name in column list.
    DuplicateColumn { name: String },

    /// Aggregate function used in a context where it is not allowed.
    AggregateNotAllowed {
        /// The context in which the aggregate was used (e.g., "WHERE clause").
        context: String,
    },

    /// Non-aggregated column in SELECT/HAVING/ORDER BY with GROUP BY.
    NonAggregatedColumn {
        /// The column name that is not aggregated.
        name: String,
    },

    /// Unsupported operation or feature.
    Unsupported(String),

    /// Internal heap operation error (insert, delete, update).
    Heap(HeapError),
}

impl std::fmt::Display for ExecutorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExecutorError::TableNotFound { name } => {
                write!(f, "table \"{}\" does not exist", name)
            }
            ExecutorError::ColumnNotFound { name } => {
                write!(f, "column \"{}\" does not exist", name)
            }
            ExecutorError::SequenceNotFound { seq_id } => {
                write!(f, "sequence {} not found", seq_id)
            }
            ExecutorError::AmbiguousColumn { name } => {
                write!(f, "column reference \"{}\" is ambiguous", name)
            }
            ExecutorError::TypeMismatch { expected, found } => {
                write!(
                    f,
                    "type mismatch: expected {}, found {}",
                    expected,
                    ty_str(*found)
                )
            }
            ExecutorError::IncomparableTypes { lhs, rhs } => {
                write!(f, "cannot compare {} with {}", ty_str(*lhs), ty_str(*rhs))
            }
            ExecutorError::ColumnIndexOutOfBounds { index, len } => {
                write!(
                    f,
                    "column index {} out of bounds for record with {} columns",
                    index, len
                )
            }
            ExecutorError::IntegerOverflow => write!(f, "integer overflow"),
            ExecutorError::DivisionByZero => write!(f, "division by zero"),
            ExecutorError::InvalidCast { from, to } => {
                write!(f, "cannot cast {} to {}", ty_str(*from), ty_str(Some(*to)))
            }
            ExecutorError::NumericOutOfRange { type_name } => {
                write!(f, "{} out of range", type_name)
            }
            ExecutorError::ColumnCountMismatch { expected, found } => {
                write!(
                    f,
                    "INSERT has {} expressions but {} target columns",
                    found, expected
                )
            }
            ExecutorError::DuplicateColumn { name } => {
                write!(f, "column \"{}\" specified more than once", name)
            }
            ExecutorError::AggregateNotAllowed { context } => {
                write!(f, "aggregate functions are not allowed in {}", context)
            }
            ExecutorError::NonAggregatedColumn { name } => {
                write!(
                    f,
                    "column \"{}\" must appear in the GROUP BY clause or be used in an aggregate function",
                    name
                )
            }
            ExecutorError::Unsupported(msg) => write!(f, "unsupported: {}", msg),
            ExecutorError::Heap(e) => write!(f, "{}", e),
        }
    }
}

fn ty_str(ty: Option<Type>) -> &'static str {
    ty.map_or("NULL", Type::display_name)
}

impl std::error::Error for ExecutorError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ExecutorError::Heap(e) => Some(e),
            _ => None,
        }
    }
}

impl From<HeapError> for ExecutorError {
    fn from(e: HeapError) -> Self {
        ExecutorError::Heap(e)
    }
}
