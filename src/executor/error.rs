//! Executor-specific errors.

use crate::catalog::CatalogError;
use crate::datum::Type;
use crate::storage::BufferPoolError;

/// Errors that can occur during query execution.
#[derive(Debug)]
pub enum ExecutorError {
    /// Referenced table does not exist.
    TableNotFound { name: String },

    /// Referenced column does not exist.
    ColumnNotFound { name: String },

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

    /// Unsupported operation or feature.
    Unsupported(String),

    /// Catalog error during table/column lookup.
    Catalog(CatalogError),

    /// Buffer pool error during page access.
    BufferPool(BufferPoolError),
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
            ExecutorError::Unsupported(msg) => write!(f, "unsupported: {}", msg),
            ExecutorError::Catalog(e) => write!(f, "{}", e),
            ExecutorError::BufferPool(e) => write!(f, "{}", e),
        }
    }
}

fn ty_str(ty: Option<Type>) -> &'static str {
    ty.map_or("NULL", Type::display_name)
}

impl std::error::Error for ExecutorError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ExecutorError::Catalog(e) => Some(e),
            ExecutorError::BufferPool(e) => Some(e),
            _ => None,
        }
    }
}

impl From<CatalogError> for ExecutorError {
    fn from(e: CatalogError) -> Self {
        ExecutorError::Catalog(e)
    }
}

impl From<BufferPoolError> for ExecutorError {
    fn from(e: BufferPoolError) -> Self {
        ExecutorError::BufferPool(e)
    }
}
