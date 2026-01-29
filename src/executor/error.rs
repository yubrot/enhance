//! Executor error types.

use std::fmt;

use crate::catalog::CatalogError;
use crate::heap::HeapError;
use crate::storage::BufferPoolError;

/// Errors that can occur during query execution.
#[derive(Debug)]
pub enum ExecutorError {
    /// Table not found.
    TableNotFound { name: String },
    /// Column not found.
    ColumnNotFound { name: String },
    /// Ambiguous column reference (multiple tables have this column).
    AmbiguousColumn { name: String },
    /// Type mismatch in expression evaluation.
    TypeMismatch { expected: String, found: String },
    /// Invalid operation (e.g., division by zero).
    InvalidOperation { message: String },
    /// Unsupported feature.
    Unsupported { feature: String },
    /// Column count mismatch in INSERT statement.
    ColumnCountMismatch { expected: usize, found: usize },
    /// Page is full and cannot accept more tuples.
    PageFull { required: usize, available: usize },
    /// Catalog error.
    Catalog(CatalogError),
    /// Buffer pool error.
    BufferPool(BufferPoolError),
    /// Heap error.
    Heap(HeapError),
}

impl fmt::Display for ExecutorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
                write!(f, "type mismatch: expected {}, found {}", expected, found)
            }
            ExecutorError::InvalidOperation { message } => {
                write!(f, "invalid operation: {}", message)
            }
            ExecutorError::Unsupported { feature } => {
                write!(f, "unsupported feature: {}", feature)
            }
            ExecutorError::ColumnCountMismatch { expected, found } => {
                write!(
                    f,
                    "INSERT has more expressions than target columns ({} > {})",
                    found, expected
                )
            }
            ExecutorError::PageFull { required, available } => {
                write!(
                    f,
                    "page full: need {} bytes but only {} available",
                    required, available
                )
            }
            ExecutorError::Catalog(e) => write!(f, "catalog error: {}", e),
            ExecutorError::BufferPool(e) => write!(f, "buffer pool error: {}", e),
            ExecutorError::Heap(e) => write!(f, "heap error: {}", e),
        }
    }
}

impl std::error::Error for ExecutorError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ExecutorError::Catalog(e) => Some(e),
            ExecutorError::BufferPool(e) => Some(e),
            ExecutorError::Heap(e) => Some(e),
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

impl From<HeapError> for ExecutorError {
    fn from(e: HeapError) -> Self {
        match e {
            HeapError::PageFull { required, available } => {
                ExecutorError::PageFull { required, available }
            }
            _ => ExecutorError::Heap(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_display() {
        let err = ExecutorError::TableNotFound {
            name: "users".to_string(),
        };
        assert_eq!(err.to_string(), "table \"users\" does not exist");

        let err = ExecutorError::ColumnNotFound {
            name: "id".to_string(),
        };
        assert_eq!(err.to_string(), "column \"id\" does not exist");

        let err = ExecutorError::AmbiguousColumn {
            name: "name".to_string(),
        };
        assert_eq!(
            err.to_string(),
            "column reference \"name\" is ambiguous"
        );

        let err = ExecutorError::TypeMismatch {
            expected: "INTEGER".to_string(),
            found: "TEXT".to_string(),
        };
        assert_eq!(err.to_string(), "type mismatch: expected INTEGER, found TEXT");

        let err = ExecutorError::InvalidOperation {
            message: "division by zero".to_string(),
        };
        assert_eq!(err.to_string(), "invalid operation: division by zero");

        let err = ExecutorError::Unsupported {
            feature: "subqueries".to_string(),
        };
        assert_eq!(err.to_string(), "unsupported feature: subqueries");
    }
}
