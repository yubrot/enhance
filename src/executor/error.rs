//! Executor errors.

use std::fmt;

/// Errors that can occur during query execution.
#[derive(Debug, Clone, PartialEq)]
pub enum ExecutorError {
    /// Column not found during planning or evaluation.
    ColumnNotFound { name: String },
    /// Table not found during planning.
    TableNotFound { name: String },
    /// Type mismatch during expression evaluation.
    TypeMismatch { expected: String, actual: String },
    /// Division by zero.
    DivisionByZero,
    /// Invalid cast operation.
    InvalidCast { from: String, to: String },
    /// Column index out of bounds during evaluation.
    ColumnIndexOutOfBounds { index: usize, len: usize },
    /// Unsupported expression or operation.
    Unsupported { message: String },
    /// Internal error (should not happen in normal operation).
    Internal { message: String },
}

impl fmt::Display for ExecutorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExecutorError::ColumnNotFound { name } => {
                write!(f, "column \"{}\" not found", name)
            }
            ExecutorError::TableNotFound { name } => {
                write!(f, "table \"{}\" not found", name)
            }
            ExecutorError::TypeMismatch { expected, actual } => {
                write!(f, "type mismatch: expected {}, got {}", expected, actual)
            }
            ExecutorError::DivisionByZero => {
                write!(f, "division by zero")
            }
            ExecutorError::InvalidCast { from, to } => {
                write!(f, "cannot cast {} to {}", from, to)
            }
            ExecutorError::ColumnIndexOutOfBounds { index, len } => {
                write!(
                    f,
                    "column index {} out of bounds for record with {} columns",
                    index, len
                )
            }
            ExecutorError::Unsupported { message } => {
                write!(f, "unsupported: {}", message)
            }
            ExecutorError::Internal { message } => {
                write!(f, "internal error: {}", message)
            }
        }
    }
}

impl std::error::Error for ExecutorError {}
