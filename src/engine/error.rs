//! Engine-level errors.

use crate::executor::ExecutorError;
use crate::heap::HeapError;
use crate::protocol::{ErrorInfo, sql_state};
use crate::sql::SyntaxError;
use crate::storage::{BufferPoolError, StorageError};
use crate::tx::TxError;

/// Errors that can occur during engine operations.
#[derive(Debug)]
pub enum EngineError {
    /// SQL parsing error.
    Parse(SyntaxError),
    /// Buffer pool error.
    BufferPool(BufferPoolError),
    /// Heap operation error.
    Heap(HeapError),
    /// Transaction error.
    Transaction(TxError),
    /// Executor error.
    Executor(ExecutorError),
    /// The current transaction is aborted; commands are ignored until ROLLBACK.
    TransactionAborted,
    /// Table already exists.
    TableAlreadyExists { name: String },
    /// Sequence not found.
    SequenceNotFound { seq_id: u32 },
    /// Invalid superblock magic number.
    InvalidMagic { expected: u32, found: u32 },
    /// Unsupported superblock version.
    UnsupportedVersion { expected: u32, found: u32 },
}

impl std::fmt::Display for EngineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EngineError::Parse(e) => write!(f, "parse error: {}", e.message),
            EngineError::BufferPool(e) => write!(f, "buffer pool error: {}", e),
            EngineError::Heap(e) => write!(f, "heap error: {}", e),
            EngineError::Transaction(e) => write!(f, "transaction error: {}", e),
            EngineError::Executor(e) => write!(f, "{}", e),
            EngineError::TransactionAborted => write!(
                f,
                "current transaction is aborted, commands ignored until end of transaction block"
            ),
            EngineError::TableAlreadyExists { name } => {
                write!(f, "table \"{}\" already exists", name)
            }
            EngineError::SequenceNotFound { seq_id } => {
                write!(f, "sequence {} not found", seq_id)
            }
            EngineError::InvalidMagic { expected, found } => {
                write!(
                    f,
                    "invalid superblock magic: expected 0x{:08X}, found 0x{:08X}",
                    expected, found
                )
            }
            EngineError::UnsupportedVersion { expected, found } => {
                write!(
                    f,
                    "unsupported superblock version: expected {}, found {}",
                    expected, found
                )
            }
        }
    }
}

impl std::error::Error for EngineError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            EngineError::Parse(e) => Some(e),
            EngineError::BufferPool(e) => Some(e),
            EngineError::Heap(e) => Some(e),
            EngineError::Transaction(e) => Some(e),
            EngineError::Executor(e) => Some(e),
            _ => None,
        }
    }
}

impl From<BufferPoolError> for EngineError {
    fn from(e: BufferPoolError) -> Self {
        EngineError::BufferPool(e)
    }
}

impl From<HeapError> for EngineError {
    fn from(e: HeapError) -> Self {
        EngineError::Heap(e)
    }
}

impl From<StorageError> for EngineError {
    fn from(e: StorageError) -> Self {
        EngineError::BufferPool(BufferPoolError::from(e))
    }
}

impl From<SyntaxError> for EngineError {
    fn from(e: SyntaxError) -> Self {
        EngineError::Parse(e)
    }
}

impl From<TxError> for EngineError {
    fn from(e: TxError) -> Self {
        EngineError::Transaction(e)
    }
}

impl From<ExecutorError> for EngineError {
    fn from(e: ExecutorError) -> Self {
        EngineError::Executor(e)
    }
}

impl EngineError {
    /// Converts this error into a protocol [`ErrorInfo`] with an appropriate SQL state code.
    ///
    /// This centralizes the mapping from domain errors to wire-protocol error responses.
    pub fn to_error_info(&self) -> ErrorInfo {
        match self {
            EngineError::Parse(e) => {
                ErrorInfo::new(sql_state::SYNTAX_ERROR, &e.message).with_position(e.position())
            }
            EngineError::Executor(exec_err) => {
                let code = match exec_err {
                    ExecutorError::TableNotFound { .. } => sql_state::UNDEFINED_TABLE,
                    ExecutorError::ColumnNotFound { .. } => sql_state::UNDEFINED_COLUMN,
                    _ => sql_state::INTERNAL_ERROR,
                };
                ErrorInfo::new(code, exec_err.to_string())
            }
            EngineError::TransactionAborted => {
                ErrorInfo::new(sql_state::IN_FAILED_SQL_TRANSACTION, self.to_string())
            }
            _ => ErrorInfo::new(sql_state::INTERNAL_ERROR, self.to_string()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sql::Span;

    #[test]
    fn test_to_error_info_parse_error() {
        let err = EngineError::Parse(SyntaxError::new("unexpected token", Span::new(9, 15)));
        let info = err.to_error_info();
        assert_eq!(info.code, sql_state::SYNTAX_ERROR);
        assert_eq!(info.message, "unexpected token");
        // position() returns span.start + 1 (1-indexed)
        assert_eq!(info.position, Some(10));
    }

    #[test]
    fn test_to_error_info_table_not_found() {
        let err = EngineError::Executor(ExecutorError::TableNotFound {
            name: "foo".to_string(),
        });
        let info = err.to_error_info();
        assert_eq!(info.code, sql_state::UNDEFINED_TABLE);
    }

    #[test]
    fn test_to_error_info_column_not_found() {
        let err = EngineError::Executor(ExecutorError::ColumnNotFound {
            name: "bar".to_string(),
        });
        let info = err.to_error_info();
        assert_eq!(info.code, sql_state::UNDEFINED_COLUMN);
    }

    #[test]
    fn test_to_error_info_transaction_aborted() {
        let err = EngineError::TransactionAborted;
        let info = err.to_error_info();
        assert_eq!(info.code, sql_state::IN_FAILED_SQL_TRANSACTION);
    }

    #[test]
    fn test_to_error_info_other_executor_error() {
        let err = EngineError::Executor(ExecutorError::Unsupported("test".to_string()));
        let info = err.to_error_info();
        assert_eq!(info.code, sql_state::INTERNAL_ERROR);
    }
}
