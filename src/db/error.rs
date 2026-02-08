//! Database-level errors.

use crate::catalog::CatalogError;
use crate::executor::ExecutorError;
use crate::protocol::{ErrorInfo, sql_state};
use crate::sql::SyntaxError;
use crate::storage::BufferPoolError;
use crate::tx::TxError;

/// Errors that can occur during database operations.
#[derive(Debug)]
pub enum DatabaseError {
    /// SQL parsing error.
    Parse(SyntaxError),
    /// Catalog error.
    Catalog(CatalogError),
    /// Buffer pool error.
    BufferPool(BufferPoolError),
    /// Transaction error.
    Transaction(TxError),
    /// Executor error.
    Executor(ExecutorError),
    /// The current transaction is aborted; commands are ignored until ROLLBACK.
    TransactionAborted,
}

impl std::fmt::Display for DatabaseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DatabaseError::Parse(e) => write!(f, "parse error: {}", e.message),
            DatabaseError::Catalog(e) => write!(f, "catalog error: {}", e),
            DatabaseError::BufferPool(e) => write!(f, "buffer pool error: {}", e),
            DatabaseError::Transaction(e) => write!(f, "transaction error: {}", e),
            DatabaseError::Executor(e) => write!(f, "{}", e),
            DatabaseError::TransactionAborted => write!(
                f,
                "current transaction is aborted, commands ignored until end of transaction block"
            ),
        }
    }
}

impl std::error::Error for DatabaseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DatabaseError::Parse(e) => Some(e),
            DatabaseError::Catalog(e) => Some(e),
            DatabaseError::BufferPool(e) => Some(e),
            DatabaseError::Transaction(e) => Some(e),
            DatabaseError::Executor(e) => Some(e),
            DatabaseError::TransactionAborted => None,
        }
    }
}

impl From<CatalogError> for DatabaseError {
    fn from(e: CatalogError) -> Self {
        DatabaseError::Catalog(e)
    }
}

impl From<BufferPoolError> for DatabaseError {
    fn from(e: BufferPoolError) -> Self {
        DatabaseError::BufferPool(e)
    }
}

impl From<SyntaxError> for DatabaseError {
    fn from(e: SyntaxError) -> Self {
        DatabaseError::Parse(e)
    }
}

impl From<TxError> for DatabaseError {
    fn from(e: TxError) -> Self {
        DatabaseError::Transaction(e)
    }
}

impl From<ExecutorError> for DatabaseError {
    fn from(e: ExecutorError) -> Self {
        DatabaseError::Executor(e)
    }
}

impl DatabaseError {
    /// Converts this error into a protocol [`ErrorInfo`] with an appropriate SQL state code.
    ///
    /// This centralizes the mapping from domain errors to wire-protocol error responses.
    pub fn to_error_info(&self) -> ErrorInfo {
        match self {
            DatabaseError::Parse(e) => {
                ErrorInfo::new(sql_state::SYNTAX_ERROR, &e.message).with_position(e.position())
            }
            DatabaseError::Executor(exec_err) => {
                let code = match exec_err {
                    ExecutorError::TableNotFound { .. } => sql_state::UNDEFINED_TABLE,
                    ExecutorError::ColumnNotFound { .. } => sql_state::UNDEFINED_COLUMN,
                    _ => sql_state::INTERNAL_ERROR,
                };
                ErrorInfo::new(code, exec_err.to_string())
            }
            DatabaseError::TransactionAborted => {
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
        let err = DatabaseError::Parse(SyntaxError::new("unexpected token", Span::new(9, 15)));
        let info = err.to_error_info();
        assert_eq!(info.code, sql_state::SYNTAX_ERROR);
        assert_eq!(info.message, "unexpected token");
        // position() returns span.start + 1 (1-indexed)
        assert_eq!(info.position, Some(10));
    }

    #[test]
    fn test_to_error_info_table_not_found() {
        let err = DatabaseError::Executor(ExecutorError::TableNotFound {
            name: "foo".to_string(),
        });
        let info = err.to_error_info();
        assert_eq!(info.code, sql_state::UNDEFINED_TABLE);
    }

    #[test]
    fn test_to_error_info_column_not_found() {
        let err = DatabaseError::Executor(ExecutorError::ColumnNotFound {
            name: "bar".to_string(),
        });
        let info = err.to_error_info();
        assert_eq!(info.code, sql_state::UNDEFINED_COLUMN);
    }

    #[test]
    fn test_to_error_info_transaction_aborted() {
        let err = DatabaseError::TransactionAborted;
        let info = err.to_error_info();
        assert_eq!(info.code, sql_state::IN_FAILED_SQL_TRANSACTION);
    }

    #[test]
    fn test_to_error_info_other_executor_error() {
        let err = DatabaseError::Executor(ExecutorError::Unsupported("test".to_string()));
        let info = err.to_error_info();
        assert_eq!(info.code, sql_state::INTERNAL_ERROR);
    }
}
