//! Database-level errors.

use crate::catalog::CatalogError;
use crate::executor::ExecutorError;
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
