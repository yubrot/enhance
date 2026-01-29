//! Database-level errors.

use crate::catalog::CatalogError;
use crate::storage::BufferPoolError;

/// Errors that can occur during database operations.
#[derive(Debug)]
pub enum DatabaseError {
    /// Catalog error.
    Catalog(CatalogError),
    /// Buffer pool error.
    BufferPool(BufferPoolError),
}

impl std::fmt::Display for DatabaseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DatabaseError::Catalog(e) => write!(f, "catalog error: {}", e),
            DatabaseError::BufferPool(e) => write!(f, "buffer pool error: {}", e),
        }
    }
}

impl std::error::Error for DatabaseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DatabaseError::Catalog(e) => Some(e),
            DatabaseError::BufferPool(e) => Some(e),
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
