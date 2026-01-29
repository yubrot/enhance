//! Catalog-specific errors.

use crate::heap::{HeapError, SerializationError};
use crate::storage::BufferPoolError;

/// Errors that can occur during catalog operations.
#[derive(Debug)]
pub enum CatalogError {
    /// Invalid superblock magic number.
    InvalidMagic { expected: u32, found: u32 },

    /// Unsupported superblock version.
    UnsupportedVersion { expected: u32, found: u32 },

    /// Table already exists.
    TableAlreadyExists { name: String },

    /// Table not found.
    TableNotFound { name: String },

    /// Sequence not found.
    SequenceNotFound { seq_id: u32 },

    /// Page is full, cannot insert more tuples.
    PageFull,

    /// Invalid data type for catalog column.
    InvalidDataType { name: String },

    /// Buffer pool error.
    BufferPool(BufferPoolError),

    /// Record serialization error.
    Serialization(SerializationError),
}

impl std::fmt::Display for CatalogError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CatalogError::InvalidMagic { expected, found } => {
                write!(
                    f,
                    "invalid superblock magic: expected 0x{:08X}, found 0x{:08X}",
                    expected, found
                )
            }
            CatalogError::UnsupportedVersion { expected, found } => {
                write!(
                    f,
                    "unsupported superblock version: expected {}, found {}",
                    expected, found
                )
            }
            CatalogError::TableAlreadyExists { name } => {
                write!(f, "table \"{}\" already exists", name)
            }
            CatalogError::TableNotFound { name } => {
                write!(f, "table \"{}\" does not exist", name)
            }
            CatalogError::SequenceNotFound { seq_id } => {
                write!(f, "sequence {} not found", seq_id)
            }
            CatalogError::PageFull => {
                write!(f, "catalog page is full")
            }
            CatalogError::InvalidDataType { name } => {
                write!(f, "invalid data type: {}", name)
            }
            CatalogError::BufferPool(e) => write!(f, "buffer pool error: {}", e),
            CatalogError::Serialization(e) => write!(f, "serialization error: {}", e),
        }
    }
}

impl std::error::Error for CatalogError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            CatalogError::BufferPool(e) => Some(e),
            CatalogError::Serialization(e) => Some(e),
            _ => None,
        }
    }
}

impl From<BufferPoolError> for CatalogError {
    fn from(e: BufferPoolError) -> Self {
        CatalogError::BufferPool(e)
    }
}

impl From<SerializationError> for CatalogError {
    fn from(e: SerializationError) -> Self {
        CatalogError::Serialization(e)
    }
}

impl From<HeapError> for CatalogError {
    fn from(e: HeapError) -> Self {
        match e {
            HeapError::PageFull { .. } => CatalogError::PageFull,
            HeapError::SlotNotFound(_) => CatalogError::PageFull, // Treat as page full for simplicity
            HeapError::Serialization(se) => CatalogError::Serialization(se),
        }
    }
}
