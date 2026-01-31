//! Error types for the heap module.

use std::fmt;

/// Errors from heap operations.
#[derive(Debug)]
pub enum HeapError {
    /// Page is full, cannot insert data.
    PageFull {
        /// Bytes required for the data and slot.
        required: usize,
        /// Bytes available in free space.
        available: usize,
    },
    /// Slot not found or already deleted.
    SlotNotFound(u16),
    /// Record size mismatch for in-place update.
    RecordSizeMismatch {
        /// Expected size (existing record).
        expected: usize,
        /// Actual size (new record).
        actual: usize,
    },
    /// Serialization error.
    Serialization(SerializationError),
}

impl fmt::Display for HeapError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            HeapError::PageFull {
                required,
                available,
            } => {
                write!(
                    f,
                    "page full: need {} bytes, have {} available",
                    required, available
                )
            }
            HeapError::SlotNotFound(slot_id) => {
                write!(f, "slot {} not found or deleted", slot_id)
            }
            HeapError::RecordSizeMismatch { expected, actual } => {
                write!(
                    f,
                    "record size mismatch: expected {} bytes, got {}",
                    expected, actual
                )
            }
            HeapError::Serialization(err) => {
                write!(f, "serialization error: {}", err)
            }
        }
    }
}

impl std::error::Error for HeapError {}

impl From<SerializationError> for HeapError {
    fn from(err: SerializationError) -> Self {
        HeapError::Serialization(err)
    }
}

/// Errors from record serialization/deserialization.
#[derive(Debug)]
pub enum SerializationError {
    /// Buffer too small for the operation.
    BufferTooSmall {
        /// Bytes required.
        required: usize,
        /// Bytes available.
        available: usize,
    },
    /// Invalid data format.
    InvalidFormat(String),
}

impl fmt::Display for SerializationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SerializationError::BufferTooSmall {
                required,
                available,
            } => {
                write!(
                    f,
                    "buffer too small: need {} bytes, have {}",
                    required, available
                )
            }
            SerializationError::InvalidFormat(msg) => {
                write!(f, "invalid format: {}", msg)
            }
        }
    }
}

impl std::error::Error for SerializationError {}

/// Returns `SerializationError::BufferTooSmall` if the buffer is too small.
#[macro_export]
macro_rules! ensure_buf_len {
    ($buf:expr, $required:expr) => {
        if $buf.len() < $required {
            return Err($crate::heap::SerializationError::BufferTooSmall {
                required: $required,
                available: $buf.len(),
            });
        }
    };
}
