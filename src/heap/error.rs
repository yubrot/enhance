//! Error types for the tuple module.

use std::fmt;

/// Errors from slotted page operations.
#[derive(Debug)]
pub enum SlottedPageError {
    /// Page is full, cannot insert record.
    PageFull {
        /// Bytes required for the record and slot.
        required: usize,
        /// Bytes available in free space.
        available: usize,
    },
    /// Slot not found or already deleted.
    SlotNotFound(u16),
    /// Page data is corrupted.
    Corrupted(String),
}

impl fmt::Display for SlottedPageError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SlottedPageError::PageFull {
                required,
                available,
            } => {
                write!(
                    f,
                    "page full: need {} bytes, have {} available",
                    required, available
                )
            }
            SlottedPageError::SlotNotFound(slot_id) => {
                write!(f, "slot {} not found or deleted", slot_id)
            }
            SlottedPageError::Corrupted(msg) => {
                write!(f, "page corrupted: {}", msg)
            }
        }
    }
}

impl std::error::Error for SlottedPageError {}

/// Errors from record serialization/deserialization.
#[derive(Debug)]
pub enum SerdeError {
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

impl fmt::Display for SerdeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SerdeError::BufferTooSmall {
                required,
                available,
            } => {
                write!(
                    f,
                    "buffer too small: need {} bytes, have {}",
                    required, available
                )
            }
            SerdeError::InvalidFormat(msg) => {
                write!(f, "invalid format: {}", msg)
            }
        }
    }
}

impl std::error::Error for SerdeError {}
