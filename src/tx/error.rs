//! Transaction error types.

use super::types::{TxId, TxState};

/// Errors that can occur during transaction operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TxError {
    /// Transaction not found in the transaction manager.
    TransactionNotFound(TxId),
    /// Invalid transaction state transition.
    InvalidStateTransition {
        /// Transaction ID.
        txid: TxId,
        /// Current state.
        current: TxState,
        /// Attempted new state.
        attempted: TxState,
    },
}

impl std::fmt::Display for TxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TxError::TransactionNotFound(txid) => {
                write!(f, "Transaction {} not found", txid)
            }
            TxError::InvalidStateTransition {
                txid,
                current,
                attempted,
            } => write!(
                f,
                "Invalid state transition for transaction {}: {} -> {}",
                txid, current, attempted
            ),
        }
    }
}

impl std::error::Error for TxError {}
