//! Transaction manager for MVCC.
//!
//! Manages transaction lifecycle: allocation of TxIds, tracking active transactions,
//! and maintaining commit/abort state.

use super::error::TxError;
use super::snapshot::Snapshot;
use super::types::{CommandId, TxId};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

/// Transaction state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransactionState {
    /// Transaction is currently in progress.
    InProgress,
    /// Transaction has committed.
    Committed,
    /// Transaction has aborted.
    Aborted,
}

impl std::fmt::Display for TransactionState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TransactionState::InProgress => write!(f, "InProgress"),
            TransactionState::Committed => write!(f, "Committed"),
            TransactionState::Aborted => write!(f, "Aborted"),
        }
    }
}

/// Transaction manager.
///
/// Responsibilities:
/// - Allocate sequential TxIds starting from 1
/// - Track active (in-progress) transactions for snapshot generation
/// - Maintain transaction commit/abort state
///
/// NOTE: Transaction state is lost on restart. Step 13 (WAL) will add CLOG
/// persistence for durable transaction state across restarts.
///
/// NOTE: Mutex-protected Vec for active transactions doesn't scale to high
/// concurrency. Production systems use lock-free ProcArray structures.
pub struct TransactionManager {
    /// Next transaction ID to allocate (starts at 1).
    next_txid: AtomicU64,
    /// Active (in-progress) transaction IDs for snapshot generation.
    active_txids: Mutex<Vec<TxId>>,
    /// Transaction state map (in-progress, committed, aborted).
    tx_states: Mutex<HashMap<TxId, TransactionState>>,
}

impl TransactionManager {
    /// Create a new transaction manager.
    pub fn new() -> Self {
        Self {
            next_txid: AtomicU64::new(1), // Start from 1 (0 is INVALID)
            active_txids: Mutex::new(Vec::new()),
            tx_states: Mutex::new(HashMap::new()),
        }
    }

    /// Begin a new transaction.
    ///
    /// Allocates a new TxId, marks it as in-progress, and adds it to the active list.
    pub fn begin(&self) -> TxId {
        let txid = TxId::new(self.next_txid.fetch_add(1, Ordering::SeqCst));

        let mut active = self.active_txids.lock().unwrap();
        active.push(txid);

        let mut states = self.tx_states.lock().unwrap();
        states.insert(txid, TransactionState::InProgress);

        txid
    }

    /// Commit a transaction.
    ///
    /// Marks the transaction as committed and removes it from the active list.
    pub fn commit(&self, txid: TxId) -> Result<(), TxError> {
        let mut states = self.tx_states.lock().unwrap();
        let state = states
            .get(&txid)
            .ok_or(TxError::TransactionNotFound(txid))?;

        if *state != TransactionState::InProgress {
            return Err(TxError::InvalidStateTransition {
                txid,
                current: state.to_string(),
                attempted: "Committed".to_string(),
            });
        }

        states.insert(txid, TransactionState::Committed);
        drop(states);

        let mut active = self.active_txids.lock().unwrap();
        active.retain(|&t| t != txid);

        Ok(())
    }

    /// Abort a transaction.
    ///
    /// Marks the transaction as aborted and removes it from the active list.
    pub fn abort(&self, txid: TxId) -> Result<(), TxError> {
        let mut states = self.tx_states.lock().unwrap();
        let state = states
            .get(&txid)
            .ok_or(TxError::TransactionNotFound(txid))?;

        if *state != TransactionState::InProgress {
            return Err(TxError::InvalidStateTransition {
                txid,
                current: state.to_string(),
                attempted: "Aborted".to_string(),
            });
        }

        states.insert(txid, TransactionState::Aborted);
        drop(states);

        let mut active = self.active_txids.lock().unwrap();
        active.retain(|&t| t != txid);

        Ok(())
    }

    /// Get the state of a transaction.
    ///
    /// Returns None if the transaction is not found (likely completed long ago
    /// and garbage collected from the state map).
    pub fn get_state(&self, txid: TxId) -> Option<TransactionState> {
        let states = self.tx_states.lock().unwrap();
        states.get(&txid).copied()
    }

    /// Create a snapshot for the current transaction.
    ///
    /// Captures the set of active transactions at this moment to determine
    /// which tuple versions are visible to this snapshot.
    pub fn snapshot(&self, current_txid: TxId, current_cid: CommandId) -> Snapshot {
        let active = self.active_txids.lock().unwrap();

        // xmin: All transactions < xmin are visible (committed before snapshot)
        // xmax: All transactions >= xmax are invisible (started after snapshot)
        // xip: Transactions in progress at snapshot time
        let xip: Vec<TxId> = active.iter().copied().collect();

        let xmin = if xip.is_empty() {
            current_txid
        } else {
            *xip.iter().min().unwrap()
        };

        let xmax = TxId::new(self.next_txid.load(Ordering::SeqCst));

        Snapshot {
            xmin,
            xmax,
            xip,
            current_txid,
            current_cid,
        }
    }
}

impl Default for TransactionManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_begin_allocates_sequential_txids() {
        let manager = TransactionManager::new();

        let tx1 = manager.begin();
        let tx2 = manager.begin();
        let tx3 = manager.begin();

        assert_eq!(tx1, TxId::new(1));
        assert_eq!(tx2, TxId::new(2));
        assert_eq!(tx3, TxId::new(3));
    }

    #[test]
    fn test_begin_marks_in_progress() {
        let manager = TransactionManager::new();
        let txid = manager.begin();

        assert_eq!(
            manager.get_state(txid),
            Some(TransactionState::InProgress)
        );
    }

    #[test]
    fn test_commit_transitions_state() {
        let manager = TransactionManager::new();
        let txid = manager.begin();

        manager.commit(txid).unwrap();
        assert_eq!(manager.get_state(txid), Some(TransactionState::Committed));
    }

    #[test]
    fn test_abort_transitions_state() {
        let manager = TransactionManager::new();
        let txid = manager.begin();

        manager.abort(txid).unwrap();
        assert_eq!(manager.get_state(txid), Some(TransactionState::Aborted));
    }

    #[test]
    fn test_commit_removes_from_active() {
        let manager = TransactionManager::new();
        let txid = manager.begin();

        manager.commit(txid).unwrap();

        let snapshot = manager.snapshot(TxId::new(999), CommandId::FIRST);
        assert!(!snapshot.xip.contains(&txid));
    }

    #[test]
    fn test_abort_removes_from_active() {
        let manager = TransactionManager::new();
        let txid = manager.begin();

        manager.abort(txid).unwrap();

        let snapshot = manager.snapshot(TxId::new(999), CommandId::FIRST);
        assert!(!snapshot.xip.contains(&txid));
    }

    #[test]
    fn test_commit_not_found() {
        let manager = TransactionManager::new();
        let result = manager.commit(TxId::new(999));
        assert!(matches!(result, Err(TxError::TransactionNotFound(_))));
    }

    #[test]
    fn test_invalid_state_transition() {
        let manager = TransactionManager::new();
        let txid = manager.begin();
        manager.commit(txid).unwrap();

        // Try to commit again
        let result = manager.commit(txid);
        assert!(matches!(result, Err(TxError::InvalidStateTransition { .. })));
    }

    #[test]
    fn test_snapshot_captures_active() {
        let manager = TransactionManager::new();

        let tx1 = manager.begin();
        let tx2 = manager.begin();
        manager.commit(tx1).unwrap();
        let tx3 = manager.begin();

        let snapshot = manager.snapshot(TxId::new(999), CommandId::FIRST);

        // tx1 committed, should not be in xip
        assert!(!snapshot.xip.contains(&tx1));
        // tx2 and tx3 still active
        assert!(snapshot.xip.contains(&tx2));
        assert!(snapshot.xip.contains(&tx3));
    }

    #[test]
    fn test_snapshot_xmin_xmax() {
        let manager = TransactionManager::new();

        let tx1 = manager.begin(); // TxId 1
        let _tx2 = manager.begin(); // TxId 2

        let snapshot = manager.snapshot(TxId::new(999), CommandId::FIRST);

        // xmin should be the minimum active transaction
        assert_eq!(snapshot.xmin, tx1);
        // xmax should be the next TxId to be allocated (3)
        assert_eq!(snapshot.xmax, TxId::new(3));
    }
}
