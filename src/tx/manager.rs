//! Transaction manager for MVCC.
//!
//! Manages transaction lifecycle: allocation of TxIds, tracking active transactions,
//! and maintaining commit/abort state.

use super::error::TxError;
use super::snapshot::Snapshot;
use super::{CommandId, TxId, TxState};
use parking_lot::Mutex;
use std::collections::HashMap;

/// Internal state protected by a single mutex to ensure atomicity
/// between txid allocation and active transaction tracking.
struct TxManagerState {
    /// Next transaction ID to allocate.
    next_txid: u64,
    /// Active (in-progress) transaction IDs for snapshot generation.
    active_txids: Vec<TxId>,
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
pub struct TransactionManager {
    /// Atomic state for txid allocation and active tracking.
    state: Mutex<TxManagerState>,
    /// Transaction state map (in-progress, committed, aborted).
    tx_states: Mutex<HashMap<TxId, TxState>>,
}

impl TransactionManager {
    /// Create a new transaction manager.
    pub fn new() -> Self {
        let mut tx_states = HashMap::new();
        // FROZEN is a synthetic "always committed" transaction used as a
        // universal visibility baseline (e.g., bootstrap tuples, catalog cache
        // fallback). Register it so that `state(TxId::FROZEN)` returns
        // `Committed` without special-casing.
        tx_states.insert(TxId::FROZEN, TxState::Committed);

        Self {
            state: Mutex::new(TxManagerState {
                next_txid: 2, // Start from 2 (0=INVALID, 1=FROZEN are reserved)
                active_txids: Vec::new(),
            }),
            tx_states: Mutex::new(tx_states),
        }
    }

    /// Begin a new transaction.
    ///
    /// Allocates a new TxId, marks it as in-progress, and adds it to the active list.
    pub fn begin(&self) -> TxId {
        let txid = {
            let mut state = self.state.lock();
            let txid = TxId::new(state.next_txid);
            state.next_txid += 1;
            state.active_txids.push(txid);
            txid
        };

        self.tx_states.lock().insert(txid, TxState::InProgress);
        txid
    }

    /// Commit a transaction.
    ///
    /// Marks the transaction as committed and removes it from the active list.
    pub fn commit(&self, txid: TxId) -> Result<(), TxError> {
        self.complete(txid, TxState::Committed)
    }

    /// Abort a transaction.
    ///
    /// Marks the transaction as aborted and removes it from the active list.
    ///
    /// NOTE: This follows a lazy hint bit strategy (the same approach PostgreSQL uses) - hint bits
    /// are NOT set during abort. Instead:
    /// - Readers (SeqScan) set hint bits when they first encounter tuples (Step 10)
    /// - VACUUM ensures all tuples eventually get hint bits set (Step 15)
    ///
    /// This keeps abort O(1) even for large transactions, avoiding the need to track and
    /// update all written tuples.
    ///
    /// IMPORTANT: Currently, tx_states is volatile. Once a transaction is GC'd from tx_states,
    /// visibility checks will incorrectly assume it was committed (see snapshot.rs:123).
    /// Step 13 (WAL) will add CLOG-equivalent persistence to fix this.
    pub fn abort(&self, txid: TxId) -> Result<(), TxError> {
        self.complete(txid, TxState::Aborted)
    }

    /// Marks the transaction as `state` and removes it from the active list.
    fn complete(&self, txid: TxId, new_state: TxState) -> Result<(), TxError> {
        {
            let mut tx_states = self.tx_states.lock();
            match tx_states.insert(txid, new_state) {
                Some(TxState::InProgress) => {}
                Some(current_state) => {
                    tx_states.insert(txid, current_state);
                    return Err(TxError::InvalidStateTransition {
                        txid,
                        current: current_state,
                        attempted: new_state,
                    });
                }
                None => {
                    tx_states.remove(&txid);
                    return Err(TxError::TransactionNotFound(txid));
                }
            }
        }

        self.state.lock().active_txids.retain(|&t| t != txid);

        Ok(())
    }

    /// Get the state of a transaction.
    ///
    /// # Panics
    ///
    /// Panics if the transaction is not found. This indicates a bug in the DBMS,
    /// since all TxIds are created through `begin()` and tx_states entries are
    /// never removed (GC requires CLOG from Step 13).
    ///
    /// NOTE: After tx_states GC is implemented (Step 13+), this function must
    /// fall back to CLOG lookup for GC'd TxIds instead of panicking. The return
    /// type may need to change or CLOG lookup could be transparent.
    pub fn state(&self, txid: TxId) -> TxState {
        self.tx_states
            .lock()
            .get(&txid)
            .copied()
            // TODO: Corrupted tuple headers from disk could trigger this, should be fixed
            .expect("TxId not found in tx_states - this is a bug")
    }

    /// Create a snapshot for the current transaction.
    ///
    /// Captures the set of active transactions at this moment to determine
    /// which tuple versions are visible to this snapshot.
    pub fn snapshot(&self, current_txid: TxId, current_cid: CommandId) -> Snapshot {
        let (xmax, xip) = {
            let state = self.state.lock();
            (TxId::new(state.next_txid), state.active_txids.to_vec())
        };

        // xmin = oldest active transaction, or current_txid if none active
        // (In practice, current_txid should always be in active_txids after begin())
        let xmin = xip.iter().min().copied().unwrap_or(current_txid);

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

        // Starts from 2 (0=INVALID, 1=FROZEN are reserved)
        assert_eq!(tx1, TxId::new(2));
        assert_eq!(tx2, TxId::new(3));
        assert_eq!(tx3, TxId::new(4));
    }

    #[test]
    fn test_begin_marks_in_progress() {
        let manager = TransactionManager::new();
        let txid = manager.begin();

        assert_eq!(manager.state(txid), TxState::InProgress);
    }

    #[test]
    fn test_commit_transitions_state() {
        let manager = TransactionManager::new();
        let txid = manager.begin();

        manager.commit(txid).unwrap();
        assert_eq!(manager.state(txid), TxState::Committed);
    }

    #[test]
    fn test_abort_transitions_state() {
        let manager = TransactionManager::new();
        let txid = manager.begin();

        manager.abort(txid).unwrap();
        assert_eq!(manager.state(txid), TxState::Aborted);
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
        assert!(matches!(
            result,
            Err(TxError::InvalidStateTransition { .. })
        ));
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

        let tx1 = manager.begin(); // TxId 2
        let _tx2 = manager.begin(); // TxId 3
        let tx3 = manager.begin(); // TxId 4
        manager.commit(tx3).unwrap();

        let snapshot = manager.snapshot(TxId::new(999), CommandId::FIRST);

        // xmin = oldest active = tx1
        assert_eq!(snapshot.xmin, tx1);
        // xmax = next_txid = 5 (unaffected by commit)
        assert_eq!(snapshot.xmax, TxId::new(5));
    }

    #[test]
    fn test_frozen_is_committed() {
        let manager = TransactionManager::new();
        assert_eq!(manager.state(TxId::FROZEN), TxState::Committed);
    }
}
