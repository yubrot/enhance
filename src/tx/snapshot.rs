//! Snapshot for MVCC isolation.
//!
//! A snapshot captures the state of committed transactions at a specific point in time,
//! enabling consistent reads without locking.
//!
//! This module provides:
//! - [`Snapshot`]: Transaction visibility state at a point in time
//! - MVCC visibility rules: Determining which tuple versions are visible based on
//!   xmin/xmax transaction IDs and commit status

use super::manager::TransactionManager;
use super::tuple_header::TupleHeader;
use super::{CommandId, TxId, TxState};

/// Snapshot for MVCC visibility determination.
///
/// Snapshot with xmin, xmax, and in-progress transaction list (intentionally using
/// the same structure as PostgreSQL for learning).
/// Each statement within a READ COMMITTED transaction gets a fresh snapshot.
///
/// # Transaction Visibility Ranges
///
/// - `txid < xmin`: **Past** (committed before snapshot, always visible)
/// - `xmin <= txid < xmax`: **Present** (check `xip` to determine if in-progress)
/// - `xmax <= txid`: **Future** (started after snapshot, always invisible)
#[derive(Debug, Clone)]
pub struct Snapshot {
    /// Lower bound
    pub xmin: TxId,
    /// Upper bound
    pub xmax: TxId,
    /// Transactions in progress at snapshot time (invisible to this snapshot).
    pub xip: Vec<TxId>,
    /// Current transaction ID (for self-visibility).
    pub current_txid: TxId,
    /// Current command ID within the transaction.
    pub current_cid: CommandId,
}

impl Snapshot {
    /// Check if a transaction ID is visible according to this snapshot.
    pub fn is_txid_visible(&self, txid: TxId) -> bool {
        if txid >= self.xmax {
            // Transaction started after snapshot was taken (future)
            return false;
        }

        if txid < self.xmin {
            // All transactions before xmin are visible (past)
            return true;
        }

        // Check if transaction was in progress at snapshot time (present)
        // NOTE: Linear search O(n) on xip. Production systems with many concurrent
        // transactions could use a sorted Vec with binary search, or a HashSet.
        !self.xip.contains(&txid)
    }

    /// Determine if a tuple is visible to this snapshot.
    ///
    /// This implements MVCC visibility rules (equivalent to PostgreSQL's `HeapTupleSatisfiesMVCC`)
    /// for READ COMMITTED isolation, where each statement gets a fresh snapshot.
    ///
    /// NOTE: This function does NOT update hint bits (xmin_committed, xmin_aborted, etc.) in
    /// the tuple header. Following a lazy hint bit strategy (the same approach PostgreSQL uses), hint bits will be set by:
    /// - Readers (SeqScan in Step 10): Set hint bits on first tuple access
    /// - VACUUM (Step 15): Ensures all tuples eventually get hint bits set
    ///
    /// This avoids making abort operations O(N) for large transactions
    ///
    /// NOTE: Other isolation levels (REPEATABLE READ, SERIALIZABLE) or special use cases
    /// (catalog scans, VACUUM) would require additional visibility functions like
    /// `HeapTupleSatisfiesSelf`, `HeapTupleSatisfiesAny`, or `HeapTupleSatisfiesDirty`.
    pub fn is_tuple_visible(&self, header: &TupleHeader, tx_manager: &TransactionManager) -> bool {
        self.is_inserted(header, tx_manager) && !self.is_deleted(header, tx_manager)
    }

    /// Check if the tuple is inserted according to this snapshot.
    ///
    /// Returns true if the inserting transaction (xmin) is visible.
    ///
    /// **Visibility rules** - Tuple is inserted if:
    /// - xmin is FROZEN (always visible, never rolled back), OR
    /// - xmin is the current transaction AND cmin < current_cid (self-visibility), OR
    /// - xmin committed before snapshot
    fn is_inserted(&self, header: &TupleHeader, tx_manager: &TransactionManager) -> bool {
        let xmin = header.xmin;

        // FROZEN tuples are always visible (inserted long ago, never rolled back)
        if xmin == TxId::FROZEN {
            return true;
        }

        // Self-visibility: tuple inserted by current transaction
        if xmin == self.current_txid {
            // Only visible if inserted by an earlier command in this transaction
            return header.cmin < self.current_cid;
        }

        // Check hint bits first for optimization
        if header.infomask.xmin_aborted() {
            return false;
        }

        if header.infomask.xmin_committed() {
            // Committed hint bit set, check snapshot visibility
            return self.is_txid_visible(xmin);
        }

        // No hint bits, must check transaction state
        // TODO: Once tx_states GC is implemented (requires CLOG from Step 13),
        // state() may need to return Option again and check CLOG for unknown TxIds.
        match tx_manager.state(xmin) {
            TxState::Committed => self.is_txid_visible(xmin),
            TxState::Aborted | TxState::InProgress => false,
        }
    }

    /// Check if the tuple is deleted according to this snapshot.
    ///
    /// Returns true if the deleting transaction (xmax) is visible.
    ///
    /// **Visibility rules** - Tuple is deleted if:
    /// - xmax is FROZEN (permanently deleted, never rolled back), OR
    /// - xmax is the current transaction AND cmax < current_cid (self-deletion), OR
    /// - xmax committed before snapshot
    fn is_deleted(&self, header: &TupleHeader, tx_manager: &TransactionManager) -> bool {
        let xmax = header.xmax;

        // Not deleted
        if xmax == TxId::INVALID {
            return false;
        }

        // FROZEN deletion is always visible (permanently deleted)
        if xmax == TxId::FROZEN {
            return true;
        }

        // Self-deletion: tuple deleted by current transaction
        if xmax == self.current_txid {
            // Only deleted if deleted by an earlier command in this transaction
            return header.cmax < self.current_cid;
        }

        // Check hint bits first for optimization
        if header.infomask.xmax_aborted() {
            return false;
        }

        if header.infomask.xmax_committed() {
            // Committed hint bit set, check snapshot visibility
            return self.is_txid_visible(xmax);
        }

        // No hint bits, must check transaction state
        // TODO: Once tx_states GC is implemented (requires CLOG from Step 13),
        // state() may need to return Option again and check CLOG for unknown TxIds.
        match tx_manager.state(xmax) {
            TxState::Committed => self.is_txid_visible(xmax),
            TxState::Aborted | TxState::InProgress => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tx::Infomask;

    /// Helper: create a TupleHeader inserted by the given transaction, not deleted.
    fn inserted_by(xmin: TxId, cmin: CommandId, infomask: Infomask) -> TupleHeader {
        TupleHeader {
            xmin,
            xmax: TxId::INVALID,
            cmin,
            cmax: CommandId::INVALID,
            infomask,
        }
    }

    /// Helper: mark a TupleHeader as deleted by the given transaction.
    fn deleted_by(header: TupleHeader, xmax: TxId, cmax: CommandId) -> TupleHeader {
        TupleHeader {
            xmax,
            cmax,
            ..header
        }
    }

    // Tests for FROZEN visibility (special transaction ID)

    #[test]
    fn test_frozen_xmin_always_visible() {
        let manager = TransactionManager::new();
        let tx = manager.begin();
        let snapshot = manager.snapshot(tx, CommandId::FIRST);

        // FROZEN tuples are always visible regardless of snapshot
        let header = inserted_by(TxId::FROZEN, CommandId::FIRST, Infomask::empty());
        assert!(snapshot.is_tuple_visible(&header, &manager));
    }

    #[test]
    fn test_frozen_xmax_always_deleted() {
        let manager = TransactionManager::new();
        let tx_insert = manager.begin();
        manager.commit(tx_insert).unwrap();

        let tx = manager.begin();
        let snapshot = manager.snapshot(tx, CommandId::FIRST);

        // Tuple inserted by committed tx, deleted with FROZEN -> not visible
        let base = inserted_by(
            tx_insert,
            CommandId::FIRST,
            Infomask::empty().with_xmin_committed(),
        );
        let header = deleted_by(base, TxId::FROZEN, CommandId::FIRST);
        assert!(!snapshot.is_tuple_visible(&header, &manager));
    }

    #[test]
    fn test_frozen_insert_and_delete() {
        let manager = TransactionManager::new();
        let tx = manager.begin();
        let snapshot = manager.snapshot(tx, CommandId::FIRST);

        // Tuple inserted and deleted with FROZEN (old version after sequence update)
        let base = inserted_by(TxId::FROZEN, CommandId::FIRST, Infomask::empty());
        let header = deleted_by(base, TxId::FROZEN, CommandId::FIRST);
        // Insert visible (FROZEN), delete visible (FROZEN) -> not visible
        assert!(!snapshot.is_tuple_visible(&header, &manager));
    }

    // Tests for xmin visibility (insertion visibility)

    #[test]
    fn test_xmin_aborted_are_invisible() {
        let manager = TransactionManager::new();

        let tx1 = manager.begin();
        manager.abort(tx1).unwrap();

        let tx2 = manager.begin();
        let snapshot = manager.snapshot(tx2, CommandId::FIRST);

        let tx3 = manager.begin();
        manager.abort(tx3).unwrap();

        for infomask in [Infomask::empty(), Infomask::empty().with_xmin_aborted()] {
            let h1 = inserted_by(tx1, CommandId::FIRST, infomask);
            let h3 = inserted_by(tx3, CommandId::FIRST, infomask);
            assert!(!snapshot.is_tuple_visible(&h1, &manager));
            assert!(!snapshot.is_tuple_visible(&h3, &manager));
        }
    }

    #[test]
    fn test_xmin_committed_visibility() {
        let manager = TransactionManager::new();

        // tx0: started before snapshot and committed long before (< xmin)
        let tx0 = manager.begin();
        manager.commit(tx0).unwrap();

        // tx1: started before snapshot and uncommitted (= xmin & in xip)
        let tx1 = manager.begin();

        // tx2: started before snapshot and committed before snapshot
        let tx2 = manager.begin();
        manager.commit(tx2).unwrap();

        // tx3: started before snapshot and committed after snapshot (in xip)
        let tx3 = manager.begin();

        // main tx
        let tx = manager.begin();

        // tx4: started before snapshot and committed before snapshot
        let tx4 = manager.begin();
        manager.commit(tx4).unwrap();

        // tx5: started before snapshot and committed after snapshot (in xip)
        let tx5 = manager.begin();

        let snapshot = manager.snapshot(tx, CommandId::FIRST);
        manager.commit(tx3).unwrap();
        manager.commit(tx5).unwrap();

        // tx6: started after snapshot and committed (>= xmax)
        let tx6 = manager.begin();
        manager.commit(tx6).unwrap();

        for infomask in [Infomask::empty(), Infomask::empty().with_xmin_committed()] {
            for (target_tx, visible) in [
                (tx0, true),  // past: < xmin
                (tx1, false), // present: in xip (uncommitted)
                (tx2, true),  // present: not in xip (committed before snapshot)
                (tx3, false), // present: in xip (committed after snapshot)
                (tx4, true),  // present: not in xip (committed before snapshot)
                (tx5, false), // present: in xip (committed after snapshot)
                (tx6, false), // future: >= xmax
            ] {
                let header = inserted_by(target_tx, CommandId::FIRST, infomask);
                assert_eq!(snapshot.is_tuple_visible(&header, &manager), visible);
            }
        }
    }

    // Tests for xmax visibility (deletion visibility)

    #[test]
    fn test_xmax_aborted_are_visible() {
        let manager = TransactionManager::new();

        let tx_insert = manager.begin();
        manager.commit(tx_insert).unwrap();

        let tx_delete1 = manager.begin();
        manager.abort(tx_delete1).unwrap();

        let tx = manager.begin();
        let snapshot = manager.snapshot(tx, CommandId::FIRST);

        let tx_delete2 = manager.begin();
        manager.abort(tx_delete2).unwrap();

        for infomask in [Infomask::empty(), Infomask::empty().with_xmax_aborted()] {
            let infomask = infomask.with_xmin_committed();
            let base = inserted_by(tx_insert, CommandId::FIRST, infomask);
            let h1 = deleted_by(base, tx_delete1, CommandId::FIRST);
            let h2 = deleted_by(base, tx_delete2, CommandId::FIRST);
            assert!(snapshot.is_tuple_visible(&h1, &manager));
            assert!(snapshot.is_tuple_visible(&h2, &manager));
        }
    }

    #[test]
    fn test_xmax_committed_visibility() {
        let manager = TransactionManager::new();

        let tx_insert = manager.begin();
        manager.commit(tx_insert).unwrap();

        // tx0: started before snapshot and committed long before (< xmin)
        let tx0 = manager.begin();
        manager.commit(tx0).unwrap();

        // tx1: started before snapshot and uncommitted (= xmin & in xip)
        let tx1 = manager.begin();

        // tx2: started before snapshot and committed before snapshot
        let tx2 = manager.begin();
        manager.commit(tx2).unwrap();

        // tx3: started before snapshot and committed after snapshot (in xip)
        let tx3 = manager.begin();

        // main tx
        let tx = manager.begin();

        // tx4: started before snapshot and committed before snapshot
        let tx4 = manager.begin();
        manager.commit(tx4).unwrap();

        // tx5: started before snapshot and committed after snapshot (in xip)
        let tx5 = manager.begin();

        let snapshot = manager.snapshot(tx, CommandId::FIRST);
        manager.commit(tx3).unwrap();
        manager.commit(tx5).unwrap();

        // tx6: started after snapshot and committed (>= xmax)
        let tx6 = manager.begin();
        manager.commit(tx6).unwrap();

        // visible=true means tuple is visible (deletion NOT visible)
        // visible=false means tuple is NOT visible (deletion IS visible)
        for infomask in [Infomask::empty(), Infomask::empty().with_xmax_committed()] {
            let infomask = infomask.with_xmin_committed();
            let base = inserted_by(tx_insert, CommandId::FIRST, infomask);
            for (target_tx, visible) in [
                (tx0, false), // past: < xmin → deletion visible
                (tx1, true),  // present: in xip (uncommitted) → deletion not visible
                (tx2, false), // present: not in xip (committed before snapshot) → deletion visible
                (tx3, true),  // present: in xip (committed after snapshot) → deletion not visible
                (tx4, false), // present: not in xip (committed before snapshot) → deletion visible
                (tx5, true),  // present: in xip (committed after snapshot) → deletion not visible
                (tx6, true),  // future: >= xmax → deletion not visible
            ] {
                let header = deleted_by(base, target_tx, CommandId::FIRST);
                assert_eq!(snapshot.is_tuple_visible(&header, &manager), visible);
            }
        }
    }

    // Tests for self-visibility (current transaction)
    // Note: Hint bits are irrelevant for self-visibility as txid match is checked first

    #[test]
    fn test_visibility_self_insert_earlier_cid() {
        let manager = TransactionManager::new();
        let tx1 = manager.begin();

        let snapshot = manager.snapshot(tx1, CommandId::new(5));

        // Tuple inserted at cmin 3 (earlier than current cid 5)
        let header = inserted_by(tx1, CommandId::new(3), Infomask::empty());
        assert!(snapshot.is_tuple_visible(&header, &manager));
    }

    #[test]
    fn test_visibility_self_insert_same_or_later_cid() {
        let manager = TransactionManager::new();
        let tx1 = manager.begin();

        let snapshot = manager.snapshot(tx1, CommandId::new(5));

        // Tuple inserted at cmin 5 (same as current) - not yet visible
        let header = inserted_by(tx1, CommandId::new(5), Infomask::empty());
        assert!(!snapshot.is_tuple_visible(&header, &manager));
    }

    #[test]
    fn test_visibility_self_delete() {
        let manager = TransactionManager::new();
        let tx1 = manager.begin();

        let snapshot = manager.snapshot(tx1, CommandId::new(5));

        // Tuple inserted at cmin 3 and deleted at cmax 4 by same transaction
        // Both are earlier than current_cid=5, so insert visible and delete visible
        let base = inserted_by(tx1, CommandId::new(3), Infomask::empty());
        let header = deleted_by(base, tx1, CommandId::new(4));

        // Insert visible (cmin=3 < current_cid=5), delete also visible (cmax=4 < current_cid=5)
        // -> tuple NOT visible
        assert!(!snapshot.is_tuple_visible(&header, &manager));
    }

    #[test]
    fn test_visibility_self_insert_then_delete_later_cid() {
        let manager = TransactionManager::new();
        let tx1 = manager.begin();

        let snapshot = manager.snapshot(tx1, CommandId::new(5));

        // Tuple inserted at cmin 3, deleted at cmax 7 (later than current_cid=5)
        let base = inserted_by(tx1, CommandId::new(3), Infomask::empty());
        let header = deleted_by(base, tx1, CommandId::new(7));

        // Insert visible (cmin=3 < current_cid=5), but delete NOT visible (cmax=7 >= current_cid=5)
        // -> tuple IS visible
        assert!(snapshot.is_tuple_visible(&header, &manager));
    }
}
