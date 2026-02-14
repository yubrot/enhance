//! Snapshot for MVCC isolation.
//!
//! A snapshot captures the state of committed transactions at a specific point in time,
//! enabling consistent reads without locking.
//!
//! This module provides:
//! - [`Snapshot`]: Transaction visibility state at a point in time
//! - [`Visibility`]: Result of a visibility check with hint bit side-information
//! - MVCC visibility rules: Determining which tuple versions are visible based on
//!   xmin/xmax transaction IDs and commit status

use super::manager::TransactionManager;
use super::tuple_header::{Infomask, TupleHeader};
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

    /// Determine tuple visibility and compute hint bits.
    ///
    /// This implements MVCC visibility rules (equivalent to PostgreSQL's
    /// `HeapTupleSatisfiesMVCC`) for READ COMMITTED isolation, where each
    /// statement gets a fresh snapshot.
    ///
    /// When a transaction state is resolved via `tx_manager.state()` during
    /// the visibility check, the corresponding hint bit is captured in
    /// [`Visibility::hint_bits`] so the caller can write it back without a
    /// second lookup. Hint bits are written back by
    /// [`scan_visible_page`](crate::heap::scan_visible_page) in a separate
    /// write-back pass, and by VACUUM (Step 15).
    ///
    /// NOTE: Other isolation levels (REPEATABLE READ, SERIALIZABLE) or special use cases
    /// (catalog scans, VACUUM) would require additional visibility functions like
    /// `HeapTupleSatisfiesSelf`, `HeapTupleSatisfiesAny`, or `HeapTupleSatisfiesDirty`.
    pub fn check_visibility(
        &self,
        header: &TupleHeader,
        tx_manager: &TransactionManager,
    ) -> Visibility {
        let (inserted, xmin_hints) = self.is_inserted(header, tx_manager);
        if !inserted {
            return Visibility {
                visible: false,
                hint_bits: xmin_hints,
            };
        }
        let (deleted, xmax_hints) = self.is_deleted(header, tx_manager);
        Visibility {
            visible: !deleted,
            hint_bits: xmin_hints.merge(xmax_hints),
        }
    }

    /// Check insert visibility (xmin side).
    ///
    /// Returns `(inserted, hint_bits)` where `inserted` indicates whether the
    /// inserting transaction is visible, and `hint_bits` contains newly
    /// discovered xmin hint bits (if any).
    ///
    /// **Visibility rules** - Tuple is inserted if:
    /// - xmin is FROZEN (always visible, never rolled back), OR
    /// - xmin is the current transaction AND cmin < current_cid (self-visibility), OR
    /// - xmin committed before snapshot
    fn is_inserted(
        &self,
        header: &TupleHeader,
        tx_manager: &TransactionManager,
    ) -> (bool, Infomask) {
        let xmin = header.xmin;

        // FROZEN tuples are always visible (inserted long ago, never rolled back)
        if xmin == TxId::FROZEN {
            return (true, Infomask::empty());
        }

        // Self-visibility: tuple inserted by current transaction
        if xmin == self.current_txid {
            // Only visible if inserted by an earlier command in this transaction
            return (header.cmin < self.current_cid, Infomask::empty());
        }

        // Check hint bits first for optimization
        if header.infomask.xmin_aborted() {
            return (false, Infomask::empty());
        }

        if header.infomask.xmin_committed() {
            // Committed hint bit set, check snapshot visibility
            return (self.is_txid_visible(xmin), Infomask::empty());
        }

        // No hint bits, must check transaction state
        // TODO: Once tx_states GC is implemented (requires CLOG from Step 13),
        // state() may need to return Option again and check CLOG for unknown TxIds.
        match tx_manager.state(xmin) {
            TxState::Committed => (
                self.is_txid_visible(xmin),
                Infomask::empty().with_xmin_committed(),
            ),
            TxState::Aborted => (false, Infomask::empty().with_xmin_aborted()),
            TxState::InProgress => (false, Infomask::empty()),
        }
    }

    /// Check delete visibility (xmax side).
    ///
    /// Returns `(deleted, hint_bits)` where `deleted` indicates whether the
    /// deleting transaction is visible, and `hint_bits` contains newly
    /// discovered xmax hint bits (if any).
    ///
    /// **Visibility rules** - Tuple is deleted if:
    /// - xmax is FROZEN (permanently deleted, never rolled back), OR
    /// - xmax is the current transaction AND cmax < current_cid (self-deletion), OR
    /// - xmax committed before snapshot
    fn is_deleted(
        &self,
        header: &TupleHeader,
        tx_manager: &TransactionManager,
    ) -> (bool, Infomask) {
        let xmax = header.xmax;

        // Not deleted
        if xmax == TxId::INVALID {
            return (false, Infomask::empty());
        }

        // FROZEN deletion is always visible (permanently deleted)
        if xmax == TxId::FROZEN {
            return (true, Infomask::empty());
        }

        // Self-deletion: tuple deleted by current transaction
        if xmax == self.current_txid {
            // Only deleted if deleted by an earlier command in this transaction
            return (header.cmax < self.current_cid, Infomask::empty());
        }

        // Check hint bits first for optimization
        if header.infomask.xmax_aborted() {
            return (false, Infomask::empty());
        }

        if header.infomask.xmax_committed() {
            // Committed hint bit set, check snapshot visibility
            return (self.is_txid_visible(xmax), Infomask::empty());
        }

        // No hint bits, must check transaction state
        // TODO: Once tx_states GC is implemented (requires CLOG from Step 13),
        // state() may need to return Option again and check CLOG for unknown TxIds.
        match tx_manager.state(xmax) {
            TxState::Committed => (
                self.is_txid_visible(xmax),
                Infomask::empty().with_xmax_committed(),
            ),
            TxState::Aborted => (false, Infomask::empty().with_xmax_aborted()),
            TxState::InProgress => (false, Infomask::empty()),
        }
    }
}

/// Result of an MVCC visibility check with hint bit side-information.
#[derive(Debug, Clone, Copy)]
pub struct Visibility {
    /// Whether the tuple is visible to the snapshot.
    pub visible: bool,
    /// Newly discovered hint bits to be merged into the tuple header.
    /// `Infomask::empty()` when no new information was discovered.
    pub hint_bits: Infomask,
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
        let vis = snapshot.check_visibility(&header, &manager);
        assert!(vis.visible);
        assert_eq!(vis.hint_bits, Infomask::empty());
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
        let vis = snapshot.check_visibility(&header, &manager);
        assert!(!vis.visible);
        assert_eq!(vis.hint_bits, Infomask::empty());
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
        let vis = snapshot.check_visibility(&header, &manager);
        assert!(!vis.visible);
        assert_eq!(vis.hint_bits, Infomask::empty());
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

        for tx in [tx1, tx3] {
            // Without pre-set hints: state() lookup discovers xmin_aborted
            let header = inserted_by(tx, CommandId::FIRST, Infomask::empty());
            let vis = snapshot.check_visibility(&header, &manager);
            assert!(!vis.visible);
            assert!(vis.hint_bits.xmin_aborted());

            // With xmin_aborted already set: same visibility, no new hints
            let header = inserted_by(tx, CommandId::FIRST, Infomask::empty().with_xmin_aborted());
            let vis = snapshot.check_visibility(&header, &manager);
            assert!(!vis.visible);
            assert_eq!(vis.hint_bits, Infomask::empty());
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

        let xmin_committed = Infomask::empty().with_xmin_committed();
        for (target_tx, visible, hint_when_no_preset) in [
            (tx0, true, xmin_committed),     // past: < xmin
            (tx1, false, Infomask::empty()), // present: in-progress → no hint
            (tx2, true, xmin_committed),     // present: committed before snapshot
            (tx3, false, xmin_committed),    // present: in xip (committed after snapshot)
            (tx4, true, xmin_committed),     // present: committed before snapshot
            (tx5, false, xmin_committed),    // present: in xip (committed after snapshot)
            (tx6, false, xmin_committed),    // future: >= xmax
        ] {
            // Without pre-set hints: state() lookup produces hint bits
            let header = inserted_by(target_tx, CommandId::FIRST, Infomask::empty());
            let vis = snapshot.check_visibility(&header, &manager);
            assert_eq!(vis.visible, visible);
            assert_eq!(vis.hint_bits, hint_when_no_preset);

            // With xmin_committed pre-set: same visibility, no new hints
            let header = inserted_by(target_tx, CommandId::FIRST, xmin_committed);
            let vis = snapshot.check_visibility(&header, &manager);
            assert_eq!(vis.visible, visible);
            assert_eq!(vis.hint_bits, Infomask::empty());
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

        let xmin_committed = Infomask::empty().with_xmin_committed();
        for tx_delete in [tx_delete1, tx_delete2] {
            // Without pre-set xmax hints: state() lookup discovers xmax_aborted
            let base = inserted_by(tx_insert, CommandId::FIRST, xmin_committed);
            let header = deleted_by(base, tx_delete, CommandId::FIRST);
            let vis = snapshot.check_visibility(&header, &manager);
            assert!(vis.visible);
            assert!(vis.hint_bits.xmax_aborted());

            // With xmax_aborted pre-set: same visibility, no new hints
            let base = inserted_by(
                tx_insert,
                CommandId::FIRST,
                xmin_committed.with_xmax_aborted(),
            );
            let header = deleted_by(base, tx_delete, CommandId::FIRST);
            let vis = snapshot.check_visibility(&header, &manager);
            assert!(vis.visible);
            assert_eq!(vis.hint_bits, Infomask::empty());
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
        let xmin_committed = Infomask::empty().with_xmin_committed();
        let xmax_committed = Infomask::empty().with_xmax_committed();
        for (target_tx, visible, hint_when_no_preset) in [
            (tx0, false, xmax_committed),   // past: < xmin → deletion visible
            (tx1, true, Infomask::empty()), // present: in-progress → no hint
            (tx2, false, xmax_committed),   // present: committed before snapshot
            (tx3, true, xmax_committed),    // present: in xip (committed after snapshot)
            (tx4, false, xmax_committed),   // present: committed before snapshot
            (tx5, true, xmax_committed),    // present: in xip (committed after snapshot)
            (tx6, true, xmax_committed),    // future: >= xmax
        ] {
            // Without pre-set xmax hints (xmin_committed always pre-set)
            let base = inserted_by(tx_insert, CommandId::FIRST, xmin_committed);
            let header = deleted_by(base, target_tx, CommandId::FIRST);
            let vis = snapshot.check_visibility(&header, &manager);
            assert_eq!(vis.visible, visible);
            assert_eq!(vis.hint_bits, hint_when_no_preset);

            // With xmax_committed pre-set: same visibility, no new hints
            let base = inserted_by(
                tx_insert,
                CommandId::FIRST,
                xmin_committed.merge(xmax_committed),
            );
            let header = deleted_by(base, target_tx, CommandId::FIRST);
            let vis = snapshot.check_visibility(&header, &manager);
            assert_eq!(vis.visible, visible);
            assert_eq!(vis.hint_bits, Infomask::empty());
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
        let vis = snapshot.check_visibility(&header, &manager);
        assert!(vis.visible);
        assert_eq!(vis.hint_bits, Infomask::empty());
    }

    #[test]
    fn test_visibility_self_insert_same_or_later_cid() {
        let manager = TransactionManager::new();
        let tx1 = manager.begin();

        let snapshot = manager.snapshot(tx1, CommandId::new(5));

        // Tuple inserted at cmin 5 (same as current) - not yet visible
        let header = inserted_by(tx1, CommandId::new(5), Infomask::empty());
        let vis = snapshot.check_visibility(&header, &manager);
        assert!(!vis.visible);
        assert_eq!(vis.hint_bits, Infomask::empty());
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
        let vis = snapshot.check_visibility(&header, &manager);
        assert!(!vis.visible);
        assert_eq!(vis.hint_bits, Infomask::empty());
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
        let vis = snapshot.check_visibility(&header, &manager);
        assert!(vis.visible);
        assert_eq!(vis.hint_bits, Infomask::empty());
    }
}
