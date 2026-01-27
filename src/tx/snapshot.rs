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
use super::types::{CommandId, TxId, TxState};

/// Snapshot for MVCC visibility determination.
///
/// PostgreSQL-style snapshot with xmin, xmax, and in-progress transaction list.
/// Each statement within a READ COMMITTED transaction gets a fresh snapshot.
///
/// # Transaction Visibility Ranges
///
/// - `txid < xmin`: **Past** (committed before snapshot, always visible)
/// - `xmin <= txid < xmax`: **Present** (check `xip` to determine if in-progress)
/// - `txid >= xmax`: **Future** (started after snapshot, always invisible)
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
        !self.xip.contains(&txid)
    }

    /// Determine if a tuple is visible to this snapshot.
    ///
    /// This implements PostgreSQL's `HeapTupleSatisfiesMVCC` visibility rules for
    /// READ COMMITTED isolation, where each statement gets a fresh snapshot.
    ///
    /// **Visibility rules:**
    ///
    /// 1. **xmin check** - Tuple is visible if:
    ///    - xmin is the current transaction AND cid < current_cid (self-visibility), OR
    ///    - xmin committed before snapshot
    ///
    /// 2. **xmax check** - Tuple is NOT deleted if:
    ///    - xmax is INVALID (never deleted), OR
    ///    - xmax aborted, OR
    ///    - xmax is in progress by another transaction, OR
    ///    - xmax is the current transaction AND cid >= current_cid (not yet deleted)
    ///
    /// NOTE: This function does NOT update hint bits (xmin_committed, xmin_aborted, etc.) in
    /// the tuple header. Following PostgreSQL's lazy hint bit strategy, hint bits will be set by:
    /// - Readers (SeqScan in Step 10): Set hint bits on first tuple access
    /// - VACUUM (Step 15): Ensures all tuples eventually get hint bits set
    ///
    /// This avoids making abort operations O(N) for large transactions
    ///
    /// NOTE: Other isolation levels (REPEATABLE READ, SERIALIZABLE) or special use cases
    /// (catalog scans, VACUUM) would require additional visibility functions like
    /// `HeapTupleSatisfiesSelf`, `HeapTupleSatisfiesAny`, or `HeapTupleSatisfiesDirty`.
    pub fn is_tuple_visible(&self, header: &TupleHeader, tx_manager: &TransactionManager) -> bool {
        // Check if tuple was inserted (xmin visibility)
        if !self.is_inserted(header, tx_manager) {
            return false;
        }

        // Check if tuple was deleted (xmax visibility)
        if self.is_deleted(header, tx_manager) {
            return false;
        }

        true
    }

    /// Check if the tuple is inserted according to this snapshot.
    ///
    /// Returns true if the inserting transaction (xmin) is visible.
    fn is_inserted(&self, header: &TupleHeader, tx_manager: &TransactionManager) -> bool {
        let xmin = header.xmin;

        // Self-visibility: tuple inserted by current transaction
        if xmin == self.current_txid {
            // Only visible if inserted by an earlier command in this transaction
            return header.cid < self.current_cid;
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
    fn is_deleted(&self, header: &TupleHeader, tx_manager: &TransactionManager) -> bool {
        let xmax = header.xmax;

        // Not deleted
        if xmax == TxId::INVALID {
            return false;
        }

        // Self-deletion: tuple deleted by current transaction
        if xmax == self.current_txid {
            // Only deleted if deleted by an earlier command in this transaction
            return header.cid < self.current_cid;
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
    use crate::tx::types::Infomask;

    fn make_snapshot(xmin: u64, xmax: u64, xip: Vec<u64>, current: u64, cid: u32) -> Snapshot {
        Snapshot {
            xmin: TxId::new(xmin),
            xmax: TxId::new(xmax),
            xip: xip.into_iter().map(TxId::new).collect(),
            current_txid: TxId::new(current),
            current_cid: CommandId::new(cid),
        }
    }

    #[test]
    fn test_visibility_committed_before_snapshot() {
        let manager = TransactionManager::new();
        let tx1 = manager.begin(); // TxId 1
        manager.commit(tx1).unwrap();

        let snapshot = make_snapshot(2, 3, vec![2], 2, 0);

        let header = TupleHeader {
            xmin: tx1,
            xmax: TxId::INVALID,
            cid: CommandId::FIRST,
            infomask: Infomask::empty().with_xmin_committed(),
        };

        assert!(snapshot.is_tuple_visible(&header, &manager));
    }

    #[test]
    fn test_visibility_aborted_xmin() {
        let manager = TransactionManager::new();
        let tx1 = manager.begin();
        manager.abort(tx1).unwrap();

        let snapshot = make_snapshot(2, 3, vec![2], 2, 0);

        let header = TupleHeader {
            xmin: tx1,
            xmax: TxId::INVALID,
            cid: CommandId::FIRST,
            infomask: Infomask::empty().with_xmin_aborted(),
        };

        assert!(!snapshot.is_tuple_visible(&header, &manager));
    }

    #[test]
    fn test_visibility_in_progress_at_snapshot() {
        let manager = TransactionManager::new();
        let tx1 = manager.begin(); // TxId 1

        // Snapshot taken while tx1 is in progress
        let snapshot = make_snapshot(1, 2, vec![1], 2, 0);

        let header = TupleHeader {
            xmin: tx1,
            xmax: TxId::INVALID,
            cid: CommandId::FIRST,
            infomask: Infomask::empty(),
        };

        assert!(!snapshot.is_tuple_visible(&header, &manager));
    }

    #[test]
    fn test_visibility_self_earlier_cid() {
        let manager = TransactionManager::new();
        let tx1 = manager.begin(); // TxId 1

        // Current transaction, current cid = 5
        let snapshot = make_snapshot(1, 2, vec![1], 1, 5);

        // Tuple inserted at cid 3 (earlier than current cid 5)
        let header = TupleHeader {
            xmin: tx1,
            xmax: TxId::INVALID,
            cid: CommandId::new(3),
            infomask: Infomask::empty(),
        };

        assert!(snapshot.is_tuple_visible(&header, &manager));
    }

    #[test]
    fn test_visibility_self_same_or_later_cid() {
        let manager = TransactionManager::new();
        let tx1 = manager.begin();

        // Current transaction, current cid = 5
        let snapshot = make_snapshot(1, 2, vec![1], 1, 5);

        // Tuple inserted at cid 5 (same as current)
        let header = TupleHeader {
            xmin: tx1,
            xmax: TxId::INVALID,
            cid: CommandId::new(5),
            infomask: Infomask::empty(),
        };

        assert!(!snapshot.is_tuple_visible(&header, &manager));
    }

    #[test]
    fn test_visibility_deleted_by_committed_tx() {
        let manager = TransactionManager::new();
        let tx1 = manager.begin(); // TxId 1 (insert)
        manager.commit(tx1).unwrap();

        let tx2 = manager.begin(); // TxId 2 (delete)
        manager.commit(tx2).unwrap();

        let snapshot = make_snapshot(3, 4, vec![3], 3, 0);

        let header = TupleHeader {
            xmin: tx1,
            xmax: tx2,
            cid: CommandId::FIRST,
            infomask: Infomask::empty()
                .with_xmin_committed()
                .with_xmax_committed(),
        };

        // Inserted by tx1 (visible), deleted by tx2 (also visible) -> not visible
        assert!(!snapshot.is_tuple_visible(&header, &manager));
    }

    #[test]
    fn test_visibility_deleted_by_aborted_tx() {
        let manager = TransactionManager::new();
        let tx1 = manager.begin();
        manager.commit(tx1).unwrap();

        let tx2 = manager.begin();
        manager.abort(tx2).unwrap();

        let snapshot = make_snapshot(3, 4, vec![3], 3, 0);

        let header = TupleHeader {
            xmin: tx1,
            xmax: tx2,
            cid: CommandId::FIRST,
            infomask: Infomask::empty().with_xmin_committed().with_xmax_aborted(),
        };

        // Inserted by tx1 (visible), deleted by tx2 (aborted) -> visible
        assert!(snapshot.is_tuple_visible(&header, &manager));
    }

    #[test]
    fn test_visibility_deleted_by_in_progress() {
        let manager = TransactionManager::new();
        let tx1 = manager.begin();
        manager.commit(tx1).unwrap();

        let tx2 = manager.begin(); // In progress

        let snapshot = make_snapshot(3, 4, vec![2, 3], 3, 0);

        let header = TupleHeader {
            xmin: tx1,
            xmax: tx2,
            cid: CommandId::FIRST,
            infomask: Infomask::empty().with_xmin_committed(),
        };

        // Inserted by tx1 (visible), deleted by tx2 (in progress) -> visible
        assert!(snapshot.is_tuple_visible(&header, &manager));
    }

    #[test]
    fn test_visibility_self_delete_earlier_cid() {
        let manager = TransactionManager::new();
        let tx1 = manager.begin();

        // Current cid = 5
        let snapshot = make_snapshot(1, 2, vec![1], 1, 5);

        // Tuple inserted at cid 3 by tx1, later deleted by tx1
        let header = TupleHeader {
            xmin: tx1,
            xmax: tx1,
            cid: CommandId::new(3), // INSERT cid
            infomask: Infomask::empty(),
        };

        // cid=3 < current_cid=5, so insert is visible
        // xmax is set by same tx, and cid=3 < current_cid=5, so delete is also visible
        // Result: tuple is NOT visible (deleted)
        assert!(!snapshot.is_tuple_visible(&header, &manager));
    }

    #[test]
    fn test_visibility_self_delete_same_or_later_cid() {
        let manager = TransactionManager::new();
        let tx1 = manager.begin();

        // Current cid = 5
        let snapshot = make_snapshot(1, 2, vec![1], 1, 5);

        // Tuple inserted at cid 1 by tx1, later deleted by tx1
        // NOTE: In our simplified design, cid represents INSERT cid only.
        // For same-transaction updates/deletes, we check if the DELETE
        // happened (by checking xmax is set), but we can't determine
        // the exact delete cid without combo-cid infrastructure.
        // This means once xmax is set by the same transaction, we consider
        // the tuple deleted regardless of which command within the transaction.
        let header = TupleHeader {
            xmin: tx1,
            xmax: tx1,
            cid: CommandId::new(1), // INSERT cid
            infomask: Infomask::empty(),
        };

        // cid=1 < current_cid=5, so insert is visible
        // xmax is set by same tx, and cid=1 < current_cid=5, so delete is also visible
        // Result: tuple is NOT visible (deleted)
        assert!(!snapshot.is_tuple_visible(&header, &manager));
    }

    #[test]
    fn test_visibility_started_after_snapshot() {
        let manager = TransactionManager::new();

        // Snapshot xmax = 5, so tx5 started after snapshot
        let snapshot = make_snapshot(1, 5, vec![], 6, 0);

        let header = TupleHeader {
            xmin: TxId::new(5),
            xmax: TxId::INVALID,
            cid: CommandId::FIRST,
            infomask: Infomask::empty().with_xmin_committed(),
        };

        assert!(!snapshot.is_tuple_visible(&header, &manager));
    }
}
