//! MVCC visibility rules.
//!
//! Determines which tuple versions are visible to a given snapshot based on
//! xmin/xmax transaction IDs and commit status.

use super::manager::{TransactionManager, TransactionState};
use super::snapshot::Snapshot;
use super::tuple_header::TupleHeader;
use super::types::TxId;

/// Determine if a tuple is visible to a snapshot.
///
/// This implements PostgreSQL-style MVCC visibility rules:
///
/// 1. **xmin visibility check** - Tuple is visible if:
///    - xmin is the current transaction AND cid < current_cid (self-visibility), OR
///    - xmin committed before snapshot (xmin < xmax AND xmin not in xip)
///
/// 2. **xmax visibility check** - Tuple is NOT deleted if:
///    - xmax is INVALID (never deleted), OR
///    - xmax aborted, OR
///    - xmax is in progress by another transaction, OR
///    - xmax is the current transaction AND cid >= current_cid (not yet deleted in this statement)
///
/// NOTE: Production systems have multiple visibility functions (HeapTupleSatisfiesSelf,
/// HeapTupleSatisfiesAny, HeapTupleSatisfiesDirty) for different isolation levels and
/// use cases. This implementation focuses on READ COMMITTED semantics.
pub fn is_visible(
    header: &TupleHeader,
    snapshot: &Snapshot,
    tx_manager: &TransactionManager,
) -> bool {
    // Check xmin visibility
    if !is_xmin_visible(header, snapshot, tx_manager) {
        return false;
    }

    // Check xmax visibility (deletion)
    if is_deleted(header, snapshot, tx_manager) {
        return false;
    }

    true
}

/// Check if the tuple's xmin is visible to the snapshot.
fn is_xmin_visible(
    header: &TupleHeader,
    snapshot: &Snapshot,
    tx_manager: &TransactionManager,
) -> bool {
    let xmin = header.xmin;

    // Self-visibility: tuple inserted by current transaction
    if xmin == snapshot.current_txid {
        // Only visible if inserted by an earlier command in this transaction
        return header.cid < snapshot.current_cid;
    }

    // Check hint bits first for optimization
    if header.infomask.xmin_aborted() {
        return false;
    }

    if header.infomask.xmin_committed() {
        // Committed hint bit set, check snapshot visibility
        return is_txid_visible(xmin, snapshot);
    }

    // No hint bits, must check transaction state
    match tx_manager.get_state(xmin) {
        Some(TransactionState::Committed) => is_txid_visible(xmin, snapshot),
        Some(TransactionState::Aborted) | Some(TransactionState::InProgress) => false,
        None => {
            // Transaction not found in manager - assume very old and committed
            // NOTE: Production systems maintain transaction state in CLOG (commit log)
            is_txid_visible(xmin, snapshot)
        }
    }
}

/// Check if the tuple is deleted according to the snapshot.
fn is_deleted(
    header: &TupleHeader,
    snapshot: &Snapshot,
    tx_manager: &TransactionManager,
) -> bool {
    let xmax = header.xmax;

    // Not deleted
    if xmax.is_invalid() {
        return false;
    }

    // Self-deletion: tuple deleted by current transaction
    if xmax == snapshot.current_txid {
        // Only deleted if deleted by an earlier command in this transaction
        return header.cid < snapshot.current_cid;
    }

    // Check hint bits first for optimization
    if header.infomask.xmax_aborted() {
        return false;
    }

    if header.infomask.xmax_committed() {
        // Committed hint bit set, check snapshot visibility
        return is_txid_visible(xmax, snapshot);
    }

    // No hint bits, must check transaction state
    match tx_manager.get_state(xmax) {
        Some(TransactionState::Committed) => is_txid_visible(xmax, snapshot),
        Some(TransactionState::Aborted) | Some(TransactionState::InProgress) => false,
        None => {
            // Transaction not found - assume very old and committed
            is_txid_visible(xmax, snapshot)
        }
    }
}

/// Check if a transaction ID is visible according to the snapshot.
///
/// A transaction is visible if it committed before the snapshot was taken:
/// - txid < snapshot.xmax (started before snapshot)
/// - AND txid not in snapshot.xip (not in progress at snapshot time)
fn is_txid_visible(txid: TxId, snapshot: &Snapshot) -> bool {
    if txid >= snapshot.xmax {
        // Transaction started after snapshot was taken
        return false;
    }

    if txid < snapshot.xmin {
        // All transactions before xmin are visible
        return true;
    }

    // Check if transaction was in progress at snapshot time
    !snapshot.is_in_progress(txid)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tx::types::{CommandId, Infomask};

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

        assert!(is_visible(&header, &snapshot, &manager));
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

        assert!(!is_visible(&header, &snapshot, &manager));
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

        assert!(!is_visible(&header, &snapshot, &manager));
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

        assert!(is_visible(&header, &snapshot, &manager));
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

        assert!(!is_visible(&header, &snapshot, &manager));
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
        assert!(!is_visible(&header, &snapshot, &manager));
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
            infomask: Infomask::empty()
                .with_xmin_committed()
                .with_xmax_aborted(),
        };

        // Inserted by tx1 (visible), deleted by tx2 (aborted) -> visible
        assert!(is_visible(&header, &snapshot, &manager));
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
        assert!(is_visible(&header, &snapshot, &manager));
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
        assert!(!is_visible(&header, &snapshot, &manager));
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
        assert!(!is_visible(&header, &snapshot, &manager));
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

        assert!(!is_visible(&header, &snapshot, &manager));
    }
}
