//! Snapshot for MVCC isolation.
//!
//! A snapshot captures the state of committed transactions at a specific point in time,
//! enabling consistent reads without locking.

use super::types::{CommandId, TxId};

/// Snapshot for MVCC visibility determination.
///
/// PostgreSQL-style snapshot with xmin, xmax, and in-progress transaction list.
/// Each statement within a READ COMMITTED transaction gets a fresh snapshot.
#[derive(Debug, Clone)]
pub struct Snapshot {
    /// All transactions < xmin are visible (committed before snapshot).
    pub xmin: TxId,
    /// All transactions >= xmax are invisible (started after snapshot).
    pub xmax: TxId,
    /// Transactions in progress at snapshot time (invisible to this snapshot).
    pub xip: Vec<TxId>,
    /// Current transaction ID (for self-visibility).
    pub current_txid: TxId,
    /// Current command ID within the transaction.
    pub current_cid: CommandId,
}

impl Snapshot {
    /// Check if a transaction is in progress according to this snapshot.
    pub fn is_in_progress(&self, txid: TxId) -> bool {
        self.xip.contains(&txid)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_in_progress() {
        let snapshot = Snapshot {
            xmin: TxId::new(1),
            xmax: TxId::new(5),
            xip: vec![TxId::new(2), TxId::new(3)],
            current_txid: TxId::new(4),
            current_cid: CommandId::FIRST,
        };

        assert!(snapshot.is_in_progress(TxId::new(2)));
        assert!(snapshot.is_in_progress(TxId::new(3)));
        assert!(!snapshot.is_in_progress(TxId::new(1)));
        assert!(!snapshot.is_in_progress(TxId::new(4)));
    }
}
