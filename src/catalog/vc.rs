//! MVCC-aware catalog version cache.

use std::collections::VecDeque;
use std::sync::Arc;

use parking_lot::RwLock;

use super::Catalog;
use crate::tx::{Snapshot, TransactionManager, TxId, TxState};

/// MVCC-aware catalog version cache.
///
/// The cache avoids redundant heap scans when no DDL has been committed since
/// the last load. Self-DDL snapshots bypass the cache entirely to see their
/// own uncommitted schema changes.
pub struct CatalogVC {
    entries: RwLock<VecDeque<(TxId, Option<Arc<Catalog>>)>>,
}

impl Default for CatalogVC {
    fn default() -> Self {
        Self::new()
    }
}

impl CatalogVC {
    /// Creates a new `CatalogVC`.
    pub fn new() -> Self {
        let mut deque = VecDeque::with_capacity(2);
        deque.push_back((TxId::FROZEN, None));
        Self {
            entries: RwLock::new(deque),
        }
    }

    /// Returns a cached [`Catalog`] visible to the given MVCC snapshot.
    ///
    /// Returns `None` on cache miss (slot exists but is not yet populated)
    /// or when the snapshot belongs to the DDL transaction itself (self-DDL
    /// bypass).
    pub fn get(
        &self,
        snapshot: &Snapshot,
        tx_manager: &TransactionManager,
    ) -> Option<Arc<Catalog>> {
        let mut entries = self.entries.write();
        if let Some(Some(catalog)) = find_visible_entry(&mut entries, snapshot, tx_manager) {
            Some(Arc::clone(catalog))
        } else {
            None
        }
    }

    /// Populates the cache slot for the given snapshot if it is still empty.
    ///
    /// Called after loading a [`Catalog`] from the heap. If two threads race
    /// past a cache miss, only the first caller's catalog fills the slot;
    /// the second caller's catalog is silently discarded.
    pub fn try_populate(
        &self,
        snapshot: &Snapshot,
        tx_manager: &TransactionManager,
        catalog: Arc<Catalog>,
    ) {
        let mut entries = self.entries.write();
        if let Some(slot @ None) = find_visible_entry(&mut entries, snapshot, tx_manager) {
            *slot = Some(catalog);
        }
    }

    /// Registers an in-progress DDL transaction in the cache.
    ///
    /// Called after DDL succeeds but **before** commit, so that concurrent
    /// readers can detect the pending schema change. Panics if another DDL
    /// transaction is still in progress (serial DDL assumption).
    ///
    /// NOTE: This panic will be replaced by a DDL lock in a future step,
    /// which prevents concurrent DDL at a higher level.
    pub fn register_ddl(&self, txid: TxId, tx_manager: &TransactionManager) {
        let mut entries = self.entries.write();

        deny_concurrent_ddl(&mut entries, tx_manager);
        clean_up_latest_aborted_entry(&mut entries, tx_manager);

        entries.push_back((txid, None));

        // Keep at most 2 entries: one committed fallback + the new DDL entry.
        while entries.len() > 2 {
            entries.pop_front();
        }
    }
}

/// Finds the most recent cache entry visible to the given MVCC snapshot.
///
/// Returns `Some(slot)` for the best visible committed entry (which may
/// or may not contain a cached catalog), or `None` for self-DDL and
/// stale-read scenarios where the cache must be bypassed.
fn find_visible_entry<'a>(
    entries: &'a mut VecDeque<(TxId, Option<Arc<Catalog>>)>,
    snapshot: &Snapshot,
    tx_manager: &TransactionManager,
) -> Option<&'a mut Option<Arc<Catalog>>> {
    clean_up_latest_aborted_entry(entries, tx_manager);

    for (txid, slot) in entries.iter_mut().rev() {
        // Self-DDL: must bypass cache (uncommitted schema change).
        if *txid == snapshot.current_txid {
            return None;
        }
        // Accept only committed DDLs visible to this snapshot.
        // Aborted and in-progress entries are skipped.
        if snapshot.is_txid_visible(*txid) && tx_manager.state(*txid) == TxState::Committed {
            return Some(slot);
        }
    }

    None
}

/// Panics if the most recent DDL entry is still in progress, enforcing
/// the serial DDL assumption.
fn deny_concurrent_ddl(
    entries: &mut VecDeque<(TxId, Option<Arc<Catalog>>)>,
    tx_manager: &TransactionManager,
) {
    if let Some(&(txid, _)) = entries.back()
        && tx_manager.state(txid) == TxState::InProgress
    {
        panic!(
            "Concurrent DDL: cannot register DDL while {} is still in progress",
            txid
        );
    }
}

/// Cleans up the tail entry if it was aborted. Only the tail is removed
/// here; non-tail aborted entries are skipped during the scan and
/// naturally evicted by `register_ddl`'s size limit.
fn clean_up_latest_aborted_entry(
    entries: &mut VecDeque<(TxId, Option<Arc<Catalog>>)>,
    tx_manager: &TransactionManager,
) {
    if entries.len() > 1
        && let Some(&(txid, _)) = entries.back()
        && tx_manager.state(txid) == TxState::Aborted
    {
        entries.pop_back();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tx::CommandId;

    /// Helper: creates a minimal `Catalog` (no tables/columns).
    fn empty_catalog() -> Arc<Catalog> {
        Arc::new(Catalog::new(vec![], vec![]))
    }

    #[test]
    fn test_cache_hit() {
        let tm = TransactionManager::new();
        let vc = CatalogVC::new();
        let txid = tm.begin();
        let snap = tm.snapshot(txid, CommandId::FIRST);

        // Initially a cache miss.
        assert!(vc.get(&snap, &tm).is_none());

        // Populate the cache.
        let catalog = empty_catalog();
        vc.try_populate(&snap, &tm, Arc::clone(&catalog));

        // Now it should be a cache hit returning the same Arc.
        let cached = vc.get(&snap, &tm).expect("expected cache hit");
        assert!(Arc::ptr_eq(&catalog, &cached));
    }

    #[test]
    fn test_ddl_invalidation() {
        let tm = TransactionManager::new();
        let vc = CatalogVC::new();

        // Populate the cache for a baseline snapshot.
        let tx1 = tm.begin();
        let snap1 = tm.snapshot(tx1, CommandId::FIRST);
        let old_catalog = empty_catalog();
        vc.try_populate(&snap1, &tm, Arc::clone(&old_catalog));
        let _ = tm.abort(tx1);

        // Perform a DDL and commit.
        let ddl_txid = tm.begin();
        vc.register_ddl(ddl_txid, &tm);
        tm.commit(ddl_txid).unwrap();

        // A new snapshot should see a cache miss (new DDL slot is empty).
        let tx2 = tm.begin();
        let snap2 = tm.snapshot(tx2, CommandId::FIRST);
        assert!(vc.get(&snap2, &tm).is_none());
    }

    #[test]
    fn test_ddl_abort() {
        let tm = TransactionManager::new();
        let vc = CatalogVC::new();

        // Populate the cache.
        let tx1 = tm.begin();
        let snap1 = tm.snapshot(tx1, CommandId::FIRST);
        let cached = empty_catalog();
        vc.try_populate(&snap1, &tm, Arc::clone(&cached));
        let _ = tm.abort(tx1);

        // DDL that gets aborted.
        let ddl_txid = tm.begin();
        vc.register_ddl(ddl_txid, &tm);
        let _ = tm.abort(ddl_txid);

        // After abort, the aborted entry is cleaned up and the original
        // cached catalog is returned.
        let tx2 = tm.begin();
        let snap2 = tm.snapshot(tx2, CommandId::FIRST);
        let after = vc.get(&snap2, &tm).expect("expected cache hit");
        assert!(Arc::ptr_eq(&cached, &after));
    }

    #[test]
    fn test_self_ddl_bypass() {
        let tm = TransactionManager::new();
        let vc = CatalogVC::new();

        // Populate the cache.
        let tx0 = tm.begin();
        let snap0 = tm.snapshot(tx0, CommandId::FIRST);
        vc.try_populate(&snap0, &tm, empty_catalog());
        let _ = tm.abort(tx0);

        // Start a DDL transaction and register it.
        let ddl_txid = tm.begin();
        vc.register_ddl(ddl_txid, &tm);

        // Self-DDL snapshot should bypass the cache.
        let self_snap = tm.snapshot(ddl_txid, CommandId::FIRST.next());
        assert!(vc.get(&self_snap, &tm).is_none());

        // Other transactions should still get the cached catalog.
        let tx2 = tm.begin();
        let snap2 = tm.snapshot(tx2, CommandId::FIRST);
        assert!(vc.get(&snap2, &tm).is_some());
    }

    #[test]
    #[should_panic(expected = "Concurrent DDL")]
    fn test_concurrent_ddl_panics() {
        let tm = TransactionManager::new();
        let vc = CatalogVC::new();

        let ddl1 = tm.begin();
        vc.register_ddl(ddl1, &tm);

        // Attempting a second DDL while the first is in progress should panic.
        let ddl2 = tm.begin();
        vc.register_ddl(ddl2, &tm);
    }
}
