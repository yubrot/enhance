//! Multi-version catalog cache with MVCC-aware invalidation.
//!
//! The cache maintains a [`VecDeque`] of `(TxId, Option<Arc<Catalog>>)` entries,
//! ordered from oldest to newest. Each entry represents a DDL epoch.
//! `TxId::FROZEN` serves as the universal fallback (always visible to every snapshot).

use std::collections::VecDeque;
use std::sync::Arc;

use parking_lot::RwLock;

use super::error::CatalogError;
use super::snapshot::Catalog;
use super::store::CatalogStore;
use crate::storage::{Replacer, Storage};
use crate::tx::{Snapshot, TransactionManager, TxId, TxState};

/// Shared, MVCC-aware cache for [`Catalog`].
///
/// Maintains a small queue of versioned cache slots keyed by DDL transaction ID.
/// Readers select the most recent entry visible to their MVCC snapshot, avoiding
/// redundant heap scans of `sys_tables` / `sys_columns`.
pub struct CatalogCache {
    inner: RwLock<VecDeque<(TxId, Option<Arc<Catalog>>)>>,
}

impl CatalogCache {
    /// Creates an empty cache with the initial `TxId::FROZEN` entry.
    pub fn new() -> Self {
        let mut deque = VecDeque::with_capacity(2);
        deque.push_back((TxId::FROZEN, None));
        Self {
            inner: RwLock::new(deque),
        }
    }

    /// Registers an in-progress DDL transaction.
    ///
    /// Called after DDL succeeds but **before** commit, so that concurrent
    /// readers can detect the pending schema change.
    pub fn register_ddl(&self, txid: TxId, tx_manager: &TransactionManager) {
        let mut inner = self.inner.write();

        deny_concurrent_ddl(&mut inner, tx_manager);
        clean_up_latest_aborted_entry(&mut inner, tx_manager);

        inner.push_back((txid, None));

        // Keep at most 2 entries: one committed fallback + the new DDL entry.
        while inner.len() > 2 {
            inner.pop_front();
        }
    }

    /// Returns a cached [`Catalog`], or loads a fresh one from the heap.
    pub async fn get_or_load<S: Storage, R: Replacer>(
        &self,
        store: &CatalogStore<S, R>,
        snapshot: &Snapshot,
        tx_manager: &TransactionManager,
    ) -> Result<Arc<Catalog>, CatalogError> {
        // Phase 1: Write lock — find the visible entry (with aborted cleanup).
        {
            let mut inner = self.inner.write();
            if let Some(Some(snap)) = find_visible_entry(&mut inner, snapshot, tx_manager) {
                return Ok(Arc::clone(snap));
            }
        }

        // Phase 2: No lock — load from heap.
        // NOTE: Two threads may concurrently miss the cache and both perform a
        // heap load. This is harmless: Phase 3 re-checks and only one result
        // populates the slot; the other is used directly and discarded.
        let loaded = Arc::new(Catalog::load(store, snapshot).await?);

        // Phase 3: Write lock — re-find and populate if still empty.
        {
            let mut inner = self.inner.write();
            if let Some(slot @ None) = find_visible_entry(&mut inner, snapshot, tx_manager) {
                *slot = Some(Arc::clone(&loaded));
            }
        }

        Ok(loaded)
    }
}

impl Default for CatalogCache {
    fn default() -> Self {
        Self::new()
    }
}

/// Panics if the most recent DDL entry is still in progress, enforcing
/// the serial DDL assumption.
///
/// NOTE: This panic will be replaced by a DDL lock in a future step,
/// which prevents concurrent DDL at a higher level.
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

/// Clean up the tail entry if it was aborted. Only the tail is removed
/// here; non-tail aborted entries are skipped during the scan below and
/// naturally evicted by register_ddl's size limit.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::catalog::tests::test_catalog_store;
    use crate::sql::tests::parse_create_table;
    use crate::tx::CommandId;

    #[tokio::test]
    async fn test_no_ddl_cache_hit() {
        let (store, tx_manager) = test_catalog_store().await;
        let cache = CatalogCache::new();

        let txid = tx_manager.begin();
        let snapshot = tx_manager.snapshot(txid, CommandId::FIRST);

        // First call: cache miss, loads from heap.
        let snap1 = cache
            .get_or_load(&store, &snapshot, &tx_manager)
            .await
            .unwrap();
        assert!(snap1.resolve_table("sys_tables").is_some());

        // Second call: cache hit, returns same Arc.
        let snap2 = cache
            .get_or_load(&store, &snapshot, &tx_manager)
            .await
            .unwrap();
        assert!(Arc::ptr_eq(&snap1, &snap2));
    }

    #[tokio::test]
    async fn test_ddl_commit_invalidation() {
        let (store, tx_manager) = test_catalog_store().await;
        let cache = CatalogCache::new();

        // Populate cache.
        let tx1 = tx_manager.begin();
        let snap1 = tx_manager.snapshot(tx1, CommandId::FIRST);
        let initial = cache
            .get_or_load(&store, &snap1, &tx_manager)
            .await
            .unwrap();
        assert!(initial.resolve_table("test_tbl").is_none());
        let _ = tx_manager.abort(tx1);

        // DDL: create table.
        let ddl_txid = tx_manager.begin();
        let cid = CommandId::FIRST;
        let stmt = parse_create_table("CREATE TABLE test_tbl (id INTEGER)");
        store.create_table(ddl_txid, cid, &stmt).await.unwrap();

        // Register DDL before commit.
        cache.register_ddl(ddl_txid, &tx_manager);
        tx_manager.commit(ddl_txid).unwrap();

        // New snapshot should see the DDL.
        let tx2 = tx_manager.begin();
        let snap2 = tx_manager.snapshot(tx2, CommandId::FIRST);
        let refreshed = cache
            .get_or_load(&store, &snap2, &tx_manager)
            .await
            .unwrap();

        // Should NOT be the same Arc (cache was invalidated).
        assert!(!Arc::ptr_eq(&initial, &refreshed));
        assert!(refreshed.resolve_table("test_tbl").is_some());
    }

    #[tokio::test]
    async fn test_ddl_abort_preserves_cache() {
        let (store, tx_manager) = test_catalog_store().await;
        let cache = CatalogCache::new();

        // Populate cache.
        let tx1 = tx_manager.begin();
        let snap1 = tx_manager.snapshot(tx1, CommandId::FIRST);
        let cached = cache
            .get_or_load(&store, &snap1, &tx_manager)
            .await
            .unwrap();
        let _ = tx_manager.abort(tx1);

        // DDL that gets aborted.
        let ddl_txid = tx_manager.begin();
        let cid = CommandId::FIRST;
        let stmt = parse_create_table("CREATE TABLE vanish (id INTEGER)");
        store.create_table(ddl_txid, cid, &stmt).await.unwrap();
        cache.register_ddl(ddl_txid, &tx_manager);
        let _ = tx_manager.abort(ddl_txid);

        // After abort, the aborted entry is cleaned up and the original
        // cached catalog is returned (no redundant heap scan).
        let tx2 = tx_manager.begin();
        let snap2 = tx_manager.snapshot(tx2, CommandId::FIRST);
        let after = cache
            .get_or_load(&store, &snap2, &tx_manager)
            .await
            .unwrap();
        assert!(Arc::ptr_eq(&cached, &after));
        assert!(after.resolve_table("vanish").is_none());
    }

    #[tokio::test]
    async fn test_self_ddl_bypass() {
        let (store, tx_manager) = test_catalog_store().await;
        let cache = CatalogCache::new();

        // Populate cache.
        let tx0 = tx_manager.begin();
        let snap0 = tx_manager.snapshot(tx0, CommandId::FIRST);
        let _ = cache
            .get_or_load(&store, &snap0, &tx_manager)
            .await
            .unwrap();
        let _ = tx_manager.abort(tx0);

        // Start a DDL transaction.
        let ddl_txid = tx_manager.begin();
        let cid = CommandId::FIRST;
        let stmt = parse_create_table("CREATE TABLE self_tbl (id INTEGER)");
        store.create_table(ddl_txid, cid, &stmt).await.unwrap();
        cache.register_ddl(ddl_txid, &tx_manager);

        // Self-DDL: the same txid should get a fresh load,
        // NOT the shared cache.
        let self_snapshot = tx_manager.snapshot(ddl_txid, cid.next());
        let self_catalog = cache
            .get_or_load(&store, &self_snapshot, &tx_manager)
            .await
            .unwrap();
        // The self-DDL result should see the uncommitted table.
        assert!(self_catalog.resolve_table("self_tbl").is_some());

        // But the shared cache should NOT have been updated.
        let tx2 = tx_manager.begin();
        let snap2 = tx_manager.snapshot(tx2, CommandId::FIRST);
        let shared = cache
            .get_or_load(&store, &snap2, &tx_manager)
            .await
            .unwrap();
        // Other transactions can't see the uncommitted DDL.
        assert!(shared.resolve_table("self_tbl").is_none());
    }
}
