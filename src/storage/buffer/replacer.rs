//! Page replacement policies for the buffer pool.

#[cfg(debug_assertions)]
use std::collections::HashSet;
use std::collections::VecDeque;

use super::frame::FrameId;

/// Page replacement policy trait.
///
/// Tracks frames eligible for eviction. Frames become evictable when unpinned
/// (pin_count = 0) and are removed from candidates when pinned again.
///
/// # Usage Contract
///
/// - `unpin(frame_id)`: Called when pin_count transitions from 1 → 0
/// - `pin(frame_id)`: Called when pin_count transitions from 0 → 1
/// - Each method is called exactly once per transition
/// - Frames are guaranteed to be in the correct state (not already present/absent)
///
/// Implementations must be `Send + Sync` for the async buffer pool.
pub trait Replacer: Send + Sync {
    /// Marks a frame as evictable (pin_count 1 → 0).
    fn unpin(&mut self, frame_id: FrameId);

    /// Removes a frame from eviction candidates (pin_count 0 → 1).
    fn pin(&mut self, frame_id: FrameId);

    /// Evicts and returns a frame, or `None` if no frames are evictable.
    fn evict(&mut self) -> Option<FrameId>;

    /// Returns the number of evictable frames.
    fn size(&self) -> usize;
}

/// LRU (Least Recently Used) page replacement policy.
///
/// Evicts the least recently unpinned frame. Uses `VecDeque` for O(1) operations.
/// Debug builds include a `HashSet` for contract verification.
pub struct LruReplacer {
    /// Frames in LRU order (front = LRU).
    lru_list: VecDeque<FrameId>,

    /// Frame set for contract verification (debug only).
    #[cfg(debug_assertions)]
    frame_set: HashSet<FrameId>,
}

impl LruReplacer {
    /// Creates a new LRU replacer with pre-allocated capacity.
    pub fn new(capacity: usize) -> Self {
        Self {
            lru_list: VecDeque::with_capacity(capacity),
            #[cfg(debug_assertions)]
            frame_set: HashSet::with_capacity(capacity),
        }
    }
}

impl Replacer for LruReplacer {
    fn unpin(&mut self, frame_id: FrameId) {
        #[cfg(debug_assertions)]
        {
            let was_inserted = self.frame_set.insert(frame_id);
            debug_assert!(was_inserted, "unpin called on frame already in replacer");
        }
        self.lru_list.push_back(frame_id);
    }

    fn pin(&mut self, frame_id: FrameId) {
        #[cfg(debug_assertions)]
        {
            let was_removed = self.frame_set.remove(&frame_id);
            debug_assert!(was_removed, "pin called on frame not in replacer");
        }
        self.lru_list.retain(|&id| id != frame_id);
    }

    fn evict(&mut self) -> Option<FrameId> {
        if let Some(frame_id) = self.lru_list.pop_front() {
            #[cfg(debug_assertions)]
            {
                let was_removed = self.frame_set.remove(&frame_id);
                debug_assert!(was_removed, "evicted frame not in frame_set");
            }
            Some(frame_id)
        } else {
            None
        }
    }

    fn size(&self) -> usize {
        self.lru_list.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lru_replacer_new() {
        let replacer = LruReplacer::new(10);
        assert_eq!(replacer.size(), 0);
    }

    #[test]
    fn test_evict_empty() {
        let mut replacer = LruReplacer::new(3);
        assert_eq!(replacer.evict(), None);
    }

    #[test]
    fn test_evict_lru_order() {
        let mut replacer = LruReplacer::new(3);

        replacer.unpin(0);
        replacer.unpin(1);
        replacer.unpin(2);

        assert_eq!(replacer.size(), 3);
        assert_eq!(replacer.evict(), Some(0));
        assert_eq!(replacer.evict(), Some(1));
        assert_eq!(replacer.evict(), Some(2));
        assert_eq!(replacer.evict(), None);
        assert_eq!(replacer.size(), 0);
    }

    #[test]
    fn test_pin_removes_from_eviction() {
        let mut replacer = LruReplacer::new(3);

        replacer.unpin(0);
        replacer.unpin(1);
        replacer.unpin(2);

        replacer.pin(1);

        assert_eq!(replacer.size(), 2);
        assert_eq!(replacer.evict(), Some(0));
        assert_eq!(replacer.evict(), Some(2));
        assert_eq!(replacer.evict(), None);
    }

    #[test]
    fn test_pin_unpin_updates_lru_order() {
        let mut replacer = LruReplacer::new(3);

        replacer.unpin(0);
        replacer.unpin(1);
        replacer.unpin(2);

        replacer.pin(0);
        replacer.unpin(0);

        assert_eq!(replacer.size(), 3);
        assert_eq!(replacer.evict(), Some(1));
        assert_eq!(replacer.evict(), Some(2));
        assert_eq!(replacer.evict(), Some(0));
    }

    #[test]
    fn test_pin_unpin_cycle() {
        let mut replacer = LruReplacer::new(3);

        replacer.unpin(0);
        assert_eq!(replacer.size(), 1);

        replacer.pin(0);
        assert_eq!(replacer.size(), 0);

        replacer.unpin(0);
        assert_eq!(replacer.size(), 1);

        assert_eq!(replacer.evict(), Some(0));
    }

    #[test]
    fn test_interleaved_operations() {
        let mut replacer = LruReplacer::new(5);

        replacer.unpin(0);
        replacer.unpin(1);
        replacer.pin(0);
        replacer.unpin(2);
        replacer.unpin(0);

        assert_eq!(replacer.evict(), Some(1));

        replacer.unpin(3);

        assert_eq!(replacer.evict(), Some(2));
        assert_eq!(replacer.evict(), Some(0));
        assert_eq!(replacer.evict(), Some(3));
    }
}
