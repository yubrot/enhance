//! LRU page replacement policy.

use super::frame::FrameId;
use std::collections::{HashMap, VecDeque};
use std::sync::Mutex;

/// LRU (Least Recently Used) page replacement policy.
///
/// Tracks unpinned frames and selects victims for eviction based on
/// least-recently-used ordering.
///
/// # Design
///
/// Uses a combination of:
/// - VecDeque for LRU ordering (front = oldest, back = newest)
/// - HashMap for O(1) membership check and removal
///
/// When a frame is:
/// - **Unpinned (pin_count becomes 0)**: Add to LRU list
/// - **Pinned (accessed again)**: Remove from LRU list
/// - **Evicted**: Remove from LRU list and return as victim
pub struct LruReplacer {
    /// LRU list: front = least recently used (evict first)
    list: Mutex<VecDeque<FrameId>>,
    /// Set of frames currently in the LRU list (for O(1) removal check)
    in_list: Mutex<HashMap<FrameId, ()>>,
}

impl LruReplacer {
    /// Creates a new LRU replacer.
    pub fn new() -> Self {
        Self {
            list: Mutex::new(VecDeque::new()),
            in_list: Mutex::new(HashMap::new()),
        }
    }

    /// Selects a victim frame for eviction.
    ///
    /// Returns the FrameId of the least recently used frame, or None
    /// if no frames are available for eviction.
    pub fn victim(&self) -> Option<FrameId> {
        let mut list = self.list.lock().unwrap();
        let mut in_list = self.in_list.lock().unwrap();

        if let Some(frame_id) = list.pop_front() {
            in_list.remove(&frame_id);
            Some(frame_id)
        } else {
            None
        }
    }

    /// Pins a frame, removing it from the replacer.
    ///
    /// Called when a frame's pin_count increases from 0.
    pub fn pin(&self, frame_id: FrameId) {
        let mut list = self.list.lock().unwrap();
        let mut in_list = self.in_list.lock().unwrap();

        if in_list.remove(&frame_id).is_some() {
            // O(n) removal - acceptable for typical pool sizes
            // For very large pools, consider using a linked list with node pointers
            list.retain(|&id| id != frame_id);
        }
    }

    /// Unpins a frame, adding it to the replacer.
    ///
    /// Called when a frame's pin_count decreases to 0.
    pub fn unpin(&self, frame_id: FrameId) {
        let mut list = self.list.lock().unwrap();
        let mut in_list = self.in_list.lock().unwrap();

        // Only add if not already in list
        if let std::collections::hash_map::Entry::Vacant(e) = in_list.entry(frame_id) {
            e.insert(());
            list.push_back(frame_id);
        }
    }

    /// Returns the number of frames that can be evicted.
    #[allow(dead_code)]
    pub fn size(&self) -> usize {
        self.list.lock().unwrap().len()
    }
}

impl Default for LruReplacer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_replacer_empty() {
        let replacer = LruReplacer::new();
        assert_eq!(replacer.size(), 0);
        assert_eq!(replacer.victim(), None);
    }

    #[test]
    fn test_victim_returns_oldest() {
        let replacer = LruReplacer::new();

        replacer.unpin(FrameId::new(0));
        replacer.unpin(FrameId::new(1));
        replacer.unpin(FrameId::new(2));

        assert_eq!(replacer.size(), 3);
        assert_eq!(replacer.victim(), Some(FrameId::new(0)));
        assert_eq!(replacer.size(), 2);
        assert_eq!(replacer.victim(), Some(FrameId::new(1)));
        assert_eq!(replacer.size(), 1);
        assert_eq!(replacer.victim(), Some(FrameId::new(2)));
        assert_eq!(replacer.size(), 0);
        assert_eq!(replacer.victim(), None);
    }

    #[test]
    fn test_pin_removes_from_list() {
        let replacer = LruReplacer::new();

        replacer.unpin(FrameId::new(0));
        replacer.unpin(FrameId::new(1));
        replacer.unpin(FrameId::new(2));

        assert_eq!(replacer.size(), 3);

        replacer.pin(FrameId::new(1)); // Remove middle element

        assert_eq!(replacer.size(), 2);
        assert_eq!(replacer.victim(), Some(FrameId::new(0)));
        assert_eq!(replacer.victim(), Some(FrameId::new(2)));
        assert_eq!(replacer.victim(), None);
    }

    #[test]
    fn test_double_unpin_no_duplicate() {
        let replacer = LruReplacer::new();

        replacer.unpin(FrameId::new(0));
        replacer.unpin(FrameId::new(0)); // Second unpin should be no-op

        assert_eq!(replacer.size(), 1);
        assert_eq!(replacer.victim(), Some(FrameId::new(0)));
        assert_eq!(replacer.victim(), None);
    }

    #[test]
    fn test_pin_non_existent_is_noop() {
        let replacer = LruReplacer::new();

        replacer.unpin(FrameId::new(0));
        replacer.pin(FrameId::new(1)); // Pin a frame that's not in the list

        assert_eq!(replacer.size(), 1);
        assert_eq!(replacer.victim(), Some(FrameId::new(0)));
    }

    #[test]
    fn test_lru_order() {
        let replacer = LruReplacer::new();

        // Add frames
        replacer.unpin(FrameId::new(0));
        replacer.unpin(FrameId::new(1));
        replacer.unpin(FrameId::new(2));

        // Pin and re-unpin frame 0 (should move to back)
        replacer.pin(FrameId::new(0));
        replacer.unpin(FrameId::new(0));

        // Now order should be: 1, 2, 0
        assert_eq!(replacer.victim(), Some(FrameId::new(1)));
        assert_eq!(replacer.victim(), Some(FrameId::new(2)));
        assert_eq!(replacer.victim(), Some(FrameId::new(0)));
    }
}
