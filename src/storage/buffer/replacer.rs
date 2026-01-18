//! Page replacement policies for the buffer pool.
//!
//! This module provides the `Replacer` trait for pluggable eviction policies,
//! along with the `LruReplacer` implementation.

use std::collections::{HashSet, VecDeque};

use super::frame::FrameId;

/// Page replacement policy trait.
///
/// A replacer tracks which frames are candidates for eviction. When a frame
/// is unpinned (pin_count reaches 0), it becomes eligible for eviction.
/// When a frame is pinned again, it should be removed from eviction candidates.
///
/// # Implementation Notes
///
/// Implementations must be `Send + Sync` to work with the async buffer pool.
/// The replacer is accessed while holding the buffer pool's state lock.
///
/// NOTE: For production, consider implementing additional policies:
/// - Clock (CLOCK): Approximates LRU with lower overhead
/// - LRU-K: Tracks K most recent accesses for better prediction
/// - 2Q: Separates first-access pages from frequently accessed pages
pub trait Replacer: Send + Sync {
    /// Records that a frame was unpinned and is now evictable.
    ///
    /// If the frame is already in the replacer, its position may be updated
    /// based on the policy (e.g., moved to MRU position for LRU).
    fn unpin(&mut self, frame_id: FrameId);

    /// Records that a frame was pinned and should not be evicted.
    ///
    /// Removes the frame from eviction candidates if present.
    fn pin(&mut self, frame_id: FrameId);

    /// Removes and returns a frame to evict based on the policy.
    ///
    /// Returns `None` if there are no evictable frames.
    fn evict(&mut self) -> Option<FrameId>;

    /// Returns the number of frames currently tracked as evictable.
    fn size(&self) -> usize;
}

/// LRU (Least Recently Used) page replacement policy.
///
/// Tracks unpinned frames in LRU order. When a frame is unpinned,
/// it is added to the MRU (most recently used) position. The least
/// recently unpinned frame is evicted first when space is needed.
///
/// # Implementation
///
/// Uses a `VecDeque` for O(1) eviction from front and O(1) insertion at back.
/// A `HashSet` provides O(1) membership testing for the `pin` operation.
///
/// NOTE: For production with larger buffer pools, consider:
/// - Using an intrusive linked list to avoid HashMap overhead
/// - Implementing the Clock algorithm for O(1) operations without hashing
pub struct LruReplacer {
    /// Frames in LRU order (front = least recently used).
    lru_list: VecDeque<FrameId>,

    /// Set of frames in lru_list for O(1) membership testing.
    frame_set: HashSet<FrameId>,
}

impl LruReplacer {
    /// Creates a new LRU replacer with the given capacity.
    ///
    /// The capacity is used to pre-allocate internal data structures.
    pub fn new(capacity: usize) -> Self {
        Self {
            lru_list: VecDeque::with_capacity(capacity),
            frame_set: HashSet::with_capacity(capacity),
        }
    }
}

impl Replacer for LruReplacer {
    fn unpin(&mut self, frame_id: FrameId) {
        // If already present, remove it first to update position
        if self.frame_set.contains(&frame_id) {
            self.lru_list.retain(|&id| id != frame_id);
        } else {
            self.frame_set.insert(frame_id);
        }

        // Add to back (most recently used position)
        self.lru_list.push_back(frame_id);
    }

    fn pin(&mut self, frame_id: FrameId) {
        if self.frame_set.remove(&frame_id) {
            self.lru_list.retain(|&id| id != frame_id);
        }
    }

    fn evict(&mut self) -> Option<FrameId> {
        // Remove from front (least recently used)
        if let Some(frame_id) = self.lru_list.pop_front() {
            self.frame_set.remove(&frame_id);
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

        // Should evict in LRU order: 0, 1, 2
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

        // Pin frame 1, removing it from eviction candidates
        replacer.pin(1);

        assert_eq!(replacer.size(), 2);

        // Should evict 0 and 2, skipping 1
        assert_eq!(replacer.evict(), Some(0));
        assert_eq!(replacer.evict(), Some(2));
        assert_eq!(replacer.evict(), None);
    }

    #[test]
    fn test_pin_not_present() {
        let mut replacer = LruReplacer::new(3);

        // Pin a frame that's not in the replacer (should be a no-op)
        replacer.pin(42);

        assert_eq!(replacer.size(), 0);
    }

    #[test]
    fn test_unpin_updates_lru_order() {
        let mut replacer = LruReplacer::new(3);

        replacer.unpin(0);
        replacer.unpin(1);
        replacer.unpin(2);

        // Unpin frame 0 again, moving it to MRU position
        replacer.unpin(0);

        assert_eq!(replacer.size(), 3);

        // LRU order should now be: 1, 2, 0
        assert_eq!(replacer.evict(), Some(1));
        assert_eq!(replacer.evict(), Some(2));
        assert_eq!(replacer.evict(), Some(0));
    }

    #[test]
    fn test_unpin_same_frame_multiple_times() {
        let mut replacer = LruReplacer::new(3);

        replacer.unpin(0);
        replacer.unpin(0);
        replacer.unpin(0);

        // Should only have one entry for frame 0
        assert_eq!(replacer.size(), 1);
        assert_eq!(replacer.evict(), Some(0));
        assert_eq!(replacer.evict(), None);
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

        // Simulate typical buffer pool usage pattern
        replacer.unpin(0);
        replacer.unpin(1);
        replacer.pin(0); // Re-pin frame 0
        replacer.unpin(2);
        replacer.unpin(0); // Unpin frame 0 again

        // LRU order should be: 1, 2, 0
        assert_eq!(replacer.evict(), Some(1));

        replacer.unpin(3);

        // LRU order should be: 2, 0, 3
        assert_eq!(replacer.evict(), Some(2));
        assert_eq!(replacer.evict(), Some(0));
        assert_eq!(replacer.evict(), Some(3));
    }
}
