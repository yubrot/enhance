//! Page replacement policies for the buffer pool.
//!
//! The replacer tracks which frames are evictable (unpinned) and selects
//! victims for eviction when the buffer pool needs free frames.

use super::frame::FrameId;
use std::collections::{HashSet, VecDeque};

/// Trait for page replacement policies.
///
/// The replacer tracks which frames are evictable (unpinned) and selects
/// victims for eviction when the buffer pool needs free frames.
///
/// # Thread Safety
///
/// Implementations must be thread-safe. The BufferPoolManager will protect
/// the replacer with a Mutex.
///
/// # Usage
///
/// ```text
/// // When a page's pin_count drops to 0
/// replacer.unpin(frame_id);
///
/// // When a page's pin_count increases from 0
/// replacer.pin(frame_id);
///
/// // When the buffer pool needs a victim
/// if let Some(victim) = replacer.victim() {
///     // Evict the victim frame
/// }
/// ```
pub trait Replacer: Send {
    /// Selects a victim frame for eviction.
    ///
    /// Returns `Some(frame_id)` if there's an evictable frame, `None` if all
    /// frames are pinned.
    ///
    /// The returned frame is removed from the replacer's tracking.
    fn victim(&mut self) -> Option<FrameId>;

    /// Marks a frame as non-evictable (pinned).
    ///
    /// Called when a frame's pin_count increases from 0 to 1.
    /// If the frame is not in the replacer, this is a no-op.
    fn pin(&mut self, frame_id: FrameId);

    /// Marks a frame as evictable (unpinned).
    ///
    /// Called when a frame's pin_count decreases to 0.
    /// The frame is added to the back of the LRU queue.
    fn unpin(&mut self, frame_id: FrameId);

    /// Returns the number of evictable frames.
    fn size(&self) -> usize;
}

/// LRU (Least Recently Used) page replacement policy.
///
/// Frames are ordered by recency of unpin. When `victim()` is called,
/// the least recently unpinned frame is selected.
///
/// # Data Structure
///
/// Uses a combination of:
/// - `VecDeque<FrameId>` for the LRU order (front = oldest)
/// - `HashSet<FrameId>` for O(1) membership testing
///
/// # Lazy Removal
///
/// When `pin()` is called, the frame is removed from `in_queue` but not
/// from `lru_queue`. This avoids expensive O(n) search in the deque.
/// Stale entries are cleaned up during `victim()` calls.
///
/// # Example
///
/// ```no_run
/// use enhance::storage::buffer::{LruReplacer, Replacer, FrameId};
///
/// let mut replacer = LruReplacer::new();
///
/// // Mark frames as evictable
/// replacer.unpin(FrameId::new(0));
/// replacer.unpin(FrameId::new(1));
/// replacer.unpin(FrameId::new(2));
///
/// // Select victim (oldest)
/// assert_eq!(replacer.victim(), Some(FrameId::new(0)));
///
/// // Pin frame 1
/// replacer.pin(FrameId::new(1));
///
/// // Victim should skip pinned frame 1
/// assert_eq!(replacer.victim(), Some(FrameId::new(2)));
/// ```
pub struct LruReplacer {
    /// Frames in LRU order. Front = least recently used.
    lru_queue: VecDeque<FrameId>,

    /// Set of frames currently in the evictable set for O(1) lookup.
    ///
    /// This set is the source of truth for whether a frame is evictable.
    /// `lru_queue` may contain stale entries that have been pinned.
    in_queue: HashSet<FrameId>,
}

impl LruReplacer {
    /// Creates a new LRU replacer.
    ///
    /// # Example
    ///
    /// ```
    /// use enhance::storage::buffer::{LruReplacer, Replacer};
    ///
    /// let replacer = LruReplacer::new();
    /// assert_eq!(replacer.size(), 0);
    /// ```
    pub fn new() -> Self {
        Self {
            lru_queue: VecDeque::new(),
            in_queue: HashSet::new(),
        }
    }

    /// Creates a new LRU replacer with a specified capacity hint.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The expected number of frames (used for pre-allocation)
    ///
    /// # Example
    ///
    /// ```
    /// use enhance::storage::buffer::{LruReplacer, Replacer};
    ///
    /// let replacer = LruReplacer::with_capacity(100);
    /// assert_eq!(replacer.size(), 0);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            lru_queue: VecDeque::with_capacity(capacity),
            in_queue: HashSet::with_capacity(capacity),
        }
    }
}

impl Default for LruReplacer {
    fn default() -> Self {
        Self::new()
    }
}

impl Replacer for LruReplacer {
    fn victim(&mut self) -> Option<FrameId> {
        // Pop from front until we find an evictable frame
        while let Some(frame_id) = self.lru_queue.pop_front() {
            if self.in_queue.remove(&frame_id) {
                return Some(frame_id);
            }
            // Frame was pinned and removed from in_queue but not lru_queue
            // Continue to next candidate (lazy removal cleanup)
        }
        None
    }

    fn pin(&mut self, frame_id: FrameId) {
        // Remove from in_queue but leave in lru_queue (lazy removal)
        self.in_queue.remove(&frame_id);
    }

    fn unpin(&mut self, frame_id: FrameId) {
        // If already unpinned, no-op
        if self.in_queue.contains(&frame_id) {
            return;
        }

        // Remove stale entry from queue if it exists (O(n) operation).
        // This can happen if the frame was previously pinned after being unpinned.
        // While this is O(n), it ensures the LRU order is correct and prevents
        // the queue from accumulating stale entries.
        if let Some(pos) = self.lru_queue.iter().position(|&id| id == frame_id) {
            self.lru_queue.remove(pos);
        }

        // Add to back (most recently unpinned)
        self.lru_queue.push_back(frame_id);
        self.in_queue.insert(frame_id);
    }

    fn size(&self) -> usize {
        self.in_queue.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_replacer_is_empty() {
        let replacer = LruReplacer::new();
        assert_eq!(replacer.size(), 0);
    }

    #[test]
    fn test_victim_returns_oldest() {
        let mut replacer = LruReplacer::new();
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
    }

    #[test]
    fn test_victim_empty_returns_none() {
        let mut replacer = LruReplacer::new();
        assert_eq!(replacer.victim(), None);
    }

    #[test]
    fn test_pin_removes_from_eviction() {
        let mut replacer = LruReplacer::new();
        replacer.unpin(FrameId::new(0));
        replacer.unpin(FrameId::new(1));
        replacer.unpin(FrameId::new(2));

        replacer.pin(FrameId::new(1));

        assert_eq!(replacer.size(), 2);
        assert_eq!(replacer.victim(), Some(FrameId::new(0)));
        assert_eq!(replacer.victim(), Some(FrameId::new(2)));
        assert_eq!(replacer.victim(), None);
    }

    #[test]
    fn test_pin_nonexistent_is_noop() {
        let mut replacer = LruReplacer::new();
        replacer.pin(FrameId::new(99));
        assert_eq!(replacer.size(), 0);
    }

    #[test]
    fn test_unpin_already_unpinned() {
        let mut replacer = LruReplacer::new();
        replacer.unpin(FrameId::new(0));
        replacer.unpin(FrameId::new(0)); // Duplicate

        assert_eq!(replacer.size(), 1);
        assert_eq!(replacer.victim(), Some(FrameId::new(0)));
        assert_eq!(replacer.victim(), None);
    }

    #[test]
    fn test_pin_unpin_cycle() {
        let mut replacer = LruReplacer::new();

        // Initial unpin
        replacer.unpin(FrameId::new(0));
        assert_eq!(replacer.size(), 1);

        // Pin it
        replacer.pin(FrameId::new(0));
        assert_eq!(replacer.size(), 0);

        // Unpin again
        replacer.unpin(FrameId::new(0));
        assert_eq!(replacer.size(), 1);

        assert_eq!(replacer.victim(), Some(FrameId::new(0)));
    }

    #[test]
    fn test_lru_order_maintained() {
        let mut replacer = LruReplacer::new();

        // Unpin in order: 0, 1, 2
        replacer.unpin(FrameId::new(0));
        replacer.unpin(FrameId::new(1));
        replacer.unpin(FrameId::new(2));

        // Pin and re-unpin frame 0
        replacer.pin(FrameId::new(0));
        replacer.unpin(FrameId::new(0));

        // Order should now be: 1, 2, 0
        assert_eq!(replacer.victim(), Some(FrameId::new(1)));
        assert_eq!(replacer.victim(), Some(FrameId::new(2)));
        assert_eq!(replacer.victim(), Some(FrameId::new(0)));
    }

    #[test]
    fn test_with_capacity() {
        let replacer = LruReplacer::with_capacity(100);
        assert_eq!(replacer.size(), 0);
    }

    #[test]
    fn test_multiple_pins() {
        let mut replacer = LruReplacer::new();

        replacer.unpin(FrameId::new(0));
        replacer.pin(FrameId::new(0));
        replacer.pin(FrameId::new(0)); // Redundant pin

        assert_eq!(replacer.size(), 0);
    }

    #[test]
    fn test_interleaved_operations() {
        let mut replacer = LruReplacer::new();

        replacer.unpin(FrameId::new(0));
        replacer.unpin(FrameId::new(1));
        assert_eq!(replacer.size(), 2);

        replacer.pin(FrameId::new(0));
        assert_eq!(replacer.size(), 1);

        replacer.unpin(FrameId::new(2));
        assert_eq!(replacer.size(), 2);

        assert_eq!(replacer.victim(), Some(FrameId::new(1)));
        assert_eq!(replacer.victim(), Some(FrameId::new(2)));
        assert_eq!(replacer.victim(), None);
    }
}
