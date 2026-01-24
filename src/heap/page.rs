//! Heap page implementation using slotted page structure.
//!
//! A heap page manages variable-length records within a fixed 8KB page.
//! The page layout consists of:
//!
//! ```text
//! +------------------+ offset 0
//! | PageHeader (24B) |
//! +------------------+ offset 24
//! | Slot Array       | (grows downward)
//! +------------------+
//! | Free Space       |
//! +------------------+
//! | Records          | (grows upward from bottom)
//! +------------------+ offset 8192
//! ```
//!
//! Records are stored from the bottom of the page upward, while the slot array
//! grows downward from the header. This allows both to grow toward each other,
//! maximizing space utilization.

use super::error::HeapError;
use crate::storage::{PAGE_HEADER_SIZE, PAGE_SIZE, PageHeader, PageId};

/// Size of each slot entry in bytes.
pub const SLOT_SIZE: usize = 4;

/// Maximum record size that can fit in a single page.
///
/// This accounts for the header and at least one slot entry.
pub const MAX_RECORD_SIZE: usize = PAGE_SIZE - PAGE_HEADER_SIZE - SLOT_SIZE;

/// Slot identifier within a page.
pub type SlotId = u16;

/// A slot entry in the slot array.
///
/// Layout (4 bytes):
/// - `offset`: u16 (2 bytes, offset to record data, 0 = deleted)
/// - `length`: u16 (2 bytes, record length)
///
/// A slot with `offset == 0` is considered deleted/empty.
#[derive(Debug, Clone, Copy)]
pub struct SlotEntry {
    /// Offset to record data from start of page (0 = deleted).
    pub offset: u16,
    /// Length of record in bytes.
    pub length: u16,
}

impl SlotEntry {
    /// Creates an empty/deleted slot entry with no link to next free slot.
    pub const fn empty() -> Self {
        Self {
            offset: 0,
            length: u16::MAX,
        }
    }

    /// Creates a free slot entry linked to the next free slot.
    ///
    /// The `length` field is reused to store the next free slot ID.
    /// Use `u16::MAX` to indicate end of free list.
    pub const fn free(next: u16) -> Self {
        Self {
            offset: 0,
            length: next,
        }
    }

    /// Creates a slot entry for a record.
    pub const fn new(offset: u16, length: u16) -> Self {
        Self { offset, length }
    }

    /// Returns true if this slot is empty (deleted).
    pub fn is_empty(&self) -> bool {
        self.offset == 0
    }

    /// Returns the next free slot ID.
    ///
    /// This is only valid for empty slots where the `length` field
    /// stores the next free slot ID. Returns `u16::MAX` if this is
    /// the end of the free list.
    pub fn next_free(&self) -> u16 {
        debug_assert!(self.is_empty());
        self.length
    }

    /// Reads a slot entry from bytes.
    pub fn read_from(data: &[u8]) -> Self {
        Self {
            offset: u16::from_le_bytes([data[0], data[1]]),
            length: u16::from_le_bytes([data[2], data[3]]),
        }
    }

    /// Writes a slot entry to bytes.
    pub fn write_to(&self, data: &mut [u8]) {
        data[0..2].copy_from_slice(&self.offset.to_le_bytes());
        data[2..4].copy_from_slice(&self.length.to_le_bytes());
    }
}

/// Global identifier for a record (page + slot).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RecordId {
    /// Page containing the record.
    pub page_id: PageId,
    /// Slot within the page.
    pub slot_id: SlotId,
}

impl RecordId {
    /// Creates a new record identifier.
    pub fn new(page_id: PageId, slot_id: SlotId) -> Self {
        Self { page_id, slot_id }
    }
}

/// A heap page for storing variable-length records.
///
/// This struct provides methods for manipulating records within a page.
/// Internally uses a slotted page layout where records grow upward from
/// the bottom and the slot array grows downward from the header.
///
/// The type parameter `T` allows this to wrap:
/// - `&[u8]` - read-only view
/// - `&mut [u8]` - mutable view
/// - `Vec<u8>` - owned data
/// - Any type implementing `AsRef<[u8]>` (and optionally `AsMut<[u8]>`)
///
/// # Example
///
/// ```no_run
/// use enhance::storage::PAGE_SIZE;
/// use enhance::heap::HeapPage;
///
/// let mut data = vec![0u8; PAGE_SIZE];
/// let mut page = HeapPage::new(&mut data);
/// page.init();
///
/// let slot_id = page.insert(b"hello world").unwrap();
/// assert_eq!(page.read(slot_id), Some(b"hello world".as_slice()));
/// ```
pub struct HeapPage<T> {
    data: T,
}

// Read-only methods (available for any T: AsRef<[u8]>)
impl<T: AsRef<[u8]>> HeapPage<T> {
    /// Creates a new HeapPage page view over the given data.
    ///
    /// # Panics
    ///
    /// Panics if `data.as_ref().len() != PAGE_SIZE`.
    pub fn new(data: T) -> Self {
        assert_eq!(
            data.as_ref().len(),
            PAGE_SIZE,
            "HeapPage requires exactly {} bytes, got {}",
            PAGE_SIZE,
            data.as_ref().len()
        );
        Self { data }
    }

    /// Returns a reference to the underlying data.
    fn data(&self) -> &[u8] {
        self.data.as_ref()
    }

    /// Returns the page header.
    pub fn header(&self) -> PageHeader {
        PageHeader::read_from(&self.data()[..PAGE_HEADER_SIZE])
    }

    /// Returns the slot entry at the given index.
    fn get_slot(&self, slot_id: SlotId) -> SlotEntry {
        let offset = PAGE_HEADER_SIZE + (slot_id as usize) * SLOT_SIZE;
        SlotEntry::read_from(&self.data()[offset..offset + SLOT_SIZE])
    }

    /// Returns the contiguous free space available for new records.
    pub fn free_space(&self) -> usize {
        self.header().free_space() as usize
    }

    /// Checks if a record of given size can be inserted.
    ///
    /// This accounts for both the record data and a potential new slot entry.
    pub fn can_insert(&self, record_size: usize) -> bool {
        let header = self.header();
        let need_new_slot = header.first_free_slot == u16::MAX;
        let slot_overhead = if need_new_slot { SLOT_SIZE } else { 0 };
        self.free_space() >= record_size + slot_overhead
    }

    /// Reads a record by slot ID.
    ///
    /// Returns `None` if the slot is out of bounds or deleted.
    pub fn read(&self, slot_id: SlotId) -> Option<&[u8]> {
        let header = self.header();
        if slot_id >= header.slot_count {
            return None;
        }

        let slot = self.get_slot(slot_id);
        if slot.is_empty() {
            return None;
        }

        let start = slot.offset as usize;
        let end = start + slot.length as usize;
        Some(&self.data()[start..end])
    }

    /// Returns the fragmentation ratio (0.0 = no fragmentation, 1.0 = all garbage).
    ///
    /// Fragmentation is the ratio of wasted space to total record area.
    pub fn fragmentation(&self) -> f32 {
        let header = self.header();
        let total_record_area = (PAGE_SIZE as u16 - header.free_end) as usize;

        if total_record_area == 0 {
            return 0.0;
        }

        let mut used_space = 0usize;
        for slot_id in 0..header.slot_count {
            let slot = self.get_slot(slot_id);
            if !slot.is_empty() {
                used_space += slot.length as usize;
            }
        }

        let wasted = total_record_area.saturating_sub(used_space);
        wasted as f32 / total_record_area as f32
    }

    /// Returns an iterator over all valid (non-deleted) records.
    pub fn iter(&self) -> impl Iterator<Item = (SlotId, &[u8])> {
        let header = self.header();
        (0..header.slot_count)
            .filter_map(move |slot_id| self.read(slot_id).map(|data| (slot_id, data)))
    }

    /// Returns the number of valid (non-deleted) records in this page.
    pub fn record_count(&self) -> usize {
        let header = self.header();
        (0..header.slot_count)
            .filter(|&slot_id| !self.get_slot(slot_id).is_empty())
            .count()
    }
}

// Mutable methods (available for T: AsRef<[u8]> + AsMut<[u8]>)
impl<T: AsRef<[u8]> + AsMut<[u8]>> HeapPage<T> {
    /// Returns a mutable reference to the underlying data.
    fn data_mut(&mut self) -> &mut [u8] {
        self.data.as_mut()
    }

    /// Initializes this page as a new empty data page.
    ///
    /// This zeroes the page and writes an empty data page header.
    pub fn init(&mut self) {
        self.data_mut().fill(0);
        PageHeader::new_heap_page().write_to(&mut self.data_mut()[..PAGE_HEADER_SIZE]);
    }

    /// Sets the page header.
    fn set_header(&mut self, header: &PageHeader) {
        header.write_to(&mut self.data_mut()[..PAGE_HEADER_SIZE]);
    }

    /// Sets the slot entry at the given index.
    fn set_slot(&mut self, slot_id: SlotId, entry: &SlotEntry) {
        let offset = PAGE_HEADER_SIZE + (slot_id as usize) * SLOT_SIZE;
        entry.write_to(&mut self.data_mut()[offset..offset + SLOT_SIZE]);
    }

    /// Inserts a record and returns its slot ID.
    ///
    /// # Errors
    ///
    /// Returns `HeapError::PageFull` if there is not enough space.
    pub fn insert(&mut self, record_data: &[u8]) -> Result<SlotId, HeapError> {
        let record_size = record_data.len();
        if !self.can_insert(record_size) {
            return Err(HeapError::PageFull {
                required: record_size + SLOT_SIZE,
                available: self.free_space(),
            });
        }

        let mut header = self.header();

        // Determine slot to use
        let slot_id = if header.first_free_slot != u16::MAX {
            // Reuse a deleted slot (O(1) via free list)
            let slot_id = header.first_free_slot;
            header.first_free_slot = self.get_slot(slot_id).next_free();
            slot_id
        } else {
            // Allocate new slot
            let slot_id = header.slot_count;
            header.slot_count += 1;
            header.free_start += SLOT_SIZE as u16;
            slot_id
        };

        // Allocate space for record (grows upward from bottom)
        header.free_end -= record_size as u16;
        let record_offset = header.free_end;

        // Write record data
        let start = record_offset as usize;
        let end = start + record_size;
        self.data_mut()[start..end].copy_from_slice(record_data);

        // Write slot entry
        self.set_slot(slot_id, &SlotEntry::new(record_offset, record_size as u16));

        // Update header
        self.set_header(&header);

        Ok(slot_id)
    }

    /// Deletes a record by slot ID.
    ///
    /// This marks the slot as deleted but does not immediately reclaim space.
    /// Use [`compact`](Self::compact) to reclaim space from deleted records.
    ///
    /// # Errors
    ///
    /// Returns `HeapError::SlotNotFound` if the slot doesn't exist or is already deleted.
    pub fn delete(&mut self, slot_id: SlotId) -> Result<(), HeapError> {
        let header = self.header();
        if slot_id >= header.slot_count {
            return Err(HeapError::SlotNotFound(slot_id));
        }

        let slot = self.get_slot(slot_id);
        if slot.is_empty() {
            return Err(HeapError::SlotNotFound(slot_id));
        }

        // Mark slot as deleted and link to current free list head (O(1))
        let mut header = self.header();
        self.set_slot(slot_id, &SlotEntry::free(header.first_free_slot));
        header.first_free_slot = slot_id;
        self.set_header(&header);

        Ok(())
    }

    /// Updates a record in place if it fits, otherwise relocates it.
    ///
    /// If the new data is smaller than or equal to the old record, it is
    /// written in place. Otherwise, the old record is deleted and a new
    /// one is inserted at the current free space location.
    ///
    /// # Errors
    ///
    /// Returns `HeapError::SlotNotFound` if the slot doesn't exist or is deleted.
    /// Returns `HeapError::PageFull` if the new record doesn't fit.
    pub fn update(&mut self, slot_id: SlotId, new_data: &[u8]) -> Result<(), HeapError> {
        let header = self.header();
        if slot_id >= header.slot_count {
            return Err(HeapError::SlotNotFound(slot_id));
        }

        let old_slot = self.get_slot(slot_id);
        if old_slot.is_empty() {
            return Err(HeapError::SlotNotFound(slot_id));
        }

        let old_len = old_slot.length as usize;
        let new_len = new_data.len();

        if new_len <= old_len {
            // Fits in place - overwrite at same location
            let start = old_slot.offset as usize;
            self.data_mut()[start..start + new_len].copy_from_slice(new_data);
            // Update slot length (may be smaller, leaving a gap until compaction)
            self.set_slot(slot_id, &SlotEntry::new(old_slot.offset, new_len as u16));
            Ok(())
        } else {
            // Doesn't fit - check if we have enough total space
            let extra_needed = new_len - old_len;
            if self.free_space() < extra_needed {
                return Err(HeapError::PageFull {
                    required: new_len,
                    available: old_len + self.free_space(),
                });
            }

            // Allocate new space and write data
            let mut header = self.header();
            header.free_end -= new_len as u16;
            let new_offset = header.free_end;

            let start = new_offset as usize;
            self.data_mut()[start..start + new_len].copy_from_slice(new_data);

            // Update slot to point to new location (old space becomes garbage until compaction)
            self.set_slot(slot_id, &SlotEntry::new(new_offset, new_len as u16));
            self.set_header(&header);

            Ok(())
        }
    }

    /// Compacts the page by removing gaps between records.
    ///
    /// This operation:
    /// 1. Collects all valid records
    /// 2. Rewrites them contiguously from the bottom
    /// 3. Updates all slot offsets
    /// 4. Rebuilds the free list
    /// 5. Resets `free_end` to the new boundary
    ///
    /// After compaction, `free_space()` returns the maximum available space.
    ///
    /// NOTE: This is O(n) in the number of records. Call only when needed,
    /// such as when an insert fails but total space should be sufficient.
    pub fn compact(&mut self) {
        let header = self.header();

        // Collect all valid records with their slot IDs
        let mut records: Vec<(SlotId, Vec<u8>)> = Vec::new();
        for slot_id in 0..header.slot_count {
            let slot = self.get_slot(slot_id);
            if !slot.is_empty() {
                let start = slot.offset as usize;
                let end = start + slot.length as usize;
                records.push((slot_id, self.data()[start..end].to_vec()));
            }
        }

        // Rewrite records from bottom of page
        let mut new_free_end = PAGE_SIZE as u16;
        for (slot_id, record_data) in &records {
            new_free_end -= record_data.len() as u16;
            let start = new_free_end as usize;
            self.data_mut()[start..start + record_data.len()].copy_from_slice(record_data);
            self.set_slot(
                *slot_id,
                &SlotEntry::new(new_free_end, record_data.len() as u16),
            );
        }

        // Rebuild free list by scanning empty slots in reverse order
        // This ensures the list is ordered from lowest to highest slot ID
        let mut first_free = u16::MAX;
        for slot_id in (0..header.slot_count).rev() {
            if self.get_slot(slot_id).is_empty() {
                self.set_slot(slot_id, &SlotEntry::free(first_free));
                first_free = slot_id;
            }
        }

        // Update header
        let mut header = self.header();
        header.free_end = new_free_end;
        header.first_free_slot = first_free;
        self.set_header(&header);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::storage::{PAGE_VERSION, PageType};

    fn create_page() -> Vec<u8> {
        let mut data = vec![0u8; PAGE_SIZE];
        HeapPage::new(&mut data).init();
        data
    }

    #[test]
    fn test_header_roundtrip() {
        let mut data = vec![0u8; PAGE_SIZE];
        let mut page = HeapPage::new(&mut data);
        page.init();

        let header = page.header();
        assert_eq!(header.page_lsn, 0);
        assert_eq!(header.checksum, 0);
        assert_eq!(header.page_type, PageType::Heap);
        assert_eq!(header.page_version, PAGE_VERSION);
        assert_eq!(header.flags, 0);
        assert_eq!(header.slot_count, 0);
        assert_eq!(header.free_start, PAGE_HEADER_SIZE as u16);
        assert_eq!(header.free_end, PAGE_SIZE as u16);
        assert_eq!(header.first_free_slot, u16::MAX);
    }

    #[test]
    fn test_insert_and_read() {
        let mut data = create_page();
        let mut page = HeapPage::new(&mut data);

        let record = b"hello world";
        let slot_id = page.insert(record).unwrap();

        assert_eq!(slot_id, 0);
        assert_eq!(page.read(slot_id), Some(record.as_slice()));
        assert_eq!(page.record_count(), 1);
    }

    #[test]
    fn test_multiple_inserts() {
        let mut data = create_page();
        let mut page = HeapPage::new(&mut data);

        let records: Vec<&[u8]> = vec![b"first", b"second", b"third"];
        let slot_ids: Vec<_> = records.iter().map(|r| page.insert(*r).unwrap()).collect();

        assert_eq!(slot_ids, vec![0, 1, 2]);
        for (slot_id, expected) in slot_ids.iter().zip(records.iter()) {
            assert_eq!(page.read(*slot_id), Some(*expected));
        }
        assert_eq!(page.record_count(), 3);
    }

    #[test]
    fn test_read_invalid_slot() {
        let mut data = create_page();
        let page = HeapPage::new(&mut data);

        assert!(page.read(0).is_none());
        assert!(page.read(100).is_none());
    }

    #[test]
    fn test_delete() {
        let mut data = create_page();
        let mut page = HeapPage::new(&mut data);

        let slot0 = page.insert(b"record0").unwrap();
        let slot1 = page.insert(b"record1").unwrap();

        page.delete(slot0).unwrap();

        assert!(page.read(slot0).is_none());
        assert_eq!(page.read(slot1), Some(b"record1".as_slice()));
        assert_eq!(page.record_count(), 1);
    }

    #[test]
    fn test_delete_invalid_slot() {
        let mut data = create_page();
        let mut page = HeapPage::new(&mut data);

        assert!(matches!(page.delete(0), Err(HeapError::SlotNotFound(0))));

        let slot = page.insert(b"test").unwrap();
        page.delete(slot).unwrap();

        // Deleting already deleted slot should fail
        assert!(matches!(page.delete(slot), Err(HeapError::SlotNotFound(_))));
    }

    #[test]
    fn test_slot_reuse() {
        let mut data = create_page();
        let mut page = HeapPage::new(&mut data);

        let slot0 = page.insert(b"record0").unwrap();
        let _slot1 = page.insert(b"record1").unwrap();

        page.delete(slot0).unwrap();

        // New insert should reuse slot0
        let slot2 = page.insert(b"record2").unwrap();
        assert_eq!(slot2, slot0);
        assert_eq!(page.read(slot2), Some(b"record2".as_slice()));
    }

    #[test]
    fn test_update_smaller() {
        let mut data = create_page();
        let mut page = HeapPage::new(&mut data);

        let slot = page.insert(b"hello world").unwrap();
        page.update(slot, b"hi").unwrap();

        assert_eq!(page.read(slot), Some(b"hi".as_slice()));
    }

    #[test]
    fn test_update_larger() {
        let mut data = create_page();
        let mut page = HeapPage::new(&mut data);

        let slot = page.insert(b"hi").unwrap();
        page.update(slot, b"hello world").unwrap();

        assert_eq!(page.read(slot), Some(b"hello world".as_slice()));
    }

    #[test]
    fn test_update_invalid_slot() {
        let mut data = create_page();
        let mut page = HeapPage::new(&mut data);

        assert!(matches!(
            page.update(0, b"test"),
            Err(HeapError::SlotNotFound(0))
        ));
    }

    #[test]
    fn test_page_full() {
        let mut data = create_page();
        let mut page = HeapPage::new(&mut data);

        // Insert large records until full
        let large_record = vec![0u8; 1000];
        let mut count = 0;
        while page.insert(&large_record).is_ok() {
            count += 1;
        }

        // Should have inserted several but eventually fail
        assert!(count > 0);
        assert!(matches!(
            page.insert(&large_record),
            Err(HeapError::PageFull { .. })
        ));
    }

    #[test]
    fn test_compact() {
        let mut data = create_page();
        let mut page = HeapPage::new(&mut data);

        // Insert records
        let slot0 = page.insert(b"aaaa").unwrap();
        let slot1 = page.insert(b"bbbb").unwrap();
        let slot2 = page.insert(b"cccc").unwrap();

        // Delete middle record
        page.delete(slot1).unwrap();

        // Should have fragmentation
        assert!(page.fragmentation() > 0.0);

        // Compact
        page.compact();

        // Fragmentation should be gone
        assert!(page.fragmentation() < 0.01);

        // Records should still be readable
        assert_eq!(page.read(slot0), Some(b"aaaa".as_slice()));
        assert!(page.read(slot1).is_none()); // Still deleted
        assert_eq!(page.read(slot2), Some(b"cccc".as_slice()));
    }

    #[test]
    fn test_compact_recovers_space() {
        let mut data = create_page();
        let mut page = HeapPage::new(&mut data);

        let large_record = vec![0u8; 2000];
        let slot0 = page.insert(&large_record).unwrap();
        let slot1 = page.insert(&large_record).unwrap();
        let slot2 = page.insert(&large_record).unwrap();

        let free_before = page.free_space();

        // Delete middle record
        page.delete(slot1).unwrap();

        // Free space shouldn't increase yet (fragmented)
        assert_eq!(page.free_space(), free_before);

        // Compact
        page.compact();

        // Now free space should increase
        assert!(page.free_space() > free_before);

        // And we should be able to insert more
        let slot3 = page.insert(&large_record).unwrap();
        assert_eq!(slot3, slot1); // Reused deleted slot

        // Verify all records
        assert!(page.read(slot0).is_some());
        assert!(page.read(slot2).is_some());
        assert!(page.read(slot3).is_some());
    }

    #[test]
    fn test_iter() {
        let mut data = create_page();
        let mut page = HeapPage::new(&mut data);

        page.insert(b"first").unwrap();
        let slot1 = page.insert(b"second").unwrap();
        page.insert(b"third").unwrap();

        page.delete(slot1).unwrap();

        let records: Vec<_> = page.iter().collect();
        assert_eq!(records.len(), 2);
        assert_eq!(records[0], (0, b"first".as_slice()));
        assert_eq!(records[1], (2, b"third".as_slice()));
    }

    #[test]
    fn test_heap_page_read_only() {
        let mut data = create_page();
        {
            let mut page = HeapPage::new(&mut data);
            page.insert(b"hello").unwrap();
            page.insert(b"world").unwrap();
        }

        // Now use read-only view (with immutable reference)
        let page_ref = HeapPage::new(&data[..]);
        assert_eq!(page_ref.read(0), Some(b"hello".as_slice()));
        assert_eq!(page_ref.read(1), Some(b"world".as_slice()));
        assert_eq!(page_ref.record_count(), 2);

        let records: Vec<_> = page_ref.iter().collect();
        assert_eq!(records.len(), 2);
    }

    #[test]
    fn test_max_record_size() {
        let mut data = create_page();
        let mut page = HeapPage::new(&mut data);

        // Should be able to insert a max-sized record
        let max_record = vec![0u8; MAX_RECORD_SIZE];
        let slot = page.insert(&max_record).unwrap();
        assert_eq!(page.read(slot).map(|r| r.len()), Some(MAX_RECORD_SIZE));

        // But not another one
        assert!(matches!(
            page.insert(&[0u8; 1]),
            Err(HeapError::PageFull { .. })
        ));
    }

    #[test]
    fn test_free_space_calculation() {
        let mut data = create_page();
        let mut page = HeapPage::new(&mut data);

        let initial_free = page.free_space();
        assert_eq!(initial_free, PAGE_SIZE - PAGE_HEADER_SIZE);

        // Insert a record
        let record = b"test data";
        page.insert(record).unwrap();

        // Free space should decrease by record size + slot size
        let expected_free = initial_free - record.len() - SLOT_SIZE;
        assert_eq!(page.free_space(), expected_free);
    }

    #[test]
    fn test_empty_record() {
        let mut data = create_page();
        let mut page = HeapPage::new(&mut data);

        let slot = page.insert(b"").unwrap();
        assert_eq!(page.read(slot), Some(b"".as_slice()));
    }
}
