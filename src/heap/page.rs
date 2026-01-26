//! Heap page implementation using slotted page structure.
//!
//! A heap page manages variable-length records within a fixed 8KB page.
//! The page layout consists of:
//!
//! ```text
//! +------------------+ offset 0
//! | PageHeader (24B) |
//! +------------------+ offset 24
//! | Slot Array       | (grows down)
//! | [0][1][2]...     |
//! +------------------+ offset header.free_start(SLOT_SIZE)
//! |                  |
//! | Free Space       |
//! |                  |
//! +------------------+ offset header.free_end
//! | Records          |
//! |     ...[2][1][0] | (grows up)
//! +------------------+ offset 8192
//! ```
//!
//! Records are stored from the bottom of the page upward, while the slot array
//! grows downward from the header. This allows both to grow toward each other,
//! maximizing space utilization.

use super::error::HeapError;
use super::record::Record;
use crate::storage::{PAGE_HEADER_SIZE, PAGE_SIZE, PageHeader};
use crate::tx::{CommandId, TupleHeader, TxId, TUPLE_HEADER_SIZE};

// Should be able to insert a max-sized record
pub const MAX_RECORD_SIZE: usize = PAGE_SIZE - PAGE_HEADER_SIZE - SLOT_SIZE;

/// Maximum size for tuple payload (record + tuple header).
///
/// Account for tuple header in max payload size.
pub const MAX_TUPLE_PAYLOAD_SIZE: usize = MAX_RECORD_SIZE - TUPLE_HEADER_SIZE;

/// Size of each slot entry in bytes.
pub const SLOT_SIZE: usize = 4;

/// Slot identifier within a page (0-based index into the slot array).
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
    /// Offset to record data from start of page (0 = deleted/free).
    pub offset: u16,
    /// Length of record in bytes, or next free slot ID when deleted.
    ///
    /// When `offset == 0` (slot is free), this field stores the next free slot ID
    /// in the free list, with `u16::MAX` indicating end of list.
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
    pub const fn free(next: SlotId) -> Self {
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
    pub fn next_free(&self) -> SlotId {
        debug_assert!(self.is_empty());
        self.length
    }

    /// Reads a slot entry from bytes.
    pub fn read(data: &[u8]) -> Self {
        Self {
            offset: u16::from_le_bytes([data[0], data[1]]),
            length: u16::from_le_bytes([data[2], data[3]]),
        }
    }

    /// Writes a slot entry to bytes.
    pub fn write(&self, data: &mut [u8]) {
        data[0..2].copy_from_slice(&self.offset.to_le_bytes());
        data[2..4].copy_from_slice(&self.length.to_le_bytes());
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
/// assert_eq!(page.record(slot_id), Some(b"hello world".as_slice()));
/// ```
pub struct HeapPage<T> {
    data: T,
}

impl<T> HeapPage<T> {
    /// Consumes the page and returns the underlying data.
    pub fn into_inner(self) -> T {
        self.data
    }
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
        PageHeader::read(&self.data()[..PAGE_HEADER_SIZE])
    }

    /// Returns the slot entry at the given index.
    ///
    /// # Panics
    ///
    /// Panics if `slot_id >= slot_count`.
    fn slot(&self, slot_id: SlotId) -> SlotEntry {
        debug_assert!(
            slot_id < self.header().slot_count,
            "slot_id {} out of bounds (slot_count: {})",
            slot_id,
            self.header().slot_count
        );
        let offset = PAGE_HEADER_SIZE + (slot_id as usize) * SLOT_SIZE;
        SlotEntry::read(&self.data()[offset..offset + SLOT_SIZE])
    }

    /// Reads a record by slot ID.
    ///
    /// Returns `None` if the slot is out of bounds or deleted.
    pub fn record(&self, slot_id: SlotId) -> Option<&[u8]> {
        let header = self.header();
        if slot_id >= header.slot_count {
            return None;
        }

        let slot = self.slot(slot_id);
        if slot.is_empty() {
            return None;
        }

        let start = slot.offset as usize;
        let end = start + slot.length as usize;
        Some(&self.data()[start..end])
    }

    /// Returns an iterator over all valid (non-deleted) records.
    pub fn records(&self) -> impl Iterator<Item = (SlotId, &[u8])> {
        let header = self.header();
        (0..header.slot_count).filter_map(move |slot_id| Some((slot_id, self.record(slot_id)?)))
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
            let slot = self.slot(slot_id);
            if !slot.is_empty() {
                used_space += slot.length as usize;
            }
        }

        let wasted = total_record_area.saturating_sub(used_space);
        wasted as f32 / total_record_area as f32
    }
}

// Mutable methods (available for T: AsRef<[u8]> + AsMut<[u8]>)
impl<T: AsRef<[u8]> + AsMut<[u8]>> HeapPage<T> {
    /// Checks if there is enough contiguous free space for the given size.
    ///
    /// Returns `HeapError::PageFull` if the space is insufficient.
    fn ensure_free_space(&self, header: &PageHeader, required: usize) -> Result<(), HeapError> {
        let available = header.free_space(SLOT_SIZE) as usize;
        if available < required {
            Err(HeapError::PageFull {
                required,
                available,
            })
        } else {
            Ok(())
        }
    }

    /// Initializes this page as a new empty heap page.
    ///
    /// This zeroes the page and writes an empty heap page header.
    pub fn init(&mut self) {
        self.data_mut().fill(0);
        PageHeader::new_heap_page().write(&mut self.data_mut()[..PAGE_HEADER_SIZE]);
    }

    /// Returns a mutable reference to the underlying data.
    fn data_mut(&mut self) -> &mut [u8] {
        self.data.as_mut()
    }

    /// Sets the page header.
    fn set_header(&mut self, header: &PageHeader) {
        header.write(&mut self.data_mut()[..PAGE_HEADER_SIZE]);
    }

    /// Sets the slot entry at the given index.
    fn set_slot(&mut self, slot_id: SlotId, entry: SlotEntry) {
        let offset = PAGE_HEADER_SIZE + (slot_id as usize) * SLOT_SIZE;
        entry.write(&mut self.data_mut()[offset..offset + SLOT_SIZE]);
    }

    /// Inserts a record and returns its slot ID.
    ///
    /// # Errors
    ///
    /// Returns `HeapError::PageFull` if there is not enough space.
    pub fn insert(&mut self, record: &[u8]) -> Result<SlotId, HeapError> {
        let mut header = self.header();

        let need_new_slot = header.first_free_slot == u16::MAX;
        let slot_overhead = if need_new_slot { SLOT_SIZE } else { 0 };
        self.ensure_free_space(&header, record.len() + slot_overhead)?;

        // Determine slot to use
        let slot_id = if need_new_slot {
            // Allocate new slot
            let slot_id = header.slot_count;
            header.slot_count += 1;
            slot_id
        } else {
            // Reuse a deleted slot (O(1) via free list)
            let slot_id = header.first_free_slot;
            header.first_free_slot = self.slot(slot_id).next_free();
            slot_id
        };

        // Allocate new space and write data
        header.free_end -= record.len() as u16;
        let start = header.free_end as usize;
        self.data_mut()[start..start + record.len()].copy_from_slice(record);
        self.set_slot(slot_id, SlotEntry::new(start as u16, record.len() as u16));
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
        let mut header = self.header();
        if slot_id >= header.slot_count {
            return Err(HeapError::SlotNotFound(slot_id));
        }

        let slot = self.slot(slot_id);
        if slot.is_empty() {
            return Err(HeapError::SlotNotFound(slot_id));
        }

        // Mark slot as deleted and link to current free list head (O(1))
        self.set_slot(slot_id, SlotEntry::free(header.first_free_slot));
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
    pub fn update(&mut self, slot_id: SlotId, record: &[u8]) -> Result<(), HeapError> {
        let mut header = self.header();
        if slot_id >= header.slot_count {
            return Err(HeapError::SlotNotFound(slot_id));
        }

        let slot = self.slot(slot_id);
        if slot.is_empty() {
            return Err(HeapError::SlotNotFound(slot_id));
        }

        if record.len() <= slot.length as usize {
            // Fits in place - overwrite at same location
            let start = slot.offset as usize;
            self.data_mut()[start..start + record.len()].copy_from_slice(record);
            self.set_slot(slot_id, SlotEntry::new(start as u16, record.len() as u16));
        } else {
            // Doesn't fit - check if we have enough contiguous free space
            self.ensure_free_space(&header, record.len())?;

            // Allocate new space and write data
            header.free_end -= record.len() as u16;
            let start = header.free_end as usize;
            self.data_mut()[start..start + record.len()].copy_from_slice(record);
            self.set_slot(slot_id, SlotEntry::new(start as u16, record.len() as u16));
            self.set_header(&header);
        }
        Ok(())
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
    /// After compaction, `header().free_space()` returns the maximum available space.
    ///
    /// NOTE: This is O(n) in the number of records. Call only when needed,
    /// such as when an insert fails but total space should be sufficient.
    pub fn compact(&mut self) {
        let mut header = self.header();

        // Collect all valid records with their slot IDs
        let mut records: Vec<(SlotId, Vec<u8>)> = Vec::new();
        for slot_id in 0..header.slot_count {
            let slot = self.slot(slot_id);
            if !slot.is_empty() {
                let start = slot.offset as usize;
                let data = self.data()[start..start + slot.length as usize].to_vec();
                records.push((slot_id, data));
            }
        }

        // Rewrite records from bottom of page
        header.free_end = PAGE_SIZE as u16;
        for (slot_id, record) in &records {
            header.free_end -= record.len() as u16;
            let start = header.free_end as usize;
            self.data_mut()[start..start + record.len()].copy_from_slice(record);
            self.set_slot(*slot_id, SlotEntry::new(start as u16, record.len() as u16));
        }
        self.set_header(&header);
    }

    // ========================================================================
    // MVCC-Aware Methods
    // ========================================================================

    /// Inserts a record with MVCC tuple header.
    ///
    /// This serializes the tuple header and record together into a single
    /// slot, making MVCC versioning transparent at the page level.
    ///
    /// # Errors
    ///
    /// Returns `HeapError::PageFull` if there is not enough space.
    pub fn insert_tuple(
        &mut self,
        record: &Record,
        xmin: TxId,
        cid: CommandId,
    ) -> Result<SlotId, HeapError> {
        // Serialize tuple header + record
        let header = TupleHeader::new_insert(xmin, cid);
        let record_size = record.serialized_size();
        let total_size = TUPLE_HEADER_SIZE + record_size;

        let mut buf = vec![0u8; total_size];
        header
            .serialize(&mut buf[..TUPLE_HEADER_SIZE])
            .map_err(|e| HeapError::Serialization(e.to_string()))?;
        record
            .serialize(&mut buf[TUPLE_HEADER_SIZE..])
            .map_err(|e| HeapError::Serialization(e.to_string()))?;

        // Insert as a single record
        self.insert(&buf)
    }

    /// Updates just the tuple header in an existing slot.
    ///
    /// This is used to modify transaction visibility information (e.g., setting
    /// xmax for DELETE) without changing the record data.
    ///
    /// # Errors
    ///
    /// Returns `HeapError::SlotNotFound` if the slot doesn't exist or is deleted.
    pub fn update_tuple_header(
        &mut self,
        slot_id: SlotId,
        header: TupleHeader,
    ) -> Result<(), HeapError> {
        let page_header = self.header();
        if slot_id >= page_header.slot_count {
            return Err(HeapError::SlotNotFound(slot_id));
        }

        let slot = self.slot(slot_id);
        if slot.is_empty() {
            return Err(HeapError::SlotNotFound(slot_id));
        }

        // Serialize new header and overwrite first TUPLE_HEADER_SIZE bytes
        let mut header_buf = [0u8; TUPLE_HEADER_SIZE];
        header
            .serialize(&mut header_buf)
            .map_err(|e| HeapError::Serialization(e.to_string()))?;

        let start = slot.offset as usize;
        self.data_mut()[start..start + TUPLE_HEADER_SIZE].copy_from_slice(&header_buf);

        Ok(())
    }
}

// Read-only MVCC methods (available for any T: AsRef<[u8]>)
impl<T: AsRef<[u8]>> HeapPage<T> {
    /// Reads a tuple (header + record) by slot ID.
    ///
    /// Returns `None` if the slot is out of bounds or deleted.
    pub fn get_tuple(&self, slot_id: SlotId, schema: &[i32]) -> Option<(TupleHeader, Record)> {
        let raw = self.record(slot_id)?;
        if raw.len() < TUPLE_HEADER_SIZE {
            return None;
        }

        let header = TupleHeader::deserialize(&raw[..TUPLE_HEADER_SIZE]).ok()?;
        let record = Record::deserialize(&raw[TUPLE_HEADER_SIZE..], schema).ok()?;

        Some((header, record))
    }

    /// Returns an iterator over all tuples with headers.
    ///
    /// Yields `(SlotId, TupleHeader, Record)` for each valid (non-deleted) slot.
    pub fn tuples<'a>(
        &'a self,
        schema: &'a [i32],
    ) -> impl Iterator<Item = (SlotId, TupleHeader, Record)> + 'a {
        let header = self.header();
        (0..header.slot_count).filter_map(move |slot_id| {
            let (tuple_header, record) = self.get_tuple(slot_id, schema)?;
            Some((slot_id, tuple_header, record))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::storage::{PAGE_VERSION, PageType};

    fn create_page() -> HeapPage<Vec<u8>> {
        let mut page = HeapPage::new(vec![0u8; PAGE_SIZE]);
        page.init();
        page
    }

    #[test]
    fn test_header_roundtrip() {
        let page = create_page();
        let header = page.header();
        assert_eq!(header.page_lsn, 0);
        assert_eq!(header.checksum, 0);
        assert_eq!(header.page_type, PageType::Heap);
        assert_eq!(header.page_version, PAGE_VERSION);
        assert_eq!(header.flags, 0);
        assert_eq!(header.slot_count, 0);
        assert_eq!(header.free_start(SLOT_SIZE), PAGE_HEADER_SIZE as u16);
        assert_eq!(header.free_end, PAGE_SIZE as u16);
        assert_eq!(header.first_free_slot, u16::MAX);
    }

    #[test]
    fn test_insert_and_read() {
        let mut page = create_page();

        let record = b"hello world";
        let slot_id = page.insert(record).unwrap();

        assert_eq!(slot_id, 0);
        assert_eq!(page.record(slot_id), Some(record.as_slice()));
        assert_eq!(page.records().count(), 1);
    }

    #[test]
    fn test_multiple_inserts() {
        let mut page = create_page();

        let records: Vec<&[u8]> = vec![b"first", b"second", b"third"];
        let slot_ids: Vec<_> = records.iter().map(|r| page.insert(*r).unwrap()).collect();

        assert_eq!(slot_ids, vec![0, 1, 2]);
        for (slot_id, expected) in slot_ids.iter().zip(records.iter()) {
            assert_eq!(page.record(*slot_id), Some(*expected));
        }
        assert_eq!(page.records().count(), 3);
    }

    #[test]
    fn test_read_invalid_slot() {
        let page = create_page();

        assert!(page.record(0).is_none());
        assert!(page.record(100).is_none());
    }

    #[test]
    fn test_delete() {
        let mut page = create_page();

        let slot0 = page.insert(b"record0").unwrap();
        let slot1 = page.insert(b"record1").unwrap();

        page.delete(slot0).unwrap();

        assert!(page.record(slot0).is_none());
        assert_eq!(page.record(slot1), Some(b"record1".as_slice()));
        assert_eq!(page.records().count(), 1);

        // New insert should reuse the deleted slot
        let slot2 = page.insert(b"record2").unwrap();
        assert_eq!(slot2, slot0);
        assert_eq!(page.record(slot2), Some(b"record2".as_slice()));
    }

    #[test]
    fn test_delete_free_list() {
        let mut page = create_page();

        let slot0 = page.insert(b"a").unwrap();
        let slot1 = page.insert(b"b").unwrap();
        let slot2 = page.insert(b"c").unwrap();

        // Delete in order: slot0, slot2 (free list: slot2 -> slot0)
        page.delete(slot0).unwrap();
        page.delete(slot2).unwrap();

        // Inserts should reuse in LIFO order
        assert_eq!(page.insert(b"x").unwrap(), slot2);
        assert_eq!(page.insert(b"y").unwrap(), slot0);
        // Now free list is empty, should allocate new slot
        assert_eq!(page.insert(b"z").unwrap(), 3);

        // Untouched slot remains intact
        assert_eq!(page.record(slot1), Some(b"b".as_slice()));
    }

    #[test]
    fn test_delete_invalid_slot() {
        let mut page = create_page();

        assert!(matches!(page.delete(0), Err(HeapError::SlotNotFound(0))));

        let slot = page.insert(b"test").unwrap();
        page.delete(slot).unwrap();

        // Deleting already deleted slot should fail
        assert!(matches!(page.delete(slot), Err(HeapError::SlotNotFound(_))));
    }

    #[test]
    fn test_update_smaller() {
        let mut page = create_page();

        let slot = page.insert(b"hello world").unwrap();
        page.update(slot, b"hi").unwrap();

        assert_eq!(page.record(slot), Some(b"hi".as_slice()));
    }

    #[test]
    fn test_update_larger() {
        let mut page = create_page();

        let slot = page.insert(b"hi").unwrap();
        page.update(slot, b"hello world").unwrap();

        assert_eq!(page.record(slot), Some(b"hello world".as_slice()));
    }

    #[test]
    fn test_update_invalid_slot() {
        let mut page = create_page();

        assert!(matches!(
            page.update(0, b"test"),
            Err(HeapError::SlotNotFound(0))
        ));
    }

    #[test]
    fn test_page_full() {
        let mut page = create_page();

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
        let mut page = create_page();

        let large_record = vec![0u8; 2000];
        let slot0 = page.insert(&large_record).unwrap();
        let slot1 = page.insert(&large_record).unwrap();
        let slot2 = page.insert(&large_record).unwrap();

        let free_before = page.header().free_space(SLOT_SIZE);

        // Delete middle record
        page.delete(slot1).unwrap();

        // Should have fragmentation, but free space unchanged
        assert!(page.fragmentation() > 0.0);
        assert_eq!(page.header().free_space(SLOT_SIZE), free_before);

        // Compact
        page.compact();

        // Fragmentation gone, free space recovered
        assert!(page.fragmentation() <= 0.0);
        assert!(page.header().free_space(SLOT_SIZE) > free_before);

        // Records still readable
        assert!(page.record(slot0).is_some());
        assert!(page.record(slot1).is_none()); // Still deleted
        assert!(page.record(slot2).is_some());

        // Can insert using recovered space (reuses deleted slot)
        let slot3 = page.insert(&large_record).unwrap();
        assert_eq!(slot3, slot1);
    }

    #[test]
    fn test_records() {
        let mut page = create_page();

        page.insert(b"first").unwrap();
        let slot1 = page.insert(b"second").unwrap();
        page.insert(b"third").unwrap();

        page.delete(slot1).unwrap();

        let records: Vec<_> = page.records().collect();
        assert_eq!(records.len(), 2);
        assert_eq!(records[0], (0, b"first".as_slice()));
        assert_eq!(records[1], (2, b"third".as_slice()));
    }

    #[test]
    fn test_max_record_size() {
        let mut page = create_page();

        let max_record = vec![0u8; MAX_RECORD_SIZE];
        let slot = page.insert(&max_record).unwrap();
        assert_eq!(page.record(slot).map(|r| r.len()), Some(MAX_RECORD_SIZE));

        // But not another one
        assert!(matches!(
            page.insert(&[0u8; 1]),
            Err(HeapError::PageFull { .. })
        ));
    }

    #[test]
    fn test_free_space_calculation() {
        let mut page = create_page();

        let initial_free = page.header().free_space(SLOT_SIZE) as usize;
        assert_eq!(initial_free, PAGE_SIZE - PAGE_HEADER_SIZE);

        // Insert a record
        let record = b"test data";
        page.insert(record).unwrap();

        // Free space should decrease by record size + slot size
        let expected_free = initial_free - record.len() - SLOT_SIZE;
        assert_eq!(page.header().free_space(SLOT_SIZE) as usize, expected_free);
    }

    #[test]
    fn test_empty_record() {
        let mut page = create_page();

        let slot = page.insert(b"").unwrap();
        assert_eq!(page.record(slot), Some(b"".as_slice()));
    }

    // ========================================================================
    // MVCC Tests
    // ========================================================================

    #[test]
    fn test_insert_tuple() {
        use crate::heap::{Record, Value};
        use crate::protocol::type_oid;
        use crate::tx::{CommandId, TxId};

        let mut page = create_page();
        let record = Record::new(vec![Value::Int32(42), Value::Text("hello".to_string())]);

        let slot = page
            .insert_tuple(&record, TxId::new(1), CommandId::FIRST)
            .unwrap();
        assert_eq!(slot, 0);

        // Verify we can read it back
        let schema = [type_oid::INT4, type_oid::TEXT];
        let (header, read_record) = page.get_tuple(slot, &schema).unwrap();

        assert_eq!(header.xmin, TxId::new(1));
        assert_eq!(header.xmax, TxId::INVALID);
        assert_eq!(header.cid, CommandId::FIRST);
        assert_eq!(read_record, record);
    }

    #[test]
    fn test_get_tuple_none_for_deleted_slot() {
        use crate::protocol::type_oid;

        let page = create_page();
        let schema = [type_oid::INT4];

        // Slot doesn't exist
        assert!(page.get_tuple(0, &schema).is_none());
    }

    #[test]
    fn test_update_tuple_header() {
        use crate::heap::{Record, Value};
        use crate::protocol::type_oid;
        use crate::tx::{CommandId, Infomask, TupleHeader, TxId};

        let mut page = create_page();
        let record = Record::new(vec![Value::Int32(100)]);

        let slot = page
            .insert_tuple(&record, TxId::new(1), CommandId::FIRST)
            .unwrap();

        // Update the tuple header (e.g., marking as deleted)
        let new_header = TupleHeader {
            xmin: TxId::new(1),
            xmax: TxId::new(2), // Mark as deleted by transaction 2
            cid: CommandId::FIRST,
            infomask: Infomask::empty().with_xmin_committed(),
        };
        page.update_tuple_header(slot, new_header).unwrap();

        // Read back and verify
        let schema = [type_oid::INT4];
        let (header, read_record) = page.get_tuple(slot, &schema).unwrap();

        assert_eq!(header.xmin, TxId::new(1));
        assert_eq!(header.xmax, TxId::new(2));
        assert!(header.infomask.xmin_committed());
        assert_eq!(read_record, record);
    }

    #[test]
    fn test_tuples_iterator() {
        use crate::heap::{Record, Value};
        use crate::protocol::type_oid;
        use crate::tx::{CommandId, TxId};

        let mut page = create_page();

        // Insert multiple tuples
        let record1 = Record::new(vec![Value::Int32(1)]);
        let record2 = Record::new(vec![Value::Int32(2)]);
        let record3 = Record::new(vec![Value::Int32(3)]);

        page.insert_tuple(&record1, TxId::new(1), CommandId::FIRST)
            .unwrap();
        page.insert_tuple(&record2, TxId::new(2), CommandId::FIRST)
            .unwrap();
        page.insert_tuple(&record3, TxId::new(3), CommandId::FIRST)
            .unwrap();

        // Iterate and collect
        let schema = [type_oid::INT4];
        let tuples: Vec<_> = page.tuples(&schema).collect();

        assert_eq!(tuples.len(), 3);
        assert_eq!(tuples[0].0, 0); // slot_id
        assert_eq!(tuples[0].1.xmin, TxId::new(1)); // header
        assert_eq!(tuples[0].2, record1); // record

        assert_eq!(tuples[1].0, 1);
        assert_eq!(tuples[1].1.xmin, TxId::new(2));
        assert_eq!(tuples[1].2, record2);

        assert_eq!(tuples[2].0, 2);
        assert_eq!(tuples[2].1.xmin, TxId::new(3));
        assert_eq!(tuples[2].2, record3);
    }

    #[test]
    fn test_insert_tuple_with_null_values() {
        use crate::heap::{Record, Value};
        use crate::protocol::type_oid;
        use crate::tx::{CommandId, TxId};

        let mut page = create_page();
        let record = Record::new(vec![
            Value::Int32(42),
            Value::Null,
            Value::Text("test".to_string()),
        ]);

        let slot = page
            .insert_tuple(&record, TxId::new(1), CommandId::FIRST)
            .unwrap();

        // Read back
        let schema = [type_oid::INT4, type_oid::INT4, type_oid::TEXT];
        let (_, read_record) = page.get_tuple(slot, &schema).unwrap();
        assert_eq!(read_record, record);
    }

    #[test]
    fn test_update_tuple_header_invalid_slot() {
        use crate::tx::{CommandId, TupleHeader, TxId};

        let mut page = create_page();
        let header = TupleHeader::new_insert(TxId::new(1), CommandId::FIRST);

        assert!(matches!(
            page.update_tuple_header(0, header),
            Err(HeapError::SlotNotFound(0))
        ));
    }
}
