//! Heap page implementation using slotted page structure.
//!
//! A heap page manages variable-length tuples within a fixed 8KB page.
//! The page layout consists of:
//!
//! ```text
//! +------------------+ offset 0
//! | PageHeader (24B) |
//! +------------------+ offset PAGE_HEADER_SIZE (24)
//! | Slot Array       | (grows down)
//! | [0][1][2]...     |
//! +------------------+ offset PAGE_HEADER_SIZE + slot_count * SLOT_SIZE
//! |                  |
//! | Free Space       |
//! |                  |
//! +------------------+ offset header.free_end
//! | Tuples/Data      |
//! |     ...[2][1][0] | (grows up)
//! +------------------+ offset PAGE_SIZE - HEAP_FOOTER_SIZE (8188)
//! | HeapFooter  (4B) | next_page: u32
//! +------------------+ offset PAGE_SIZE (8192)
//! ```
//!
//! The `HeapFooter` region is placed at the end of the page so that the slot array
//! starts immediately after `PageHeader`, keeping `PageHeader::free_start` and
//! `PageHeader::free_space` correct without adjustment. `HeapFooter` stores
//! heap-specific metadata (page chain linkage) separately from `PageHeader`,
//! keeping `PageHeader` generic for all page types.
//!
//! Tuple data is stored from the bottom of the page upward (below `HeapFooter`),
//! while the slot array grows downward from the header. This allows both to grow
//! toward each other, maximizing space utilization.

use super::error::HeapError;
use super::record::Record;
use crate::datum::Type;
use crate::storage::{PAGE_HEADER_SIZE, PAGE_SIZE, PageHeader, PageId};
use crate::tx::{CommandId, TUPLE_HEADER_SIZE, TupleHeader, TxId};

/// Size of the heap-specific extra trailer in bytes.
///
/// This region at the tail of the page (bytes 8188..8192) stores heap page chain
/// linkage (`next_page: u32`), keeping `PageHeader` generic for all page types.
const HEAP_FOOTER_SIZE: usize = 4;

// Maximum size for slot data (raw bytes stored in a slot)
const MAX_SLOT_DATA_SIZE: usize = PAGE_SIZE - (PAGE_HEADER_SIZE + HEAP_FOOTER_SIZE + SLOT_SIZE);

/// Maximum size for record (data values only, without tuple header).
///
/// This is the actual space available for user data after accounting for the
/// tuple header and the heap-specific extra footer.
pub const MAX_RECORD_SIZE: usize = MAX_SLOT_DATA_SIZE - TUPLE_HEADER_SIZE;

/// Size of each slot entry in bytes.
const SLOT_SIZE: usize = 4;

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

    /// Creates a free slot entry linked to the next free slot.
    ///
    /// Used internally by SlottedPage for managing the free list.
    #[allow(dead_code)] // Used by VACUUM (not yet implemented)
    pub const fn free(next: SlotId) -> Self {
        Self {
            offset: 0,
            length: next,
        }
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

/// Low-level slotted page structure for managing variable-length records.
///
/// This struct provides the raw slot-based storage mechanism without MVCC awareness.
/// It handles the physical layout of records within a page, managing the slot array
/// and free space.
///
/// The slot array starts immediately after `PageHeader`. The `footer_size` field
/// specifies the size of the footer reserved at the tail of the page, allowing
/// different page types to reserve type-specific regions (e.g., `HeapFooter`).
/// The usable data area ends at `PAGE_SIZE - footer_size`.
///
/// This is an internal implementation detail. Use [`HeapPage`] for MVCC-aware operations.
struct SlottedPage<T> {
    data: T,
    /// Number of bytes reserved at the tail of the page for a type-specific footer.
    footer_size: usize,
}

impl<T> SlottedPage<T> {
    /// Consumes the page and returns the underlying data.
    fn into_inner(self) -> T {
        self.data
    }
}

// Read-only methods (available for any T: AsRef<[u8]>)
impl<T: AsRef<[u8]>> SlottedPage<T> {
    /// Creates a new slotted page view over the given data.
    ///
    /// `footer_size` is the number of bytes reserved at the tail of the page
    /// for a page-type-specific footer (e.g., `HeapFooter`). The usable data
    /// area ends at `PAGE_SIZE - footer_size`.
    ///
    /// # Panics
    ///
    /// Panics if `data.as_ref().len() != PAGE_SIZE`.
    fn new(data: T, footer_size: usize) -> Self {
        assert_eq!(
            data.as_ref().len(),
            PAGE_SIZE,
            "SlottedPage requires exactly {} bytes, got {}",
            PAGE_SIZE,
            data.as_ref().len()
        );
        Self { data, footer_size }
    }

    /// Returns a reference to the underlying data.
    fn data(&self) -> &[u8] {
        self.data.as_ref()
    }

    /// Returns the page header.
    fn header(&self) -> PageHeader {
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

    /// Reads slot data (raw bytes) by slot ID.
    ///
    /// Returns `None` if the slot is out of bounds or deleted.
    fn get(&self, slot_id: SlotId) -> Option<&[u8]> {
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

    /// Returns the fragmentation ratio (0.0 = no fragmentation, 1.0 = all garbage).
    ///
    /// Fragmentation is the ratio of wasted space to total record area.
    fn fragmentation(&self) -> f32 {
        let header = self.header();
        let total_record_area = ((PAGE_SIZE - self.footer_size) as u16 - header.free_end) as usize;

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
}

// Mutable methods (available for T: AsRef<[u8]> + AsMut<[u8]>)
impl<T: AsRef<[u8]> + AsMut<[u8]>> SlottedPage<T> {
    /// Returns a mutable reference to slot data (raw bytes) by slot ID.
    ///
    /// Returns `None` if the slot is out of bounds or deleted.
    fn get_mut(&mut self, slot_id: SlotId) -> Option<&mut [u8]> {
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
        Some(&mut self.data_mut()[start..end])
    }

    /// Initializes this page as a new empty page.
    ///
    /// This zeroes the page and writes an empty heap page header with
    /// `free_end` set to `PAGE_SIZE - footer_size`.
    fn init(&mut self) {
        let free_end = (PAGE_SIZE - self.footer_size) as u16;
        self.data_mut().fill(0);
        PageHeader::new_heap_page(free_end).write(&mut self.data_mut()[..PAGE_HEADER_SIZE]);
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

    /// Inserts raw data and returns its slot ID.
    ///
    /// # Errors
    ///
    /// Returns `HeapError::PageFull` if there is not enough space.
    fn insert(&mut self, data: &[u8]) -> Result<SlotId, HeapError> {
        let mut header = self.header();

        let need_new_slot = header.first_free_slot == u16::MAX;
        let slot_overhead = if need_new_slot { SLOT_SIZE } else { 0 };
        self.ensure_free_space(&header, data.len() + slot_overhead)?;

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
        header.free_end -= data.len() as u16;
        let start = header.free_end as usize;
        self.data_mut()[start..start + data.len()].copy_from_slice(data);
        self.set_slot(slot_id, SlotEntry::new(start as u16, data.len() as u16));
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
    #[allow(dead_code)] // Used by VACUUM (not yet implemented)
    fn delete(&mut self, slot_id: SlotId) -> Result<(), HeapError> {
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

    /// Compacts the page by removing gaps between records.
    ///
    /// This operation:
    /// 1. Collects all valid records
    /// 2. Rewrites them contiguously from the bottom
    /// 3. Updates all slot offsets
    /// 4. Rebuilds the free list
    /// 5. Resets `free_end` to the new boundary
    ///
    /// After compaction, free space is maximized by removing gaps between records.
    ///
    /// NOTE: This is O(n) in the number of records. Call only when needed,
    /// such as when an insert fails but total space should be sufficient.
    fn compact(&mut self) {
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

        // Rewrite records from bottom of usable area
        header.free_end = (PAGE_SIZE - self.footer_size) as u16;
        for (slot_id, record) in &records {
            header.free_end -= record.len() as u16;
            let start = header.free_end as usize;
            self.data_mut()[start..start + record.len()].copy_from_slice(record);
            self.set_slot(*slot_id, SlotEntry::new(start as u16, record.len() as u16));
        }
        self.set_header(&header);
    }
}

/// A heap page for storing MVCC-aware tuples.
///
/// This struct wraps [`SlottedPage`] and provides high-level MVCC tuple operations.
/// It manages tuples (TupleHeader + Record) rather than raw bytes.
///
/// The type parameter `T` allows this to wrap:
/// - `&[u8]` - read-only view
/// - `&mut [u8]` - mutable view
/// - `Vec<u8>` - owned data
/// - Any type implementing `AsRef<[u8]>` (and optionally `AsMut<[u8]>`)
pub struct HeapPage<T> {
    page: SlottedPage<T>,
}

impl<T> HeapPage<T> {
    /// Consumes the page and returns the underlying data.
    pub fn into_inner(self) -> T {
        self.page.into_inner()
    }
}

// Read-only methods (available for any T: AsRef<[u8]>)
impl<T: AsRef<[u8]>> HeapPage<T> {
    /// Creates a new HeapPage view over the given data.
    ///
    /// # Panics
    ///
    /// Panics if `data.as_ref().len() != PAGE_SIZE`.
    pub fn new(data: T) -> Self {
        Self {
            page: SlottedPage::new(data, HEAP_FOOTER_SIZE),
        }
    }

    /// Returns the page header.
    pub fn header(&self) -> PageHeader {
        self.page.header()
    }

    /// Returns the next page in the heap page chain.
    ///
    /// Returns `None` if this is the last page in the chain (`next_page == 0`).
    pub fn next_page(&self) -> Option<PageId> {
        let offset = PAGE_SIZE - HEAP_FOOTER_SIZE;
        let data = self.page.data();
        let raw = u32::from_le_bytes([
            data[offset],
            data[offset + 1],
            data[offset + 2],
            data[offset + 3],
        ]);
        if raw == 0 {
            None
        } else {
            Some(PageId::new(raw as u64))
        }
    }

    /// Reads a tuple (header + record) by slot ID.
    ///
    /// Returns `None` if the slot is out of bounds or deleted.
    pub fn get(&self, slot_id: SlotId, schema: &[Type]) -> Option<(TupleHeader, Record)> {
        let raw = self.page.get(slot_id)?;

        let header = TupleHeader::read(&raw[..TUPLE_HEADER_SIZE]);
        let record = Record::deserialize(&raw[TUPLE_HEADER_SIZE..], schema).ok()?;
        Some((header, record))
    }

    /// Returns the tuple header at the given slot, without deserializing the record.
    ///
    /// Returns `None` if the slot is out of bounds or deleted.
    pub fn get_header(&self, slot_id: SlotId) -> Option<TupleHeader> {
        let raw = self.page.get(slot_id)?;
        Some(TupleHeader::read(&raw[..TUPLE_HEADER_SIZE]))
    }

    /// Returns an iterator over all tuples with headers.
    ///
    /// Yields `(SlotId, TupleHeader, Record)` for each valid (non-deleted) slot.
    pub fn scan<'a>(
        &'a self,
        schema: &'a [Type],
    ) -> impl Iterator<Item = (SlotId, TupleHeader, Record)> + 'a {
        let header = self.page.header();
        (0..header.slot_count).filter_map(move |slot_id| {
            let (tuple_header, record) = self.get(slot_id, schema)?;
            Some((slot_id, tuple_header, record))
        })
    }

    /// Returns the fragmentation ratio (0.0 = no fragmentation, 1.0 = all garbage).
    ///
    /// Fragmentation is the ratio of wasted space to total record area.
    /// This is useful for determining whether VACUUM should compact the page.
    pub fn fragmentation(&self) -> f32 {
        self.page.fragmentation()
    }
}

// Mutable methods (available for T: AsRef<[u8]> + AsMut<[u8]>)
impl<T: AsRef<[u8]> + AsMut<[u8]>> HeapPage<T> {
    /// Initializes this page as a new empty heap page.
    ///
    /// This zeroes the page (including the `HeapFooter` region at the tail) and
    /// writes an empty heap page header with `free_end` set to `PAGE_SIZE - HEAP_FOOTER_SIZE`.
    /// The `next_page` field defaults to 0 (no next page) from the zeroed bytes.
    pub fn init(&mut self) {
        self.page.init();
    }

    /// Sets the next page in the heap page chain.
    ///
    /// Pass `None` to mark this as the last page in the chain.
    ///
    /// NOTE: `next_page` is stored as `u32`, limiting the chain to ~4 billion pages
    /// (32TB at 8KB/page). This is sufficient for this project's scope.
    pub fn set_next_page(&mut self, next: Option<PageId>) {
        let raw: u32 = match next {
            Some(page_id) => {
                debug_assert!(
                    page_id.page_num() <= u32::MAX as u64,
                    "page_num {} exceeds u32 range for next_page",
                    page_id.page_num()
                );
                page_id.page_num() as u32
            }
            None => 0,
        };
        let offset = PAGE_SIZE - HEAP_FOOTER_SIZE;
        let data = self.page.data_mut();
        data[offset..offset + HEAP_FOOTER_SIZE].copy_from_slice(&raw.to_le_bytes());
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
    /// After compaction, free space is maximized by removing gaps between records.
    ///
    /// NOTE: This is O(n) in the number of records. Call only when needed
    /// (e.g., during VACUUM when fragmentation exceeds a threshold).
    pub fn compact(&mut self) {
        self.page.compact();
    }

    /// Inserts a record with MVCC tuple header.
    ///
    /// This serializes the tuple header and record together into a single
    /// slot, making MVCC versioning transparent at the page level.
    ///
    /// # Errors
    ///
    /// Returns `HeapError::PageFull` if there is not enough space.
    pub fn insert(
        &mut self,
        record: &Record,
        xmin: TxId,
        cmin: CommandId,
    ) -> Result<SlotId, HeapError> {
        // Serialize tuple header + record
        let header = TupleHeader::new(xmin, cmin);
        let record_size = record.serialized_size();
        let total_size = TUPLE_HEADER_SIZE + record_size;

        let mut buf = vec![0u8; total_size];
        header.write(&mut buf[..TUPLE_HEADER_SIZE]);
        record.serialize(&mut buf[TUPLE_HEADER_SIZE..])?;

        // Insert as raw slot data
        self.page.insert(&buf)
    }

    /// Updates just the tuple header in an existing slot.
    ///
    /// This is used to modify transaction visibility information (e.g., setting
    /// xmax for DELETE) without changing the record data.
    ///
    /// # Errors
    ///
    /// Returns `HeapError::SlotNotFound` if the slot doesn't exist or is deleted.
    pub fn update_header(&mut self, slot_id: SlotId, header: TupleHeader) -> Result<(), HeapError> {
        // Get mutable access to the slot data
        let slot_data = self
            .page
            .get_mut(slot_id)
            .ok_or(HeapError::SlotNotFound(slot_id))?;

        // Write new header and overwrite first TUPLE_HEADER_SIZE bytes
        header.write(&mut slot_data[..TUPLE_HEADER_SIZE]);

        Ok(())
    }

    /// Updates the record data in an existing slot in-place.
    ///
    /// This performs a direct overwrite of the record portion (after TupleHeader),
    /// bypassing MVCC versioning. The new record must have exactly the same
    /// serialized size as the existing record.
    ///
    /// This is used for operations that intentionally bypass MVCC, such as:
    /// - Sequence updates (nextval) which are never rolled back
    ///
    /// The tuple header is NOT modified by this operation.
    ///
    /// # Errors
    ///
    /// Returns `HeapError::SlotNotFound` if the slot doesn't exist or is deleted.
    /// Returns `HeapError::RecordSizeMismatch` if the new record has a different size.
    pub fn update_record_in_place(
        &mut self,
        slot_id: SlotId,
        record: &Record,
    ) -> Result<(), HeapError> {
        let slot_data = self
            .page
            .get_mut(slot_id)
            .ok_or(HeapError::SlotNotFound(slot_id))?;

        let record_data = &mut slot_data[TUPLE_HEADER_SIZE..];

        if record.serialized_size() != record_data.len() {
            return Err(HeapError::RecordSizeMismatch {
                expected: record_data.len(),
                actual: record.serialized_size(),
            });
        }

        record.serialize(record_data)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::datum::{Type, Value};
    use crate::heap::Record;
    use crate::storage::{PAGE_VERSION, PageId, PageType};
    use crate::tx::{CommandId, Infomask, TupleHeader, TxId};

    fn create_slotted_page() -> SlottedPage<Vec<u8>> {
        let mut page = SlottedPage::new(vec![0u8; PAGE_SIZE], HEAP_FOOTER_SIZE);
        page.init();
        page
    }

    #[test]
    fn test_slotted_page_header_roundtrip() {
        let page = create_slotted_page();
        let header = page.header();
        assert_eq!(header.page_lsn, 0);
        assert_eq!(header.checksum, 0);
        assert_eq!(header.page_type, PageType::Heap);
        assert_eq!(header.page_version, PAGE_VERSION);
        assert_eq!(header.flags, 0);
        assert_eq!(header.slot_count, 0);
        assert_eq!(header.free_start(SLOT_SIZE), PAGE_HEADER_SIZE as u16);
        assert_eq!(header.free_end, (PAGE_SIZE - HEAP_FOOTER_SIZE) as u16);
        assert_eq!(header.first_free_slot, u16::MAX);
    }

    #[test]
    fn test_slotted_page_insert_and_get() {
        let mut page = create_slotted_page();

        let data = b"hello world";
        let slot_id = page.insert(data).unwrap();

        assert_eq!(slot_id, 0);
        assert_eq!(page.get(slot_id), Some(data.as_slice()));
        assert_eq!(page.header().slot_count, 1);
    }

    #[test]
    fn test_slotted_page_multiple_inserts() {
        let mut page = create_slotted_page();

        let records: Vec<&[u8]> = vec![b"first", b"second", b"third"];
        let slot_ids: Vec<_> = records.iter().map(|r| page.insert(r).unwrap()).collect();

        assert_eq!(slot_ids, vec![0, 1, 2]);
        for (slot_id, expected) in slot_ids.iter().zip(records.iter()) {
            assert_eq!(page.get(*slot_id), Some(*expected));
        }
        assert_eq!(page.header().slot_count, 3);
    }

    #[test]
    fn test_slotted_page_get_invalid_slot() {
        let page = create_slotted_page();

        assert!(page.get(0).is_none());
        assert!(page.get(100).is_none());
    }

    #[test]
    fn test_slotted_page_delete() {
        let mut page = create_slotted_page();

        let slot0 = page.insert(b"record0").unwrap();
        let slot1 = page.insert(b"record1").unwrap();

        page.delete(slot0).unwrap();

        assert!(page.get(slot0).is_none());
        assert_eq!(page.get(slot1), Some(b"record1".as_slice()));

        // New insert should reuse the deleted slot
        let slot2 = page.insert(b"record2").unwrap();
        assert_eq!(slot2, slot0);
        assert_eq!(page.get(slot2), Some(b"record2".as_slice()));
    }

    #[test]
    fn test_slotted_page_delete_free_list() {
        let mut page = create_slotted_page();

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
        assert_eq!(page.get(slot1), Some(b"b".as_slice()));
    }

    #[test]
    fn test_slotted_page_delete_invalid_slot() {
        let mut page = create_slotted_page();

        assert!(matches!(page.delete(0), Err(HeapError::SlotNotFound(0))));

        let slot = page.insert(b"test").unwrap();
        page.delete(slot).unwrap();

        // Deleting already deleted slot should fail
        assert!(matches!(page.delete(slot), Err(HeapError::SlotNotFound(_))));
    }

    #[test]
    fn test_slotted_page_page_full() {
        let mut page = create_slotted_page();

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
    fn test_slotted_page_compact() {
        let mut page = create_slotted_page();

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
        assert!(page.get(slot0).is_some());
        assert!(page.get(slot1).is_none()); // Still deleted
        assert!(page.get(slot2).is_some());

        // Can insert using recovered space (reuses deleted slot)
        let slot3 = page.insert(&large_record).unwrap();
        assert_eq!(slot3, slot1);
    }

    #[test]
    fn test_slotted_page_max_slot_data_size() {
        let mut page = create_slotted_page();

        let max_data = vec![0u8; MAX_SLOT_DATA_SIZE];
        let slot = page.insert(&max_data).unwrap();
        assert_eq!(page.get(slot).map(|r| r.len()), Some(MAX_SLOT_DATA_SIZE));

        // But not another one
        assert!(matches!(
            page.insert(&[0u8; 1]),
            Err(HeapError::PageFull { .. })
        ));
    }

    #[test]
    fn test_slotted_page_free_space_calculation() {
        let mut page = create_slotted_page();

        let initial_free = page.header().free_space(SLOT_SIZE) as usize;
        assert_eq!(
            initial_free,
            PAGE_SIZE - HEAP_FOOTER_SIZE - PAGE_HEADER_SIZE
        );

        // Insert a record
        let data = b"test data";
        page.insert(data).unwrap();

        // Free space should decrease by record size + slot size
        let expected_free = initial_free - data.len() - SLOT_SIZE;
        assert_eq!(page.header().free_space(SLOT_SIZE) as usize, expected_free);
    }

    #[test]
    fn test_slotted_page_empty_record() {
        let mut page = create_slotted_page();

        let slot = page.insert(b"").unwrap();
        assert_eq!(page.get(slot), Some(b"".as_slice()));
    }

    fn create_heap_page() -> HeapPage<Vec<u8>> {
        let mut page = HeapPage::new(vec![0u8; PAGE_SIZE]);
        page.init();
        page
    }

    #[test]
    fn test_heap_page_insert() {
        let mut page = create_heap_page();
        let record = Record::new(vec![Value::Integer(42), Value::Text("hello".to_string())]);

        let slot = page
            .insert(&record, TxId::new(1), CommandId::FIRST)
            .unwrap();
        assert_eq!(slot, 0);

        // Verify we can read it back
        let schema = [Type::Integer, Type::Text];
        let (header, read_record) = page.get(slot, &schema).unwrap();

        assert_eq!(header.xmin, TxId::new(1));
        assert_eq!(header.xmax, TxId::INVALID);
        assert_eq!(header.cmin, CommandId::FIRST);
        assert_eq!(header.cmax, CommandId::INVALID);
        assert_eq!(read_record, record);
    }

    #[test]
    fn test_heap_page_get_none_for_deleted_slot() {
        let page = create_heap_page();
        let schema = [Type::Integer];

        // Slot doesn't exist
        assert!(page.get(0, &schema).is_none());
    }

    #[test]
    fn test_heap_page_update_header() {
        let mut page = create_heap_page();
        let record = Record::new(vec![Value::Integer(100)]);

        let slot = page
            .insert(&record, TxId::new(1), CommandId::FIRST)
            .unwrap();

        // Update the tuple header (e.g., marking as deleted)
        let new_header = TupleHeader {
            xmin: TxId::new(1),
            xmax: TxId::new(2), // Mark as deleted by transaction 2
            cmin: CommandId::FIRST,
            cmax: CommandId::new(1), // Deleted at command 1
            infomask: Infomask::empty().with_xmin_committed(),
        };
        page.update_header(slot, new_header).unwrap();

        // Read back and verify
        let schema = [Type::Integer];
        let (header, read_record) = page.get(slot, &schema).unwrap();

        assert_eq!(header.xmin, TxId::new(1));
        assert_eq!(header.xmax, TxId::new(2));
        assert!(header.infomask.xmin_committed());
        assert_eq!(read_record, record);
    }

    #[test]
    fn test_heap_page_scan() {
        let mut page = create_heap_page();

        // Insert multiple tuples
        let record1 = Record::new(vec![Value::Integer(1)]);
        let record2 = Record::new(vec![Value::Integer(2)]);
        let record3 = Record::new(vec![Value::Integer(3)]);

        page.insert(&record1, TxId::new(1), CommandId::FIRST)
            .unwrap();
        page.insert(&record2, TxId::new(2), CommandId::FIRST)
            .unwrap();
        page.insert(&record3, TxId::new(3), CommandId::FIRST)
            .unwrap();

        // Iterate and collect
        let schema = [Type::Integer];
        let tuples: Vec<_> = page.scan(&schema).collect();

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
    fn test_heap_page_insert_with_null_values() {
        let mut page = create_heap_page();
        let record = Record::new(vec![
            Value::Integer(42),
            Value::Null,
            Value::Text("test".to_string()),
        ]);

        let slot = page
            .insert(&record, TxId::new(1), CommandId::FIRST)
            .unwrap();

        // Read back and verify element-by-element (Value::Null != Value::Null)
        let schema = [Type::Integer, Type::Integer, Type::Text];
        let (_, read_record) = page.get(slot, &schema).unwrap();
        assert_eq!(read_record.len(), record.len());
        assert_eq!(read_record.values[0], record.values[0]);
        assert!(read_record.values[1].is_null());
        assert_eq!(read_record.values[2], record.values[2]);
    }

    #[test]
    fn test_heap_page_update_header_invalid_slot() {
        let mut page = create_heap_page();
        let header = TupleHeader::new(TxId::new(1), CommandId::FIRST);

        assert!(matches!(
            page.update_header(0, header),
            Err(HeapError::SlotNotFound(0))
        ));
    }

    #[test]
    fn test_heap_page_update_record_in_place() {
        let mut page = create_heap_page();

        // Insert initial record
        let record = Record::new(vec![Value::Integer(1), Value::Bigint(100)]);
        let slot = page
            .insert(&record, TxId::new(1), CommandId::FIRST)
            .unwrap();

        // Update in-place with same-size record
        let updated = Record::new(vec![Value::Integer(1), Value::Bigint(200)]);
        page.update_record_in_place(slot, &updated).unwrap();

        // Verify update
        let schema = [Type::Integer, Type::Bigint];
        let (header, read_record) = page.get(slot, &schema).unwrap();

        // Header unchanged
        assert_eq!(header.xmin, TxId::new(1));
        assert_eq!(header.xmax, TxId::INVALID);

        // Record updated
        assert_eq!(read_record, updated);
    }

    #[test]
    fn test_heap_page_update_record_in_place_size_mismatch() {
        let mut page = create_heap_page();

        // Insert initial record
        let record = Record::new(vec![Value::Integer(1)]);
        let slot = page
            .insert(&record, TxId::new(1), CommandId::FIRST)
            .unwrap();

        // Try to update with different-size record
        let updated = Record::new(vec![Value::Integer(1), Value::Bigint(200)]);
        let result = page.update_record_in_place(slot, &updated);

        assert!(matches!(result, Err(HeapError::RecordSizeMismatch { .. })));
    }

    #[test]
    fn test_heap_page_next_page_roundtrip() {
        let mut page = create_heap_page();

        // Initially no next page
        assert_eq!(page.next_page(), None);

        // Set next page
        page.set_next_page(Some(PageId::new(42)));
        assert_eq!(page.next_page(), Some(PageId::new(42)));

        // Change next page
        page.set_next_page(Some(PageId::new(100)));
        assert_eq!(page.next_page(), Some(PageId::new(100)));

        // Clear next page
        page.set_next_page(None);
        assert_eq!(page.next_page(), None);
    }

    #[test]
    fn test_heap_page_init_clears_next_page() {
        let mut page = create_heap_page();
        page.set_next_page(Some(PageId::new(42)));
        assert_eq!(page.next_page(), Some(PageId::new(42)));

        // Re-init should clear next_page
        page.init();
        assert_eq!(page.next_page(), None);
    }

    #[test]
    fn test_heap_page_next_page_does_not_interfere_with_tuples() {
        let mut page = create_heap_page();
        page.set_next_page(Some(PageId::new(99)));

        // Insert a tuple
        let record = Record::new(vec![Value::Integer(42)]);
        let slot = page
            .insert(&record, TxId::new(1), CommandId::FIRST)
            .unwrap();

        // Verify both next_page and tuple are correct
        assert_eq!(page.next_page(), Some(PageId::new(99)));
        let schema = [Type::Integer];
        let (header, read_record) = page.get(slot, &schema).unwrap();
        assert_eq!(header.xmin, TxId::new(1));
        assert_eq!(read_record, record);
    }
}
