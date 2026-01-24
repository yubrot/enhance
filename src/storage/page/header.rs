//! Page header format for the storage layer.
//!
//! This module defines the common page header structure used by all page types
//! in the database. The header contains metadata for page identification,
//! integrity checking, and space management.
//!
//! **Note:** The storage I/O layer (`Storage` trait implementations) does not
//! interpret this header during read/write operations—it simply reads and writes
//! raw 8KB page buffers. Header interpretation is the responsibility of higher-level
//! modules (e.g., heap pages, B+tree nodes) that manage specific page formats.

use super::PAGE_SIZE;

/// Size of the page header in bytes.
pub const PAGE_HEADER_SIZE: usize = 24;

/// Current page layout version.
pub const PAGE_VERSION: u8 = 1;

/// Page type identifiers.
///
/// Used to distinguish different page formats within the database.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PageType {
    /// Uninitialized or free page.
    Free = 0,
    /// Data page with slotted records (heap).
    Data = 1,
}

impl PageType {
    /// Creates a PageType from a raw u8 value.
    ///
    /// Returns `None` if the value doesn't match any known page type.
    pub fn from_u8(v: u8) -> Option<Self> {
        match v {
            0 => Some(PageType::Free),
            1 => Some(PageType::Data),
            _ => None,
        }
    }
}

/// Page header stored at the beginning of each page.
///
/// Layout (24 bytes total):
/// - `page_lsn`: u64 (8 bytes) - LSN of last modification (for WAL/recovery)
/// - `checksum`: u16 (2 bytes) - Page checksum (0 = not computed)
/// - `page_type`: u8 (1 byte)
/// - `page_version`: u8 (1 byte) - Layout version for format migration
/// - `flags`: u16 (2 bytes) - Page state flags
/// - `slot_count`: u16 (2 bytes)
/// - `free_start`: u16 (2 bytes)
/// - `free_end`: u16 (2 bytes)
/// - `first_free_slot`: u16 (2 bytes)
/// - `reserved`: [u8; 2]
///
/// This layout is inspired by PostgreSQL's PageHeaderData (24 bytes) and provides
/// fields necessary for WAL integration (Week 21-23) and corruption detection.
#[derive(Debug, Clone, Copy)]
pub struct PageHeader {
    /// Log Sequence Number of the last WAL record that modified this page.
    /// Used for crash recovery to determine if a page needs redo.
    /// Set to 0 until WAL is implemented.
    pub page_lsn: u64,
    /// Checksum of the page contents for corruption detection.
    /// Set to 0 when checksums are disabled or not yet computed.
    pub checksum: u16,
    /// Type of this page.
    pub page_type: PageType,
    /// Layout version number for format migration.
    /// Current version is 1.
    pub page_version: u8,
    /// Page state flags (e.g., has free lines, page full hint).
    pub flags: u16,
    /// Number of slots in the slot array (including deleted slots).
    pub slot_count: u16,
    /// Offset where free space starts (end of slot array).
    pub free_start: u16,
    /// Offset where free space ends (start of record area).
    pub free_end: u16,
    /// Index of first free (deleted) slot, or `u16::MAX` if none.
    pub first_free_slot: u16,
}

impl PageHeader {
    /// Creates a new header for an empty data page.
    pub fn new_data_page() -> Self {
        Self {
            page_lsn: 0,
            checksum: 0,
            page_type: PageType::Data,
            page_version: PAGE_VERSION,
            flags: 0,
            slot_count: 0,
            free_start: PAGE_HEADER_SIZE as u16,
            free_end: PAGE_SIZE as u16,
            first_free_slot: u16::MAX,
        }
    }

    /// Returns the amount of contiguous free space available.
    pub fn free_space(&self) -> u16 {
        self.free_end.saturating_sub(self.free_start)
    }

    /// Reads a header from a page byte slice.
    pub fn read_from(data: &[u8]) -> Self {
        Self {
            page_lsn: u64::from_le_bytes([
                data[0], data[1], data[2], data[3], data[4], data[5], data[6], data[7],
            ]),
            checksum: u16::from_le_bytes([data[8], data[9]]),
            page_type: PageType::from_u8(data[10]).unwrap_or(PageType::Free),
            page_version: data[11],
            flags: u16::from_le_bytes([data[12], data[13]]),
            slot_count: u16::from_le_bytes([data[14], data[15]]),
            free_start: u16::from_le_bytes([data[16], data[17]]),
            free_end: u16::from_le_bytes([data[18], data[19]]),
            first_free_slot: u16::from_le_bytes([data[20], data[21]]),
            // Bytes 22..24 are reserved
        }
    }

    /// Writes the header to a page byte slice.
    pub fn write_to(&self, data: &mut [u8]) {
        data[0..8].copy_from_slice(&self.page_lsn.to_le_bytes());
        data[8..10].copy_from_slice(&self.checksum.to_le_bytes());
        data[10] = self.page_type as u8;
        data[11] = self.page_version;
        data[12..14].copy_from_slice(&self.flags.to_le_bytes());
        data[14..16].copy_from_slice(&self.slot_count.to_le_bytes());
        data[16..18].copy_from_slice(&self.free_start.to_le_bytes());
        data[18..20].copy_from_slice(&self.free_end.to_le_bytes());
        data[20..22].copy_from_slice(&self.first_free_slot.to_le_bytes());
        // Bytes 22..24 are reserved and should remain zeroed
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_page_type_from_u8() {
        assert_eq!(PageType::from_u8(0), Some(PageType::Free));
        assert_eq!(PageType::from_u8(1), Some(PageType::Data));
        assert_eq!(PageType::from_u8(2), None);
        assert_eq!(PageType::from_u8(255), None);
    }

    #[test]
    fn test_header_new_data_page() {
        let header = PageHeader::new_data_page();
        assert_eq!(header.page_lsn, 0);
        assert_eq!(header.checksum, 0);
        assert_eq!(header.page_type, PageType::Data);
        assert_eq!(header.page_version, PAGE_VERSION);
        assert_eq!(header.flags, 0);
        assert_eq!(header.slot_count, 0);
        assert_eq!(header.free_start, PAGE_HEADER_SIZE as u16);
        assert_eq!(header.free_end, PAGE_SIZE as u16);
        assert_eq!(header.first_free_slot, u16::MAX);
    }

    #[test]
    fn test_header_free_space() {
        let header = PageHeader::new_data_page();
        assert_eq!(
            header.free_space(),
            (PAGE_SIZE - PAGE_HEADER_SIZE) as u16
        );
    }

    #[test]
    fn test_header_roundtrip() {
        let original = PageHeader {
            page_lsn: 0x123456789ABCDEF0,
            checksum: 0xABCD,
            page_type: PageType::Data,
            page_version: 1,
            flags: 0x1234,
            slot_count: 42,
            free_start: 100,
            free_end: 8000,
            first_free_slot: 5,
        };

        let mut buf = vec![0u8; PAGE_HEADER_SIZE];
        original.write_to(&mut buf);

        let parsed = PageHeader::read_from(&buf);
        assert_eq!(parsed.page_lsn, original.page_lsn);
        assert_eq!(parsed.checksum, original.checksum);
        assert_eq!(parsed.page_type, original.page_type);
        assert_eq!(parsed.page_version, original.page_version);
        assert_eq!(parsed.flags, original.flags);
        assert_eq!(parsed.slot_count, original.slot_count);
        assert_eq!(parsed.free_start, original.free_start);
        assert_eq!(parsed.free_end, original.free_end);
        assert_eq!(parsed.first_free_slot, original.first_free_slot);
    }
}
