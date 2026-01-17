//! Page identifier and size constants.

/// 8KB page size (aligned with OS page size and PostgreSQL standard).
pub const PAGE_SIZE: usize = 8192;

/// Unique identifier for a page within the storage system.
///
/// PageId is a 64-bit value that uniquely identifies a page. The value
/// encodes the page number within the storage backend.
///
/// NOTE: For production, this could be extended to support multiple files
/// (tablespaces, indexes, etc.) by encoding file_id in the high bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PageId(pub u64);

impl PageId {
    /// Creates a new PageId from a page number.
    pub const fn new(page_num: u64) -> Self {
        Self(page_num)
    }

    /// Returns the page number.
    pub const fn page_num(&self) -> u64 {
        self.0
    }

    /// Calculates the byte offset for this page in a storage file.
    ///
    /// This is used by FileStorage to seek to the correct position.
    pub const fn byte_offset(&self) -> u64 {
        self.0 * PAGE_SIZE as u64
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_page_id_byte_offset() {
        assert_eq!(PageId::new(0).byte_offset(), 0);
        assert_eq!(PageId::new(1).byte_offset(), 8192);
        assert_eq!(PageId::new(100).byte_offset(), 819200);
        assert_eq!(PageId::new(1000).byte_offset(), 8192000);
    }

    #[test]
    fn test_page_id_new() {
        let page_id = PageId::new(42);
        assert_eq!(page_id.page_num(), 42);
    }

    #[test]
    fn test_page_id_ordering() {
        assert!(PageId::new(0) < PageId::new(1));
        assert!(PageId::new(1) < PageId::new(100));
        assert_eq!(PageId::new(42), PageId::new(42));
    }
}
