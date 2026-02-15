//! Superblock structure for database metadata.
//!
//! The superblock occupies page 0 and contains metadata about the database,
//! including pointers to catalog tables and ID generators.

use super::error::EngineError;
use crate::storage::PageId;

/// Magic number for the enhance database format ("ENHN" in hex).
const MAGIC: u32 = 0x454E_484E;

/// Current superblock format version.
const VERSION: u32 = 1;

/// Superblock containing database metadata.
///
/// Layout (48 bytes):
/// - `magic`: u32 (4 bytes) - Magic number to identify format
/// - `version`: u32 (4 bytes) - Format version for compatibility
/// - `sys_tables_page`: u64 (8 bytes) - Page ID for sys_tables
/// - `sys_columns_page`: u64 (8 bytes) - Page ID for sys_columns
/// - `sys_sequences_page`: u64 (8 bytes) - Page ID for sys_sequences
/// - `next_table_id`: u32 (4 bytes) - Next table ID to allocate
/// - `next_seq_id`: u32 (4 bytes) - Next sequence ID to allocate
/// - Reserved: 8 bytes for future use
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Superblock {
    /// Magic number to identify the database format.
    pub magic: u32,
    /// Format version for compatibility checks.
    pub version: u32,
    /// Page ID of the sys_tables heap page.
    pub sys_tables_page: PageId,
    /// Page ID of the sys_columns heap page.
    pub sys_columns_page: PageId,
    /// Page ID of the sys_sequences heap page.
    pub sys_sequences_page: PageId,
    /// Next table ID to allocate.
    pub next_table_id: u32,
    /// Next sequence ID to allocate.
    pub next_seq_id: u32,
}

impl Superblock {
    /// Size of the superblock data in bytes.
    pub const SIZE: usize = 48;

    /// Creates a new superblock with default values.
    ///
    /// The catalog page IDs must be set after allocating pages.
    pub fn new() -> Self {
        Self {
            magic: MAGIC,
            version: VERSION,
            sys_tables_page: PageId::new(0),
            sys_columns_page: PageId::new(0),
            sys_sequences_page: PageId::new(0),
            next_table_id: 1,
            next_seq_id: 1,
        }
    }

    /// Reads a superblock from a page buffer.
    ///
    /// # Panics
    ///
    /// Panics if the buffer is smaller than [`Self::SIZE`].
    pub fn read(buf: &[u8]) -> Self {
        assert!(
            buf.len() >= Self::SIZE,
            "buffer too small for superblock: {} < {}",
            buf.len(),
            Self::SIZE
        );

        let magic = u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]);
        let version = u32::from_le_bytes([buf[4], buf[5], buf[6], buf[7]]);
        let sys_tables_page = PageId::new(u64::from_le_bytes([
            buf[8], buf[9], buf[10], buf[11], buf[12], buf[13], buf[14], buf[15],
        ]));
        let sys_columns_page = PageId::new(u64::from_le_bytes([
            buf[16], buf[17], buf[18], buf[19], buf[20], buf[21], buf[22], buf[23],
        ]));
        let sys_sequences_page = PageId::new(u64::from_le_bytes([
            buf[24], buf[25], buf[26], buf[27], buf[28], buf[29], buf[30], buf[31],
        ]));
        let next_table_id = u32::from_le_bytes([buf[32], buf[33], buf[34], buf[35]]);
        let next_seq_id = u32::from_le_bytes([buf[36], buf[37], buf[38], buf[39]]);

        Self {
            magic,
            version,
            sys_tables_page,
            sys_columns_page,
            sys_sequences_page,
            next_table_id,
            next_seq_id,
        }
    }

    /// Writes the superblock to a page buffer.
    ///
    /// # Panics
    ///
    /// Panics if the buffer is smaller than [`Self::SIZE`].
    pub fn write(&self, buf: &mut [u8]) {
        assert!(
            buf.len() >= Self::SIZE,
            "buffer too small for superblock: {} < {}",
            buf.len(),
            Self::SIZE
        );

        buf[0..4].copy_from_slice(&self.magic.to_le_bytes());
        buf[4..8].copy_from_slice(&self.version.to_le_bytes());
        buf[8..16].copy_from_slice(&self.sys_tables_page.page_num().to_le_bytes());
        buf[16..24].copy_from_slice(&self.sys_columns_page.page_num().to_le_bytes());
        buf[24..32].copy_from_slice(&self.sys_sequences_page.page_num().to_le_bytes());
        buf[32..36].copy_from_slice(&self.next_table_id.to_le_bytes());
        buf[36..40].copy_from_slice(&self.next_seq_id.to_le_bytes());
        // Reserved bytes 40..48 are left as-is (should be zeroed on init)
    }

    /// Validates the superblock magic and version.
    ///
    /// Returns `Ok(())` if valid, otherwise returns an error describing the issue.
    pub fn validate(&self) -> Result<(), EngineError> {
        if self.magic != MAGIC {
            return Err(EngineError::InvalidMagic {
                expected: MAGIC,
                found: self.magic,
            });
        }
        if self.version != VERSION {
            return Err(EngineError::UnsupportedVersion {
                expected: VERSION,
                found: self.version,
            });
        }
        Ok(())
    }

    /// Allocates and returns the next table ID.
    pub fn allocate_table_id(&mut self) -> u32 {
        let id = self.next_table_id;
        self.next_table_id += 1;
        id
    }

    /// Allocates and returns the next sequence ID.
    pub fn allocate_seq_id(&mut self) -> u32 {
        let id = self.next_seq_id;
        self.next_seq_id += 1;
        id
    }
}

impl Default for Superblock {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_superblock_new() {
        let sb = Superblock::new();
        assert_eq!(sb.magic, MAGIC);
        assert_eq!(sb.version, VERSION);
        assert_eq!(sb.sys_tables_page, PageId::new(0));
        assert_eq!(sb.sys_columns_page, PageId::new(0));
        assert_eq!(sb.sys_sequences_page, PageId::new(0));
        assert_eq!(sb.next_table_id, 1);
        assert_eq!(sb.next_seq_id, 1);
    }

    #[test]
    fn test_superblock_roundtrip() {
        let mut sb = Superblock::new();
        sb.sys_tables_page = PageId::new(1);
        sb.sys_columns_page = PageId::new(2);
        sb.sys_sequences_page = PageId::new(3);
        sb.next_table_id = 100;
        sb.next_seq_id = 50;

        let mut buf = vec![0u8; Superblock::SIZE];
        sb.write(&mut buf);

        let sb2 = Superblock::read(&buf);
        assert_eq!(sb, sb2);
    }

    #[test]
    fn test_superblock_validate() {
        let sb = Superblock::new();
        assert!(sb.validate().is_ok());

        let mut bad_magic = Superblock::new();
        bad_magic.magic = 0xDEADBEEF;
        assert!(matches!(
            bad_magic.validate(),
            Err(EngineError::InvalidMagic { .. })
        ));

        let mut bad_version = Superblock::new();
        bad_version.version = 99;
        assert!(matches!(
            bad_version.validate(),
            Err(EngineError::UnsupportedVersion { .. })
        ));
    }

    #[test]
    fn test_superblock_allocate_ids() {
        let mut sb = Superblock::new();

        assert_eq!(sb.allocate_table_id(), 1);
        assert_eq!(sb.allocate_table_id(), 2);
        assert_eq!(sb.allocate_table_id(), 3);
        assert_eq!(sb.next_table_id, 4);

        assert_eq!(sb.allocate_seq_id(), 1);
        assert_eq!(sb.allocate_seq_id(), 2);
        assert_eq!(sb.next_seq_id, 3);
    }
}
