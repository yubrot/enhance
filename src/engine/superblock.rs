//! Superblock structure for database metadata.
//!
//! The superblock occupies page 0 and contains metadata about the database,
//! including first-page pointers for system catalog heap chains and ID generators.

use super::error::EngineError;
use crate::catalog::{ColumnInfo, SequenceInfo, SystemCatalogTable, TableInfo};
use crate::heap::{HeapPage, insert};
use crate::storage::{BufferPool, PageId, Replacer, Storage};
use crate::tx::{CommandId, TxId};

/// Magic number for the enhance database format ("ENHN" in hex).
const MAGIC: u32 = 0x454E_484E;

/// Current superblock format version.
const VERSION: u32 = 1;

/// Superblock containing database metadata.
///
/// Layout (48 bytes):
/// - `magic`: u32 (4 bytes) - Magic number to identify format
/// - `version`: u32 (4 bytes) - Format version for compatibility
/// - `sys_tables_page`: u64 (8 bytes) - First page of sys_tables heap chain
/// - `sys_columns_page`: u64 (8 bytes) - First page of sys_columns heap chain
/// - `sys_sequences_page`: u64 (8 bytes) - First page of sys_sequences heap chain
/// - `next_table_id`: u32 (4 bytes) - Next table ID to allocate
/// - `next_seq_id`: u32 (4 bytes) - Next sequence ID to allocate
/// - Reserved: 8 bytes for future use
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Superblock {
    /// Magic number to identify the database format.
    pub magic: u32,
    /// Format version for compatibility checks.
    pub version: u32,
    /// First page of the sys_tables heap chain.
    pub sys_tables_page: PageId,
    /// First page of the sys_columns heap chain.
    pub sys_columns_page: PageId,
    /// First page of the sys_sequences heap chain.
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

    /// Opens or initializes the database superblock.
    ///
    /// If the storage is empty (page_count == 0), initializes a new database
    /// by creating catalog pages and inserting initial metadata.
    /// Otherwise, reads and validates the existing superblock from page 0.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Storage I/O fails
    /// - Superblock validation fails (invalid magic or version)
    pub async fn boot<S: Storage, R: Replacer>(
        pool: &BufferPool<S, R>,
    ) -> Result<Self, EngineError> {
        match pool.page_count().await {
            0 => Self::initialize(pool).await,
            _ => Self::load(pool).await,
        }
    }

    /// Bootstraps the catalog for a fresh database.
    ///
    /// Creates the initial catalog pages and inserts metadata for the
    /// catalog tables themselves.
    ///
    /// NOTE: Without WAL (Step 13), crash during bootstrap leaves the
    /// database in an inconsistent state that cannot be recovered.
    async fn initialize<S: Storage, R: Replacer>(
        pool: &BufferPool<S, R>,
    ) -> Result<Self, EngineError> {
        let mut sb_guard = pool.new_page().await?;
        // NOTE: Using assert_eq! here panics instead of returning an error.
        // Production code should return an appropriate error.
        assert_eq!(sb_guard.page_id(), PageId::new(0), "First page must be 0");

        let sys_tables_guard = pool.new_page().await?;
        let sys_tables_page = sys_tables_guard.page_id();
        HeapPage::new(sys_tables_guard).init();

        let sys_columns_guard = pool.new_page().await?;
        let sys_columns_page = sys_columns_guard.page_id();
        HeapPage::new(sys_columns_guard).init();

        let sys_sequences_guard = pool.new_page().await?;
        let sys_sequences_page = sys_sequences_guard.page_id();
        HeapPage::new(sys_sequences_guard).init();

        let mut superblock = Self::new();
        superblock.sys_tables_page = sys_tables_page;
        superblock.sys_columns_page = sys_columns_page;
        superblock.sys_sequences_page = sys_sequences_page;
        superblock.next_table_id = crate::catalog::LAST_RESERVED_TABLE_ID + 1;
        superblock.next_seq_id = 1;

        superblock.write(sb_guard.data_mut());
        drop(sb_guard);

        // Bootstrap uses TxId::FROZEN so tuples are immediately visible without
        // requiring a transaction commit. This is safe because bootstrap runs
        // exclusively at database initialization time.
        let txid = TxId::FROZEN;
        let cid = CommandId::FIRST;

        // Insert catalog table metadata into sys_tables
        for table_info in [
            TableInfo::table_info(sys_tables_page),
            ColumnInfo::table_info(sys_columns_page),
            SequenceInfo::table_info(sys_sequences_page),
        ] {
            insert(pool, sys_tables_page, &table_info.to_record(), txid, cid).await?;
        }

        // Insert column metadata into sys_columns
        for col in TableInfo::columns()
            .into_iter()
            .chain(ColumnInfo::columns())
            .chain(SequenceInfo::columns())
        {
            insert(pool, sys_columns_page, &col.to_record(), txid, cid).await?;
        }

        pool.flush_all().await?;

        Ok(superblock)
    }

    /// Reads and validates the existing superblock from page 0.
    async fn load<S: Storage, R: Replacer>(pool: &BufferPool<S, R>) -> Result<Self, EngineError> {
        let guard = pool.fetch_page(PageId::new(0)).await?;
        let superblock = Self::read(guard.data());
        drop(guard);
        superblock.validate()?;
        Ok(superblock)
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
    use crate::catalog::LAST_RESERVED_TABLE_ID;
    use crate::storage::tests::test_pool;

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

    #[tokio::test]
    async fn test_boot_creates_catalog() {
        let pool = test_pool();

        let sb = Superblock::boot(&pool).await.unwrap();

        assert!(sb.validate().is_ok());
        assert_eq!(sb.sys_tables_page, PageId::new(1));
        assert_eq!(sb.sys_columns_page, PageId::new(2));
        assert_eq!(sb.sys_sequences_page, PageId::new(3));
        assert_eq!(sb.next_table_id, LAST_RESERVED_TABLE_ID + 1);
    }

    #[tokio::test]
    async fn test_boot_reads_existing_superblock() {
        let pool = test_pool();

        // First boot: bootstraps a new database.
        let sb = Superblock::boot(&pool).await.unwrap();

        // Second boot: loads the existing superblock.
        let sb2 = Superblock::boot(&pool).await.unwrap();

        assert_eq!(sb2.sys_tables_page, sb.sys_tables_page);
        assert_eq!(sb2.sys_columns_page, sb.sys_columns_page);
        assert_eq!(sb2.sys_sequences_page, sb.sys_sequences_page);
        assert_eq!(sb2.next_table_id, sb.next_table_id);
    }
}
