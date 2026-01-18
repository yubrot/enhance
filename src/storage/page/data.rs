//! Page-aligned memory allocation for storage layer.

use std::alloc::{Layout, alloc, dealloc};
use std::ptr::NonNull;

use super::PAGE_SIZE;

/// OS page size for alignment (4KB is typical for x86_64).
///
/// This is the typical page size used by modern operating systems.
/// Aligning to this boundary provides:
/// - Better cache line efficiency
/// - Compatibility with Direct I/O requirements
/// - Reduced false sharing in concurrent scenarios
const OS_PAGE_ALIGNMENT: usize = 4096;

/// Page-aligned memory allocation.
///
/// Allocates exactly `PAGE_SIZE` (8KB) bytes aligned to OS page boundaries
/// (4KB). This provides better performance characteristics than standard
/// heap allocation for page-based storage systems.
///
/// The memory is zero-initialized on allocation.
///
/// # Memory Layout
///
/// ```text
/// Address: 0x...000   (aligned to 4KB boundary)
/// Size:    8192 bytes (PAGE_SIZE)
/// ```
///
/// # Safety
///
/// This type uses `std::alloc` directly and maintains the following invariants:
/// - `ptr` is always valid and properly aligned
/// - Memory is allocated for exactly `PAGE_SIZE` bytes
/// - Memory is deallocated exactly once in `Drop`
pub struct PageData {
    ptr: NonNull<u8>,
    layout: Layout,
}

impl Default for PageData {
    fn default() -> Self {
        Self::new()
    }
}

impl PageData {
    /// Creates a new page-aligned allocation, zero-initialized.
    ///
    /// # Panics
    ///
    /// Panics if allocation fails (out of memory).
    pub fn new() -> Self {
        let layout = Layout::from_size_align(PAGE_SIZE, OS_PAGE_ALIGNMENT)
            .expect("PAGE_SIZE and OS_PAGE_ALIGNMENT should be valid");

        // SAFETY: layout is valid (non-zero size, valid alignment)
        let ptr = unsafe { alloc(layout) };
        let ptr = NonNull::new(ptr).expect("allocation failed");

        // Zero-initialize the memory
        // SAFETY: ptr is valid for PAGE_SIZE bytes
        unsafe {
            std::ptr::write_bytes(ptr.as_ptr(), 0, PAGE_SIZE);
        }

        Self { ptr, layout }
    }

    /// Returns a slice to the underlying memory.
    pub fn as_slice(&self) -> &[u8] {
        // SAFETY: ptr is valid for layout.size() bytes
        unsafe { std::slice::from_raw_parts(self.ptr.as_ptr(), self.layout.size()) }
    }

    /// Returns a mutable slice to the underlying memory.
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        // SAFETY: ptr is valid for layout.size() bytes
        unsafe { std::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.layout.size()) }
    }
}

impl Drop for PageData {
    fn drop(&mut self) {
        // SAFETY: ptr and layout match the values used in alloc()
        unsafe {
            dealloc(self.ptr.as_ptr(), self.layout);
        }
    }
}

// PageData is Send because it owns its allocation
unsafe impl Send for PageData {}
// PageData is Sync because access is exclusive (through &mut or Mutex)
unsafe impl Sync for PageData {}

impl AsRef<[u8]> for PageData {
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl AsMut<[u8]> for PageData {
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_mut_slice()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_page_data_allocation() {
        let page = PageData::new();
        assert_eq!(page.as_slice().len(), PAGE_SIZE);
    }

    #[test]
    fn test_page_data_zero_initialized() {
        let page = PageData::new();
        assert!(page.as_slice().iter().all(|&b| b == 0));
    }

    #[test]
    fn test_page_data_alignment() {
        let page = PageData::new();
        let addr = page.ptr.as_ptr() as usize;
        // Check that address is aligned to 4KB boundary
        assert_eq!(addr % OS_PAGE_ALIGNMENT, 0);
    }

    #[test]
    fn test_page_data_write_and_read() {
        let mut page = PageData::new();
        let slice = page.as_mut_slice();
        slice[0] = 42;
        slice[100] = 99;

        assert_eq!(page.as_slice()[0], 42);
        assert_eq!(page.as_slice()[100], 99);
        assert_eq!(page.as_slice()[1], 0);
    }
}
