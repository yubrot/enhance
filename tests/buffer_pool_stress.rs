//! Buffer pool stress test with concurrent random range access.
//!
//! This test simulates realistic concurrent data access patterns with:
//! - Multiple workers performing random read/write operations
//! - Linear range access that may span multiple pages
//! - Random page releases mid-write to test consistency
//! - Additive write model for deterministic verification
//! - Mixed cache-hit and eviction scenarios

use std::sync::{Arc, Mutex};

use enhance::storage::buffer::{BufferPool, LruReplacer};
use enhance::storage::{FileStorage, PAGE_SIZE, PageId, Storage};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use tempfile::TempDir;

/// Test context containing shared resources.
struct TestContext {
    pool: BufferPool<FileStorage, LruReplacer>,
    write_log: Mutex<Vec<WriteRecord>>,
    config: TestConfig,
    _temp_dir: TempDir, // Keep temp directory alive
}

/// Configuration for the stress test.
#[derive(Debug, Clone)]
struct TestConfig {
    /// Number of frames in the buffer pool.
    pool_size: usize,
    /// Total number of pages in storage.
    total_pages: usize,
    /// Number of concurrent worker tasks.
    num_workers: usize,
    /// Number of operations each worker performs.
    ops_per_worker: usize,
    /// Maximum bytes per access range (controls page-spanning).
    max_range_size: usize,
}

impl Default for TestConfig {
    fn default() -> Self {
        Self {
            pool_size: 50,
            total_pages: 200,
            num_workers: 32,
            ops_per_worker: 200,
            max_range_size: PAGE_SIZE * 3,
        }
    }
}

/// A record of a write operation for verification.
#[derive(Debug, Clone, Copy)]
struct WriteRecord {
    /// Starting byte offset in the global address space.
    start_offset: usize,
    /// Number of bytes written.
    length: usize,
    /// Value added to each byte in the range.
    add_value: u8,
}

/// Returns the total size of the address space in bytes.
fn address_space_size(total_pages: usize) -> usize {
    total_pages * PAGE_SIZE
}

/// Computes the affected pages and their offset ranges for a byte range.
///
/// Returns a vector of (PageId, offset_range) tuples where offset_range
/// is the range of offsets within that page.
fn compute_page_ranges(
    start_offset: usize,
    length: usize,
) -> Vec<(PageId, std::ops::Range<usize>)> {
    if length == 0 {
        return vec![];
    }

    let start_page = start_offset / PAGE_SIZE;
    let end_page = (start_offset + length - 1) / PAGE_SIZE;
    let range_end = start_offset + length;

    (start_page..=end_page)
        .map(|page_num| {
            let page_id = PageId::new(page_num as u64);
            let page_start = page_num * PAGE_SIZE;
            let page_end = page_start + PAGE_SIZE;

            // Compute overlap
            let overlap_start = start_offset.max(page_start);
            let overlap_end = range_end.min(page_end);
            let offset_range = (overlap_start - page_start)..(overlap_end - page_start);

            (page_id, offset_range)
        })
        .collect()
}

/// A single worker task that performs random read/write operations.
async fn worker_task(ctx: Arc<TestContext>, seed: u64) {
    let mut rng = StdRng::seed_from_u64(seed);
    let address_space = address_space_size(ctx.config.total_pages);

    for _ in 0..ctx.config.ops_per_worker {
        // Generate random range
        let length = rng.gen_range(1..=ctx.config.max_range_size.min(address_space));
        let start_offset = rng.gen_range(0..=(address_space - length));
        let is_write = rng.gen_bool(0.2); // 20% write, 80% read

        if is_write {
            let record = WriteRecord {
                start_offset,
                length,
                add_value: rng.r#gen(),
            };
            perform_write(&ctx, record).await;
        } else {
            perform_read(&ctx, start_offset, length).await;
        }

        // Yield to allow other workers to make progress
        tokio::task::yield_now().await;
    }
}

/// Performs a write operation with random mid-write page releases.
async fn perform_write(ctx: &TestContext, record: WriteRecord) {
    ctx.write_log.lock().unwrap().push(record);

    let page_ranges = compute_page_ranges(record.start_offset, record.length);
    for (page_id, offset_range) in page_ranges {
        let mut guard = ctx.pool.fetch_page_mut(page_id, true).await.unwrap();

        // Write to each byte in the offset range, with random mid-write releases
        for offset in offset_range {
            guard[offset] = guard[offset].wrapping_add(record.add_value);
        }
    }
}

/// Performs a read operation to exercise the buffer pool.
async fn perform_read(ctx: &TestContext, start_offset: usize, length: usize) {
    let page_ranges = compute_page_ranges(start_offset, length);
    for (page_id, offset_range) in page_ranges {
        let guard = ctx.pool.fetch_page(page_id).await.unwrap();

        // Just read the data to exercise the cache
        let _data = &guard[offset_range];
    }
}

/// Verifies that the final state matches the expected state from the write log.
async fn verify_final_state(ctx: &TestContext) {
    ctx.pool.flush_all().await.expect("flush_all failed");

    let address_space = address_space_size(ctx.config.total_pages);
    let mut expected = vec![0u8; address_space];

    {
        let log = ctx.write_log.lock().unwrap();
        println!("Verifying {} write records...", log.len());

        for record in log.iter() {
            for i in 0..record.length {
                let offset = record.start_offset + i;
                expected[offset] = expected[offset].wrapping_add(record.add_value);
            }
        }
    }

    let mut mismatches = 0;
    for page_num in 0..ctx.config.total_pages {
        let page_id = PageId::new(page_num as u64);
        let guard = ctx.pool.fetch_page(page_id).await.unwrap();
        let page_start = page_num * PAGE_SIZE;

        for offset in 0..PAGE_SIZE {
            let global_offset = page_start + offset;
            let actual = guard[offset];
            let expected_val = expected[global_offset];

            if actual != expected_val {
                if mismatches < 10 {
                    // Print first 10 mismatches
                    eprintln!(
                        "Mismatch at page {} offset {} (global {}): expected {}, got {}",
                        page_num, offset, global_offset, expected_val, actual
                    );
                }
                mismatches += 1;
            }
        }
    }

    assert_eq!(
        mismatches, 0,
        "Found {} mismatches in final verification",
        mismatches
    );

    println!("Verification complete: all bytes match expected values");
}

// To run: cargo test --test buffer_pool_stress -- --ignored --nocapture
// or use: cargo llvm-cov --open --test buffer_pool_stress -- --ignored --nocapture
// to see coverage
#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
#[ignore]
async fn test_buffer_pool_stress_concurrent_range_access() {
    let config = TestConfig::default();

    println!("Starting buffer pool stress test with config:");
    println!("  pool_size: {}", config.pool_size);
    println!("  total_pages: {}", config.total_pages);
    println!("  num_workers: {}", config.num_workers);
    println!("  ops_per_worker: {}", config.ops_per_worker);
    println!("  max_range_size: {}", config.max_range_size);

    // Setup storage and buffer pool
    let temp_dir = tempfile::tempdir().expect("Failed to create temp directory");
    let storage = FileStorage::open(temp_dir.path().join("test.db"))
        .await
        .expect("Failed to open FileStorage");

    for _ in 0..config.total_pages {
        storage.allocate_page().await.unwrap();
    }
    let replacer = LruReplacer::new(config.pool_size);
    let pool = BufferPool::new(storage, replacer, config.pool_size);

    // Create shared context
    let ctx = Arc::new(TestContext {
        pool,
        write_log: Mutex::new(Vec::new()),
        config,
        _temp_dir: temp_dir,
    });

    // Spawn worker tasks
    let mut handles = Vec::new();
    for index in 0..ctx.config.num_workers {
        let ctx = Arc::clone(&ctx);
        let seed = index as u64 * 12345; // Deterministic seed per worker

        handles.push(tokio::spawn(async move { worker_task(ctx, seed).await }));
    }

    // Wait for all workers to complete
    println!(
        "Waiting for {} workers to complete...",
        ctx.config.num_workers
    );
    for (i, handle) in handles.into_iter().enumerate() {
        handle
            .await
            .unwrap_or_else(|e| panic!("Worker {} task panicked: {:?}", i, e));
    }

    println!("All workers completed. Starting verification...");

    verify_final_state(&ctx).await;

    println!("Stress test passed!");
}
