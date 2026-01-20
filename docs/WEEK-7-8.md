# Week 7-8: Buffer Pool & LRU Policy

> Implement fetch_page, unpin_page, and LRU eviction. Map PageId to memory Frames. Design latch hierarchy to ensure deadlock-free operation.

# This Week I Learned

## Buffer Pool Design

The buffer pool caches up to `pool_size` pages from a potentially vast Storage as **frames** in memory.

Frames share a pre-allocated fixed-size memory region. A frame holding a page can be **evicted** and reassigned to a different page. However, the **Pin/Unpin** mechanism prevents frames currently in use (pin_count > 0) from being evicted.

Frame contents are written back to Storage at these times:

- When `flush_page` is explicitly called
- During eviction (only if the dirty flag is set)

### Callers Must Mark the Dirty Flag

Frames have a dirty flag, and marking it to indicate modifications is **the caller's responsibility**. Reasons why the Buffer Pool doesn't auto-detect changes:

1. **Performance**: Detecting changes across all bytes is expensive (requires comparing entire page size)
2. **Explicit intent**: Only the caller knows whether a change should be persisted
3. **Optimization opportunity**: Allows avoiding write-back for read-only access or when discarding temporary changes

This is a common design pattern in DBMSs; PostgreSQL and MySQL take the same approach.

### Replacer Trait

Victim frame selection for eviction is delegated to the `Replacer` trait. This implementation uses a simple LRU (Least Recently Used) algorithm for learning purposes.

LRU is simple to implement and has predictable behavior. More sophisticated policies (Clock, 2Q, ARC, etc.) can be introduced by swapping the trait implementation. In practice, PostgreSQL uses Clock-Sweep (an NFU variant optimized for fine-grained locking), while MySQL InnoDB uses a modified LRU with midpoint insertion.

### Separation of Frame Data and Metadata

The buffer pool separates frame data from metadata with different lock types:

```
frames: Vec<RwLock<PageData>>     -- Async RwLock (tokio)
state: Mutex<BufferPoolState<R>>  -- Sync Mutex (std)
```

**State Mutex protects**: `page_table`, `frame_metadata`, `free_list`, `replacer`

This design simultaneously satisfies three constraints:

**1. Maximizing Concurrency**

If frame data and metadata were protected by a single lock, accessing one page would block all other page accesses. Separation enables:

- Concurrent access to different pages
- Multiple readers on the same page (RwLock)
- Minimal state lock contention since metadata operations complete quickly

**2. Deadlock Prevention via Latch Ordering**

With two independent locks, acquisition order matters. Drop and flush operations need to acquire the state lock while holding a frame lock:

```rust
// flush: clear dirty flag after writing data
let data_guard = self.frames[frame_id].read().await;  // Frame lock
// ... write_page ...
let mut state = self.state.lock();  // State lock (Frame → State)
state.frame_metadata[frame_id].is_dirty = false;
```

If the reverse order (State → Frame) were also allowed, circular waits would occur. Therefore, only "Frame → State" ordering is permitted.

**3. Enabling Synchronous Drop**

Rust has no async drop. The unpin operation when guards are dropped must execute synchronously:

```rust
impl Drop for PageReadGuard<'_, S, R> {
    fn drop(&mut self) {
        self.inner.release(self.frame_id, false);  // Called synchronously
    }
}
```

Using `std::sync::Mutex` allows synchronous state lock acquisition within Drop. `tokio::sync::Mutex` would require `.await`, which cannot be used in Drop.

#### Data-PageId Consistency as a Consequence

Since Frame lock and State lock are independent, it might seem dangerous that "a frame could be reassigned to a different page while reading its data." However, the following invariant prevents this:

**Invariant**: While holding a frame's read/write lock, the frame's `page_id` may become `None`, but **cannot change to a different page ID**.

**Reason**: Loading a new page into a frame requires the frame's **write lock** (`complete_read` updates `page_table` only after acquiring write lock). Therefore, data is safe as long as you hold the read lock.

```rust
// In acquire: always acquire write lock when loading a new page
let mut data = self.frames[new_frame_id].write().await;
self.storage.read_page(page_id, data.as_mut_slice()).await
```

The flush operation verifies `page_id` before and after the write to handle concurrent eviction correctly—ensuring dirty flags aren't cleared for the wrong page.

#### Multi-Page Lock Ordering

When acquiring multiple pages simultaneously (e.g., for JOIN operations), locks must be acquired in **ascending PageId order**.

```rust
// ✅ Correct: ascending PageId order
let page_1 = bpm.fetch_page(PageId::new(1)).await?;
let page_5 = bpm.fetch_page(PageId::new(5)).await?;

// ❌ Wrong: potential deadlock
let page_5 = bpm.fetch_page(PageId::new(5)).await?;
let page_1 = bpm.fetch_page(PageId::new(1)).await?;
```

The Buffer Pool cannot know which pages will be acquired together. Only higher layers have this information, so ordering guarantees are delegated to callers. For B-tree indexes, production RDBMSs use "latch crabbing" (top-down acquisition with early release of safe nodes) to allow high concurrency while preventing deadlocks.

### Page Guards: RAII Pattern for Safe Access

Guards provide type-safe access to page data and ensure automatic unpinning when dropped.

```rust
// Read-only access (shared lock)
pub struct PageReadGuard<'a, S: Storage, R: Replacer> { ... }

// Mutable access (exclusive lock)
pub struct PageWriteGuard<'a, S: Storage, R: Replacer> { ... }
```

**Benefits:**

1. **Memory safety**: Rust's borrow checker prevents use-after-free and data races
2. **Automatic cleanup**: Guards unpin pages on drop (even during panics)
3. **Convenient API**: Implements `Deref`/`DerefMut` for direct slice access

## Cancel Safety Considerations

**WARNING: This implementation is NOT cancel-safe.**

If a Future returned by buffer pool methods is dropped before completion (e.g., via `tokio::time::timeout`), internal state may become inconsistent:

- **Frame leaks**: Pin counts may not be decremented, causing frames to remain pinned indefinitely
- **Inconsistent metadata**: Page table or replacer state may become out of sync

**Mitigation:**

- Always await buffer pool operations to completion
- Do not use timeout operations that may cancel buffer pool Futures
- Ensure cleanup code completes before task cancellation

## Testing: Concurrent Stress Test

`tests/buffer_pool_stress.rs` validates correctness under concurrent load:

```rust
struct TestConfig {
    pool_size: 32,              // Frames in buffer pool
    total_pages: 100,           // Pages in storage (> pool_size)
    num_workers: 16,            // Concurrent tasks
    ops_per_worker: 500,        // Operations per task
    max_range_size: PAGE_SIZE * 3,  // Spans multiple pages
    page_release_probability: 0.03,  // Random mid-write releases
}
```

**Test Strategy:**

1. **Additive write model**: Each write adds a known value to bytes (allows verification)
2. **Random range access**: Read/write ranges may span multiple pages
3. **Mid-write releases**: Drop guards randomly during writes to test consistency
4. **Final verification**: Reconstruct expected state from write log and compare with actual storage

**Why this design?**

The key is `total_pages > pool_size` with high concurrency. This forces frequent evictions under contention, naturally triggering:

- **Write-back retries**: When a page is pinned during eviction write-back (`complete_write_back` returns `Retry`)
- **Read race conditions**: When multiple tasks load the same page simultaneously (`complete_read` handles "another thread won")

These edge cases are difficult to test deterministically but occur reliably under stress. Coverage reports confirm these code paths are exercised.

# Looking Forward

## Production Readiness Gaps

The current implementation prioritizes learning and clarity. For production use, consider:

### Performance Optimizations

- **parking_lot::Mutex**: Faster, no poisoning (but less debugging info)
- **Split state locks**: Separate locks for page_table and replacer to reduce contention
- **Lock-free page table**: Use concurrent hash maps for higher throughput
- **Page prefetching**: Predict sequential access patterns and load ahead
- **Background flusher**: Dedicated task to flush dirty pages asynchronously

### Monitoring & Metrics

- **Hit rate**: Cache hits / total accesses
- **Eviction count**: Pages evicted over time
- **Dirty page count**: Pages pending write-back
- **Pin count distribution**: Identify hot pages
- **I/O latency**: Read/write operation timings

### Resilience

- **Graceful shutdown**: Flush all dirty pages before exit
- **Page checksums**: Validate integrity on read (CRC32, xxHash)
- **I/O error recovery**: Retry transient failures, fail fast on corruption
- **Deadlock detection**: Monitor lock wait times, auto-abort on timeout

### Advanced Features

- **Multiple buffer pools**: Per-tablespace or per-index pools
- **Adaptive replacement**: Clock, 2Q, or ARC for better hit rates
- **Large page support**: Handle pages > 8KB for TOAST-like data
- **Direct I/O**: Bypass OS page cache for more control
- **NUMA awareness**: Allocate frames on local memory nodes
