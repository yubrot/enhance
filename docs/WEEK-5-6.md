# Week 5-6: Storage Layer

> Define the Storage trait. Implement MemoryStorage and FileStorage for 8KB page I/O.

# This Week I Learned

## Design Decisions

These decisions shape how the storage layer integrates with the Buffer Pool Manager (Week 7-8) and beyond.

### Caller-Owned Buffers

The `Storage` trait does **raw byte I/O only**. The caller provides the buffer (`&mut [u8]` or `&[u8]`), and Storage reads or writes exactly 8KB.

Notably, each `read_page()` or `write_page()` call goes directly to the underlying storage.

**Rationale**: Memory allocation, caching, and buffer lifetime management are explicitly the caller's responsibility. This keeps `Storage` focused solely on I/O operations. The Buffer Pool Manager (Week 7-8) will manage page caching and eviction.

### Async-First

All trait methods return futures using Rust 1.75+ native `async fn` in traits.

**Design Context**: RDBMS implementations face a fundamental concurrency challenge - handling multiple client connections while managing shared resources (buffer pool, locks, disk I/O). There are several established approaches:

| Concurrency Model          | Examples                   | Strengths                                                       | Weaknesses                                                  |
| -------------------------- | -------------------------- | --------------------------------------------------------------- | ----------------------------------------------------------- |
| **Process-per-connection** | PostgreSQL (traditional)   | Full isolation, crash safety                                    | High memory overhead, slow context switching                |
| **Thread-per-connection**  | MySQL (traditional)        | Lighter than processes, shared memory                           | Doesn't scale with many connections, context switching cost |
| **Thread pool**            | Modern PostgreSQL, MariaDB | Bounded resource usage, better scalability                      | Complex work stealing, still limited by thread count        |
| **Async/Event-driven**     | ScyllaDB, Redis            | Handle many connections with few threads, efficient I/O waiting | Complex async programming, harder debugging                 |

Our approach corresponds to the **Async/Event-driven** model, but leverages Rust's safety guarantees and tokio's ecosystem.

**Notable characteristics of Async Rust + tokio**:

1. **Compile-time state machines**: Futures compile to state machines at compile time with no heap allocations per async call. Callback-based systems (Node.js, libuv) use dynamic dispatch; async/await is zero-cost in Rust.
2. **Compile-time `Send + Sync` checking**: The compiler prevents holding non-Send values (e.g., `Rc<T>`) across `.await` points. This is enforced at compile time, unlike runtime checks in Go or dynamic languages.
3. **Uniform async/await syntax**: TCP listener, query parser, buffer pool, and disk I/O all use `async fn` and `.await`. Python's asyncio requires mixing blocking I/O threads with async runtime; Rust doesn't.
4. **Strongly-typed futures**: `Future<Output = Result<T, E>>` encodes return types in the type system. C-based async systems (libuv callbacks) often use void pointers; Rust futures are fully type-checked.
5. **Integrated ecosystem**: `tokio::fs::File`, `tokio::net::TcpListener`, and async traits work together without adapters. No bridging layer needed between different async primitives.

**Trade-offs**: Async Rust has a steeper learning curve. Lifetime management across `.await` and debugging async stack traces require familiarity with the model. For this learning-focused project, these challenges provide insight into modern concurrency patterns.

# Looking Forward

## Buffer Pool Manager Integration

The `Storage` trait is designed for integration with the Buffer Pool Manager (Week 7-8).

```
┌─────────────────────────────┐
│ Buffer Pool Manager         │  ← Week 7-8
│ - fetch_page(PageId)        │
│ - unpin_page(PageId)        │
│ - LRU eviction              │
│ - Arc<RwLock<Page>>         │
└───────────┬─────────────────┘
            │ read_page / write_page
            │ (on cache miss / eviction)
            v
┌─────────────────────────────┐
│ Storage Trait               │  ← Week 5-6 (this)
│ - No caching                │
│ - Raw 8KB I/O               │
└───────────┬─────────────────┘
            v
      MemoryStorage / FileStorage
```

- **Week 7-8: Buffer Pool Manager** will:
  - Call `storage.read_page()` on cache miss
  - Call `storage.write_page()` when evicting dirty pages
  - Maintain page-level locks (`Arc<RwLock<Page>>`) for concurrency control
  - Implement LRU eviction policy
- **Week 9: Slotted Page Structure** will use `Storage` (via BPM) to persist variable-length records within 8KB pages.
- **Week 21: Write-Ahead Log (WAL)** relies on `sync_all()` to ensure durability: logs must be flushed to disk before data pages.

## Production Readiness Gaps

The current implementation prioritizes learning and clarity. For production use, consider:

- **Graceful shutdown**: Flush all dirty pages and sync before exit
- **Corruption recovery**: Checksum validation (e.g., CRC32) for page integrity
- **I/O error handling**: Retry logic for transient failures
- **Resource limits**: Maximum file size, memory limits
- **Multiple files**: Support for tablespaces, indexes in separate files
- **Direct I/O**: Bypass OS page cache for more control (e.g., `O_DIRECT` on Linux)
- **Concurrent file handles**: One handle per thread for parallel I/O (pread/pwrite)
- **Monitoring**: I/O metrics (read/write latency, throughput, cache hit rate)
