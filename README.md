# enhance: A From-Scratch RDBMS Implementation

enhance is a relational database management system (RDBMS) built from the ground up in Rust. The primary goal of this project is to bridge the gap between being a high-level database user and understanding the "magic" that happens beneath the surface of systems like PostgreSQL.

This project is designed as an intensive learning journey, focusing on core database internals, asynchronous systems, and low-level memory management.

## Project Vision & Philosophy

- **Minimal Dependencies**: Rely on Tokio for the async runtime and a few essential crates. Avoid large frameworks to focus on manual implementation of core logic.
- **PostgreSQL Compatibility**: Implement the wire protocol manually so that standard tools like `psql` can connect to the database.
- **Concurrency First**: Implement page-level locking and asynchronous I/O from the start to fully utilize Rust’s safety and performance.
- **Transparency**: Every layer—from the byte-level storage to the SQL parser—is handwritten to ensure deep understanding.

### Architectural Decisions

| Component           | Decision                           | Rationale                                                                                 |
| ------------------- | ---------------------------------- | ----------------------------------------------------------------------------------------- |
| Language & Runtime  | Rust + Tokio (Async)               | Deep dive into async Rust; suitable for handling concurrent database sessions.            |
| Protocol            | PostgreSQL v3.0 (Handwritten)      | Support for Extended Query Protocol (Parse/Bind/Execute) to work with modern drivers.     |
| Storage Unit        | 8KB Fixed-size Pages               | Aligns with OS page sizes and PostgreSQL standards for efficient I/O.                     |
| Storage Abstraction | Trait-based                        | Allows seamless switching between MemoryStorage and FileStorage (Disk).                   |
| Concurrency Control | Page-level Latching                | High concurrency using Arc<RwLock<Page>>. Requires strict latch hierarchy.                |
| Transaction Model   | MVCC (Multi-Version)               | PostgreSQL-style xmin/xmax in tuple header. Readers never block writers.                  |
| Isolation Level     | READ COMMITTED only                | Snapshot per statement. REPEATABLE READ/SERIALIZABLE out of scope for simplicity.         |
| Row-Level Locking   | xmax-based with Deadlock Detection | FOR UPDATE/SHARE via tuple header. Wait-for graph for deadlock detection.                 |
| Data Layout         | Slotted Page Structure             | Efficiently manages variable-length records within fixed 8KB pages.                       |
| B+Tree Concurrency  | Latch Coupling (Crabbing)          | Acquire child latch before releasing parent. Enables concurrent tree traversal.           |
| System Catalog      | Self-hosted Heap Tables            | Catalog tables stored as regular heap tuples with MVCC. No "faking" approach.             |
| Parser              | Handwritten Recursive Descent      | Deep learning of SQL-92 grammar without using parser generators.                          |
| Query Planner       | Rule-based                         | Simple predicate matching for index selection. Cost-based optimization out of scope.      |
| Execution Model     | Volcano Model                      | Standard iterator-based processing; composable and intuitive for single-query efficiency. |
| Durability          | WAL + REDO Recovery                | Write-ahead logging with checkpoint. UNDO not needed due to MVCC design.                  |
| Storage Maintenance | VACUUM                             | Dead tuple cleanup essential for MVCC. Reclaims space within pages.                       |

### Technical Constraints & Guardrails

- **Latch Hierarchy**: Page-level latches must be acquired in a predetermined order (e.g., by Page ID) to prevent deadlocks. Row-level locks use wait-for graph for deadlock detection.
- **Catalog Bootstrap**: System catalog tables must be initialized before any user operations. Catalog schema is hardcoded at startup, then stored as regular tuples.
- **Async/Blocking I/O**: Standard file I/O is blocking. We will use `tokio::fs` and carefully manage the transition between async code and disk operations to avoid stalling the executor.
- **Error Handling in Transactions**: When a statement fails within a transaction, the transaction enters an aborted state and only accepts ROLLBACK. No partial rollback or SAVEPOINT support.

## Detailed Roadmap

### Month 1: Networking & Extended Protocol Foundation

Goal: Connect via `psql` and handle the stateful Parse/Bind/Execute flow.

1. ✅ TCP Server & Handshake: Implement Tokio listener. Handle StartupMessage (Big Endian) and SSLRequest. Achieve a "Trust" authentication state.
2. ✅ Simple Query Protocol: Handle the 'Q' message. Implement the basic loop to return CommandComplete.
3. ✅ Extended Query Protocol (Parse/Bind/Execute): Implement stateful storage for PreparedStatement and Portal concept. Handle the complete flow from Parse, Describe, Bind, to Execute messages.

### Month 2: Concurrent Storage Engine

Goal: Manage 8KB pages safely across threads with disk persistence.

4. ✅ Storage Trait & Implementations: Define the Storage trait. Implement memory-backed and file-backed storage for 8KB page I/O.
5. ✅ Buffer Pool & LRU Policy: Implement fetch_page, unpin_page, and LRU eviction. Map PageId to memory Frames. Design latch hierarchy to ensure deadlock-free operation.

### Month 3: Data Layout & Serialization & SQL Parsing

Goal: Manage variable-length records within the 8KB limit and parse SQL into AST.

6. ✅ Slotted Page & Record Management: Implement the slotted page structure (header and slot array), binary serialization for records, and CRUD operations (Insert, Delete, Update) with free space reclamation.
7. ✅ Lexer & Parser: Tokenize SQL strings. Implement recursive descent parser for CREATE TABLE, INSERT, SELECT, UPDATE, DELETE. Design AST structure.

### Month 4: MVCC Foundation

Goal: Establish MVCC infrastructure with transaction visibility and self-hosted catalog.

8. ✅ MVCC Core: Transaction manager (TxId allocation, active transaction tracking, commit/abort state machine), tuple header extension (xmin/xmax/cid/infomask), Snapshot structure, visibility rules (`HeapTupleSatisfiesMVCC`).
9. ✅ System Catalog: Store table/column definitions as heap tuples with MVCC. Bootstrap reserved catalog tables (pg_class, pg_attribute equivalent). Implement auto-increment sequences for SERIAL columns.

### Month 5: Query Execution

Goal: Execute queries with MVCC awareness.

10. ✅ Basic Executor & EXPLAIN: Implement Volcano trait (`next() -> Option<Tuple>`), SeqScan (heap iteration with visibility check), Filter (WHERE evaluation), Projection (column selection), and EXPLAIN output for plan visualization.
11. ✅ DML Operations: INSERT (set xmin), DELETE (set xmax), UPDATE (delete + insert as new version). Implement type coercion for mixed-type expressions.
12. Sort & Aggregation: ORDER BY with in-memory sort, GROUP BY, aggregate functions (COUNT, SUM, AVG, MIN, MAX).

### Month 6: Durability

Goal: Crash recovery and storage maintenance.

13. Write-Ahead Log: Log record types (INSERT/UPDATE/DELETE/COMMIT), WAL buffer management, write-ahead principle enforcement, fsync discipline.
14. Checkpoint & Recovery: Dirty page tracking in buffer pool, checkpoint record writing, flush policy, REDO replay sequence on startup.
15. VACUUM & FSM: Dead tuple identification via visibility rules, space reclamation within pages. Implement Free Space Map (FSM) as a separate structure tracking available space per heap page, enabling efficient page selection for INSERT operations.

### Month 7: Indexing & Advanced Features

Goal: Fast lookups, multi-table queries, and fine-grained concurrency.

16. B+Tree Index: Internal/leaf node layout as 8KB pages, search algorithm, insert with node splitting.
17. IndexScan, Planner & Constraints: Index traversal with visibility check. Simple rule-based planner for SeqScan vs IndexScan selection. Implement PRIMARY KEY and UNIQUE constraints using B+Tree index for uniqueness validation during INSERT/UPDATE.
18. HOT (Heap-Only Tuples): Same-page UPDATE chains to avoid unnecessary index updates.
19. Nested Loop Join: Iterate inner table for each outer row. Support equi-join predicates.
20. Row-Level Lock: FOR UPDATE/FOR SHARE via xmax-based locking, wait queue for lock conflicts, deadlock detection (wait-for graph).

## Development Methodology

This project is built using an AI-Driven, Understanding-First approach.

- AI as Driver: The AI generates implementation code based on specific architectural requirements.
- User as Navigator: I review every line, ensure it adheres to the ADR, and verify the memory/concurrency safety.
- Iteration: Use `psql` and unit tests at every week's end to verify the "Vertical Slice" of the system.

## Production Readiness

This project is designed for learning and experimentation, not production use. Throughout the codebase, inline `NOTE:` comments document what would be necessary to make each component production-ready (e.g., graceful shutdown, connection limiting, proper authentication, input validation). These comments serve as a roadmap for future hardening while keeping the learning-focused implementation minimal and understandable.
