# enhance: A From-Scratch RDBMS Implementation

enhance is a relational database management system (RDBMS) built from the ground up in Rust. The primary goal of this project is to bridge the gap between being a high-level database user and understanding the "magic" that happens beneath the surface of systems like PostgreSQL.

This project is designed as a 6-month intensive learning journey, focusing on core database internals, asynchronous systems, and low-level memory management.

## Project Vision & Philosophy

- **Minimal Dependencies**: Rely on Tokio for the async runtime and a few essential crates. Avoid large frameworks to focus on manual implementation of core logic.
- **PostgreSQL Compatibility**: Implement the wire protocol manually so that standard tools like `psql` can connect to the database.
- **Concurrency First**: Implement page-level locking and asynchronous I/O from the start to fully utilize Rust’s safety and performance.
- **Transparency**: Every layer—from the byte-level storage to the SQL parser—is handwritten to ensure deep understanding.

### Architectural Decisions

| Component           | Decision                      | Rationale                                                                                 |
| ------------------- | ----------------------------- | ----------------------------------------------------------------------------------------- |
| Language & Runtime  | Rust + Tokio (Async)          | Deep dive into async Rust; suitable for handling concurrent database sessions.            |
| Protocol            | PostgreSQL v3.0 (Handwritten) | Support for Extended Query Protocol (Parse/Bind/Execute) to work with modern drivers.     |
| Storage Unit        | 8KB Fixed-size Pages          | Aligns with OS page sizes and PostgreSQL standards for efficient I/O.                     |
| Storage Abstraction | Trait-based                   | Allows seamless switching between MemoryStorage and FileStorage (Disk).                   |
| Concurrency Control | Page-level Latching           | High concurrency using Arc<RwLock<Page>>. Requires strict latch hierarchy.                |
| Data Layout         | Slotted Page Structure        | Efficiently manages variable-length records within fixed 8KB pages.                       |
| Parser              | Handwritten Recursive Descent | Deep learning of SQL-92 grammar without using parser generators.                          |
| Execution Model     | Volcano Model                 | Standard iterator-based processing; composable and intuitive for single-query efficiency. |

### Technical Constraints & Guardrails

- **Deadlock Prevention**: Since we use page-level locking, a strict Latch Hierarchy must be followed. Locks must always be acquired in a predetermined order (e.g., by Page ID) to avoid circular waits.
- **System Catalog "Faking"**: Tools like `psql` query `pg_catalog` extensively upon connection. We will implement "dummy" responses for these system queries initially to maintain compatibility without over-engineering metadata.
- **Async/Blocking I/O**: Standard file I/O is blocking. We will use `tokio::fs` and carefully manage the transition between async code and disk operations to avoid stalling the executor.

## 6-Month Detailed Roadmap (24 Weeks)

### Month 1: Networking & Extended Protocol Foundation

Goal: Connect via `psql` and handle the stateful Parse/Bind/Execute flow.

- ✅ Week 1: TCP Server & Handshake: Implement Tokio listener. Handle StartupMessage (Big Endian) and SSLRequest. Achieve a "Trust" authentication state.
- ✅ Week 2: Simple Query Protocol: Handle the 'Q' message. Implement the basic loop to return CommandComplete.
- ✅ Week 3-4: Extended Query Protocol (Parse/Bind/Execute): Implement stateful storage for PreparedStatement and Portal concept. Handle the complete flow from Parse, Describe, Bind, to Execute messages.

### Month 2: Concurrent Storage Engine

Goal: Manage 8KB pages safely across threads with disk persistence.

- ✅ Week 5-6: Storage Trait & Implementations: Define the Storage trait. Implement memory-backed and file-backed storage for 8KB page I/O.
- ✅ Week 7-8: Buffer Pool & LRU Policy: Implement fetch_page, unpin_page, and LRU eviction. Map PageId to memory Frames. Design latch hierarchy to ensure deadlock-free operation.

### Month 3: Data Layout & Serialization

Goal: Manage variable-length records within the 8KB limit.

- ✅ Week 9-11: Slotted Page & Record Management: Implement the slotted page structure (header and slot array), binary serialization for records, and CRUD operations (Insert, Delete, Update) with free space reclamation.
- Week 12: Minimal System Catalog: Implement a way to persist table definitions (schema) in a reserved page (e.g., Page 0).

### Month 4: SQL Parsing & Execution Engine

Goal: Turn SQL strings into a stream of rows using the Volcano Model.

- Week 13: Lexical Analyzer (Lexer): Tokenize SQL strings.
- Week 14: Recursive Descent Parser: Support CREATE TABLE, INSERT, and SELECT (FROM/WHERE). Output an Abstract Syntax Tree (AST).
- Week 15: Volcano Executor Interface: Define the Executor trait with a next() method. Implement SeqScan.
- Week 16: Filter & Projection: Implement operators for the WHERE clause and column selection.

### Month 5: Advanced Operators & Indexing

Goal: Support table JOINS and speed up lookups with B+Trees.

- Week 17: Join Syntax & Planning: Extend the parser and AST to handle multiple table references.
- Week 18: Nested Loop Join: Implement the first join operator (iterating the inner table for every row of the outer).
- Week 19: B+Tree Physical Layout: Design internal and leaf node structures as 8KB pages.
- Week 20: B+Tree Logic (Search/Insert): Implement node splitting and the IndexScan operator.

### Month 6: Transactions (ACID) & Final Polish

Goal: Ensure reliability through WAL and measure performance.

- Week 21: Write-Ahead Log (WAL): Implement log records and the fsync dance (log before data).
- Week 22: Transaction Manager: Manage TransactionID and states (Running/Committed/Aborted).
- Week 23: Crash Recovery: Implement the REDO logic to replay the WAL on startup.
- Week 24: Benchmarking & Finalization: Run performance tests. Compare indexed vs. non-indexed scans. Celebrate.

## Development Methodology

This project is built using an AI-Driven, Understanding-First approach.

- AI as Driver: The AI generates implementation code based on specific architectural requirements.
- User as Navigator: I review every line, ensure it adheres to the ADR, and verify the memory/concurrency safety.
- Iteration: Use `psql` and unit tests at every week's end to verify the "Vertical Slice" of the system.

## Production Readiness

This project is designed for learning and experimentation, not production use. Throughout the codebase, inline `NOTE:` comments document what would be necessary to make each component production-ready (e.g., graceful shutdown, connection limiting, proper authentication, input validation). These comments serve as a roadmap for future hardening while keeping the learning-focused implementation minimal and understandable.
