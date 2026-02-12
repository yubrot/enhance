# Implementation Difficulty Assessment

This document evaluates remaining roadmap items from the perspective of Agentic Coding, based on experience from the first three months of development.

**Key observation**: Latch hierarchy and concurrency control (difficulty 5) proved challenging for Agentic Coding, while knowledge-based implementations following clear specifications (difficulty 2-3) were completed quickly.

## Difficulty Ratings (1-5)

| # | Item | Difficulty | Rationale |
|---|------|:----------:|-----------|
| 12 | **Sort & Aggregation** | 2 | Standard algorithms. In-memory sort is simple. Aggregate functions are well-defined |
| 13 | **Write-Ahead Log** | 4 | CLOG (persistent TxState) as prerequisite sub-step, then WAL log records + write-ahead principle. Coordination with Buffer Pool. fsync timing |
| 14 | **Checkpoint & Recovery** | **5** | Dirty page concurrency during checkpoint. Correct REDO replay ordering. Crash recovery testing is difficult |
| 15 | **VACUUM & FSM** | 3 | Depends on visibility rules but extends existing compaction. FSM is an independent structure |
| 16 | **B+Tree Index** | **5** | Correct latch coupling (crabbing) implementation. Concurrency during node splits. Integration with Buffer Pool latch hierarchy |
| 17 | **IndexScan, Planner & Constraints** | 3 | Traversal is simple if B+Tree is correct. Rule-based planner is condition matching |
| 18 | **HOT** | 3 | Same-page chain management. Logic for skipping index updates |
| 19 | **Nested Loop Join** | 2 | Simple algorithm. Fits naturally into Volcano model |
| 20 | **Row-Level Lock** | **5** | Wait queue management. Deadlock detection (wait-for graph). Interaction between xmax-based locking and MVCC visibility |

## Step 13 Sub-steps

Step 13 (WAL) involves two distinct subsystems that should be implemented in order:

1. **CLOG (Commit Log)**: Persistent `TxId → TxState` map replacing the volatile `tx_states` HashMap in `TransactionManager`. This is a prerequisite for WAL because:
   - WAL REDO replay updates CLOG entries during recovery
   - Without CLOG, restarted servers lose all transaction state, making aborted transactions appear committed
   - Consumers: `Snapshot::is_inserted()` and `Snapshot::is_deleted()` call `TransactionManager::state()` when hint bits are unset
2. **WAL log records + buffer**: Define log record types (INSERT/UPDATE/DELETE/COMMIT), implement WAL buffer, enforce write-ahead principle (log before data page flush), fsync discipline
3. **Heap integration**: Modify heap write operations (`heap::insert`, `heap::delete`, `heap::update`) to emit WAL records before modifying data pages

CLOG alone does NOT provide crash consistency (data pages may be unflushed), so all three sub-steps must be completed before the system is durable. However, implementing CLOG first isolates the simpler persistence concern from the more complex WAL machinery.

## Pattern Analysis

### Difficulty 5 (Requires Caution): Concurrency Control is the Core Challenge

- **14. Checkpoint & Recovery**: Page modification during flush
- **16. B+Tree Index**: Correct latch acquire/release ordering in crabbing
- **20. Row-Level Lock**: Wait-for graph construction and deadlock detection

**Common pattern**: State transitions interleave across multiple tasks. Agentic Coding handles single logical flows well but struggles with reasoning about mutual dependencies ("A waits for B, B waits for C...").

### Difficulty 2 (Strength): Pattern Implementation with Clear Specifications

- **7. Parser**: Grammar rules → code transformation
- **10. Executor**: Iterator trait implementation
- **12. Aggregation**: Well-defined COUNT/SUM/AVG etc.
- **19. Nested Loop Join**: Textbook algorithm

## Recommended Approach by Difficulty

| Difficulty | Strategy |
|:----------:|----------|
| 2-3 | Let AI implement in one pass, verify with tests |
| 4 | Fix design first, review in small increments |
| 5 | **Human confirms logic at pseudocode level** → AI translates to code. Focus on concurrency testing |

For B+Tree (16) and Row-Level Lock (20) in particular, explicitly documenting latch/lock acquisition order in diagrams or step-by-step descriptions before coding will reduce rework.
