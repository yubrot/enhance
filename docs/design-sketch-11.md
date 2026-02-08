# Design Sketch: Step 11 — DML Operations

> INSERT (set xmin), DELETE (set xmax), UPDATE (delete + insert as new version). Implement type coercion for mixed-type expressions.

## Type Glossary

| Type | Module | Purpose |
| --- | --- | --- |
| `HeapWriter` | `heap/writer.rs` | Multi-page tuple insertion: walks page chain, allocates new pages, inserts tuples |
| `HeapScanner` | `heap/scanner.rs` | Multi-page tuple scanning: walks page chain, yields `(TupleId, TupleHeader, Record)` |
| `Plan::Insert` | `executor/plan.rs` | Logical plan for INSERT: target table metadata + bound value expressions |
| `Plan::Update` | `executor/plan.rs` | Logical plan for UPDATE: child scan plan + bound assignment expressions |
| `Plan::Delete` | `executor/plan.rs` | Logical plan for DELETE: child scan plan |
| `InsertNode` | `executor/node.rs` | Physical INSERT executor: evaluates values, inserts tuples via ExecContext |
| `UpdateNode` | `executor/node.rs` | Physical UPDATE executor: scans target rows, deletes old + inserts new version |
| `DeleteNode` | `executor/node.rs` | Physical DELETE executor: scans target rows, marks xmax |

### Naming Decisions

- "tuple" vs "row": unchanged from Step 10 — "tuple" = on-disk (TupleHeader + Record), "row" = in-executor logical unit (`Row`)
- "page chain": singly-linked list of heap pages via `HeapPage`-specific `next_page` field. Each table has a `first_page`; subsequent pages are linked
- "HeapWriter" vs "HeapPage": `HeapPage` operates on a single page; `HeapWriter` manages the multi-page chain for insertion
- "HeapScanner" vs "SeqScan": `HeapScanner` is heap-level (walks pages, yields raw tuples); `SeqScan` is executor-level (Volcano node wrapping `HeapScanner`)
- "assignment": a single `SET column = expr` pair in UPDATE, bound to column index + `BoundExpr`
- "coerce": implicit type conversion from a value's runtime type to the target column type (via `Value::cast`)
- "affected rows": count returned by DML — INSERT returns total inserted, UPDATE/DELETE return total modified/deleted

## Page Layout: HeapPage-Specific Header

Page chain linkage is **not** in the general `PageHeader` — it is a heap-specific concern. `PageHeader` (24 bytes including 4 reserved bytes) remains unchanged, preserving its generality for future page types (B+tree, FSM, etc.).

Instead, `HeapPage` owns a 4-byte extra header area immediately after `PageHeader`:

```text
HeapPage layout:
+------------------+-------------------+------------------+---+------------------+
| PageHeader (24B) | HeapExtra (4B)    | Slot Array       |   | Tuple data       |
|                  | next_page: u32    | [0][1][2]...     |   | ...[2][1][0]     |
+------------------+-------------------+------------------+---+------------------+
  offset 0           offset 24           offset 28         ...   offset 8192
```

- `next_page: u32` — page number of the next page in the chain (0 = end of chain)
- `HEAP_EXTRA_SIZE = 4` — constant in `heap/page.rs`
- `SlottedPage` takes a `data_offset` parameter indicating where usable data starts (28 for heap pages, allowing future B+tree pages to specify their own offset)
- Max record size decreases by 4 bytes (8164B → 8160B) — negligible

### Rationale (vs. `PageHeader::next_page`)

| Concern | PageHeader approach | HeapExtra approach |
| --- | --- | --- |
| B+tree (Step 16) | Leaf pages need `left_sibling` + `right_sibling` — different semantics | B+tree uses its own `BTreeExtra` with 8+ bytes |
| PageHeader generality | `next_page` field semantics vary by page type — confusing | Each page type defines its own extra header |
| Reserved bytes | Consumed; no room for WAL/checksum expansion | Preserved for future WAL/checksum needs |
| Corruption resilience | Same — both are singly-linked | Same — WAL (Step 13) + checksums mitigate |

## Module Structure

### New Modules

- `src/heap/writer.rs` — Multi-page tuple insertion
  - `pub struct HeapWriter` — Walks page chain to find space, allocates new pages, inserts tuples
  - `pub async fn insert(pool, first_page, schema, record, xmin, cmin) -> Result<TupleId, HeapError>`
  - Handles page-full by walking to next page or allocating a new one
  - `pub async fn insert_on_page_or_after(pool, page_id, schema, record, xmin, cmin) -> Result<TupleId, HeapError>` — Same-page priority for UPDATE

- `src/heap/scanner.rs` — Multi-page tuple scanning
  - `pub struct HeapScanner` — Async iterator over page chain, yields `(TupleId, TupleHeader, Record)` per tuple
  - Used by both `ExecContext` (via `scan_table`) and `Catalog` (via `get_table`/`get_columns`)
  - Yields all tuples without MVCC filtering (caller applies visibility)

### Modified Modules

- `src/heap/page.rs` — Add HeapExtra header, parameterize SlottedPage data offset
  - `const HEAP_EXTRA_SIZE: usize = 4` — size of heap-specific header
  - `const HEAP_DATA_OFFSET: usize = PAGE_HEADER_SIZE + HEAP_EXTRA_SIZE` — slot array starts here
  - `pub fn next_page(&self) -> Option<PageId>` — reads next_page from HeapExtra
  - `pub fn set_next_page(&mut self, next: Option<PageId>)` — writes next_page to HeapExtra
  - `init()` — also zeroes HeapExtra (next_page = 0 = no next page)
  - `SlottedPage::new()` takes `data_offset` to know where slot array begins
  - `MAX_RECORD_SIZE` decreases by `HEAP_EXTRA_SIZE` (4 bytes)

- `src/heap.rs` — Re-export new modules
  - `pub use writer::HeapWriter`
  - `pub use scanner::HeapScanner`

- `src/catalog/core.rs` — Replace direct `HeapPage::insert/scan` with `HeapWriter/HeapScanner`
  - `get_table()` — use `HeapScanner` instead of single-page `HeapPage::scan`
  - `get_columns()` — use `HeapScanner` instead of single-page `HeapPage::scan`
  - `insert_table()` — use `HeapWriter::insert` instead of direct `HeapPage::insert`
  - `insert_column()` — use `HeapWriter::insert` instead of direct `HeapPage::insert`
  - `create_sequence()` — use `HeapWriter::insert` instead of direct `HeapPage::insert`
  - `nextval()` — still uses direct `HeapPage` access (scan + in-place update is sequence-specific)
  - `bootstrap()` — still uses direct `HeapPage` access (bootstraps initial pages directly)

- `src/executor/context.rs` — Replace single-page scan with `HeapScanner`, add DML operations
  - `scan_heap_page` → replace with multi-page scan using `HeapScanner` (rename to `scan_table` or keep interface but walk chain internally)
  - Add `fn insert_tuple(...)` — delegates to `HeapWriter::insert`
  - Add `fn delete_tuple(...)` — sets xmax on tuple via HeapPage
  - Add `fn update_tuple(...)` — delete + insert with same-page priority
  - Add `fn nextval(...)` — delegates to `Catalog::nextval`

- `src/executor/node.rs` — Update `SeqScan` for multi-page, add DML nodes
  - `SeqScan` — remove single-page buffer, use `HeapScanner` via `ExecContext`
  - Add `InsertNode`, `UpdateNode`, `DeleteNode` structs and `ExecutorNode` variants
  - Add `ExecutorNode::execute_dml()` method

- `src/executor/plan.rs` — Add DML plan variants
  - `Plan::Insert { table_name, table_id, first_page, schema, column_count, values, serial_columns }`
  - `Plan::Update { table_name, input, assignments, schema, first_page }`
  - `Plan::Delete { table_name, input }`
  - Update `Plan::columns()` — DML plans return `&[]`
  - Update `Plan::explain()` — format DML plans

- `src/executor/planner.rs` — Add DML planner functions
  - `pub async fn plan_insert(stmt, catalog, snapshot) -> Result<Plan, ExecutorError>`
  - `pub async fn plan_update(stmt, catalog, snapshot) -> Result<Plan, ExecutorError>`
  - `pub async fn plan_delete(stmt, catalog, snapshot) -> Result<Plan, ExecutorError>`
  - Extract `build_seq_scan_plan` from existing `plan_select` to share with DML planners

- `src/executor/error.rs` — Add new error variants
  - `ColumnCountMismatch { expected, found }`
  - `DuplicateColumn { name }`
  - `Heap(HeapError)` — wraps HeapError
  - Add `From<HeapError>` impl

- `src/executor.rs` — Re-export new planner functions
  - `pub use planner::{plan_insert, plan_update, plan_delete}`

- `src/db/session.rs` — Wire DML through `execute_statement`
  - `Statement::Insert/Update/Delete` → plan → execute → command tag
  - EXPLAIN support for DML plans

### Dependency Graph

```text
session → planner → catalog (read schema)
session → node → context (heap I/O)
planner → expr (bind expressions)
planner → plan (construct plans)
node → context → heap/writer (insert tuples)
                → heap/scanner (scan tuples)
                → heap/page (delete: update_header)
                → catalog (nextval for SERIAL)
node → eval (evaluate BoundExpr)
catalog → heap/writer (insert catalog tuples)
catalog → heap/scanner (scan catalog tuples)
catalog → heap/page (nextval: in-place update)
```

No circular dependencies. `heap/writer` and `heap/scanner` are shared by both `executor/context` and `catalog/core`, providing a unified multi-page heap abstraction.

## Error Hierarchy

| Error Type | Module | New Variants | Converted to |
| --- | --- | --- | --- |
| `ExecutorError` | `executor/error.rs` | `ColumnCountMismatch`, `DuplicateColumn`, `Heap(HeapError)` | `DatabaseError::Executor(ExecutorError)` |
| `HeapError` | `heap/error.rs` | (existing `PageFull`, `SlotNotFound`) | `ExecutorError::Heap(HeapError)` |

## Edge Case Checklist

### Multi-page
- [ ] Single-page table scan works as before (regression)
- [ ] SeqScan follows page chain across multiple pages
- [ ] INSERT into full page allocates new page and links via next_page
- [ ] INSERT into table with multiple pages — scan chain for space, append new page if all full
- [ ] HeapPage next_page = 0 means no next page (sentinel)
- [ ] HeapExtra area is properly initialized by `HeapPage::init()`
- [ ] Catalog tables work with multi-page (get_table, get_columns scan full chain)
- [ ] Catalog insert_table/insert_column use HeapWriter (auto-extend on page full)
- [ ] Bootstrap still works (direct single-page init, no HeapWriter needed)

### INSERT
- [ ] INSERT with explicit column list in different order than table schema
- [ ] INSERT with fewer columns than table — unspecified non-SERIAL columns get NULL
- [ ] INSERT with SERIAL columns — auto-populate via nextval, skip if explicitly provided
- [ ] INSERT with duplicate column names in column list → error
- [ ] INSERT with too many/few values vs column count → error
- [ ] Multi-row INSERT (`VALUES (...), (...), (...)`) — each row gets same xmin/cmin
- [ ] Type coercion: integer literal `42` into SMALLINT column → cast Bigint→Smallint
- [ ] Type coercion: float literal `3.14` into INTEGER column → cast Double→Integer (rounds)
- [ ] Type coercion: string literal `'hello'` into INTEGER column → error
- [ ] Type coercion: NULL into any column type → pass through as Null
- [ ] Page full during INSERT → auto-extend to new page

### DELETE
- [ ] DELETE with WHERE → only matching rows get xmax set
- [ ] DELETE without WHERE → all visible rows deleted
- [ ] DELETE on empty table → affected count = 0
- [ ] DELETE visibility: only rows visible to current snapshot are candidates

### UPDATE
- [ ] UPDATE with WHERE → only matching rows get delete+insert treatment
- [ ] UPDATE without WHERE → all visible rows updated
- [ ] UPDATE on empty table → affected count = 0
- [ ] UPDATE same-page priority: try inserting new version on same page as deleted tuple
- [ ] UPDATE fallback: if same page is full, walk chain / allocate new page
- [ ] UPDATE type coercion on SET values (same rules as INSERT)
- [ ] UPDATE preserves columns not in SET list
- [ ] UPDATE SET with expression referencing other columns (e.g., `SET x = x + 1`)

### Transaction / MVCC
- [ ] Auto-commit mode: DML wraps in transaction if not in explicit one
- [ ] Explicit transaction: DML uses transaction's txid/cid
- [ ] CommandId increment: each DML statement in a transaction gets next CommandId
- [ ] Failed DML in explicit transaction → transaction marked failed, only ROLLBACK accepted

### Protocol
- [ ] INSERT command tag: `INSERT 0 {count}` (the `0` is a legacy OID, always 0)
- [ ] UPDATE command tag: `UPDATE {count}`
- [ ] DELETE command tag: `DELETE {count}`

## Commit Plan

- [x] **Commit 1: HeapPage layout with HeapExtra header** — Add 4-byte `HeapExtra` region (bytes 24..28) to `HeapPage` for `next_page: u32`. Parameterize `SlottedPage` to accept `data_offset` so the slot array starts after type-specific headers. Add `HeapPage::next_page()` / `set_next_page()`. `PageHeader` remains unchanged.
  - Tests: HeapPage next_page roundtrip, init sets next_page to None, SlottedPage insert/get/scan still work with new offset, MAX_RECORD_SIZE decreased by 4, existing HeapPage tests pass (regression)
  - Edge cases: next_page = 0 sentinel, SlottedPage data_offset correctness

- [x] **Commit 2: HeapScanner — multi-page scan** — Implement `HeapScanner` that walks the page chain and yields all tuples (without MVCC filtering). Refactor `ExecContext::scan_heap_page` to use `HeapScanner` for multi-page scan, update `SeqScan` node accordingly. Refactor `Catalog::get_table/get_columns` to use `HeapScanner`.
  - Tests: scan single page (regression), scan across 2-3 linked pages, scan empty table, scan table with empty intermediate pages, catalog get_table/get_columns still work
  - Edge cases: page chain traversal terminates at next_page=0

- [ ] **Commit 3: HeapWriter — multi-page insert** — Implement `HeapWriter` that walks the page chain to find free space, allocates and links new pages when full. Refactor `Catalog::insert_table/insert_column/create_sequence` to use `HeapWriter`.
  - Tests: insert into page with space, insert triggers new page allocation and linkage, catalog create_table + get_table roundtrip after refactor, insert many rows spanning multiple pages, verify page chain integrity after multiple inserts
  - Edge cases: page full → new page allocation, catalog multi-page scenario (many tables/columns)

- [ ] **Commit 4: ExecContext DML operations** — Extend `ExecContext` trait and `ExecContextImpl` with `insert_tuple` (via HeapWriter), `delete_tuple` (set xmax), `update_tuple` (delete + insert with same-page priority), `nextval`
  - Tests: insert a tuple via context and verify it's readable, delete a tuple and verify not visible, update a tuple and verify new version, nextval returns incrementing values, insert triggers page extension
  - Edge cases: same-page UPDATE priority, cross-page UPDATE fallback

- [ ] **Commit 5: DML planner — plan_insert** — Add `Plan::Insert` and `plan_insert()` with column resolution, SERIAL handling, type coercion
  - Tests: basic INSERT plan, INSERT with column list, INSERT with column reordering, INSERT with SERIAL skip, column count mismatch error, duplicate column error, type coercion (integer→smallint, float→integer, incompatible types error), multi-row INSERT
  - Edge cases: column list ordering, SERIAL auto-populate, type coercion

- [ ] **Commit 6: DML planner — plan_update and plan_delete** — Add `Plan::Update`, `Plan::Delete`, `plan_update()`, `plan_delete()` with shared scan construction
  - Tests: basic UPDATE plan, UPDATE with WHERE, DELETE plan, DELETE with WHERE, UPDATE type coercion on SET values, UPDATE referencing existing columns
  - Edge cases: UPDATE type coercion, expression referencing other columns

- [ ] **Commit 7: DML executor nodes and EXPLAIN** — Add `InsertNode`, `UpdateNode`, `DeleteNode` with `execute_dml()`, EXPLAIN support for DML plans
  - Tests: INSERT executes and returns correct affected count, DELETE filters and returns count, UPDATE delete+insert, multi-row INSERT, UPDATE/DELETE without WHERE, EXPLAIN INSERT/UPDATE/DELETE
  - Edge cases: empty table operations, multi-page INSERT

- [ ] **Commit 8: Session integration and end-to-end tests** — Wire DML through `Session::execute_statement`, correct command tags, full SQL round-trip tests
  - Tests: `INSERT INTO t VALUES (...)` → SELECT verifies data, UPDATE modifies data → SELECT verifies, DELETE removes data → SELECT verifies, multi-statement transaction (BEGIN → INSERT → UPDATE → DELETE → SELECT → COMMIT), auto-commit DML, failed DML sets failed flag, EXPLAIN DML, SERIAL column auto-increment, multi-page INSERT (many rows) → SELECT returns all
  - Edge cases: transaction abort visibility, command tag format, CommandId increment
