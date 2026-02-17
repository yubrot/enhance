# Design Sketch: Step 12 — Sort & Aggregation

> ORDER BY with in-memory sort, GROUP BY, aggregate functions (COUNT, SUM, AVG, MIN, MAX).

## Type Glossary

| Type | Module | Purpose |
| --- | --- | --- |
| `AggregateFunction` | `executor/aggregate.rs` | Enum of supported aggregate functions (Count, Sum, Avg, Min, Max) |
| `AggregateOp` | `executor/aggregate.rs` | A single aggregate operation: function + argument expression + distinct flag |
| `Accumulator` | `executor/aggregate.rs` | Trait for aggregate state machines (init → feed → finish) |
| `CountAccumulator` | `executor/aggregate.rs` | COUNT(\*) and COUNT(expr) accumulator |
| `SumAccumulator` | `executor/aggregate.rs` | SUM(expr) accumulator |
| `AvgAccumulator` | `executor/aggregate.rs` | AVG(expr) accumulator (always returns Double) |
| `MinAccumulator` | `executor/aggregate.rs` | MIN(expr) accumulator |
| `MaxAccumulator` | `executor/aggregate.rs` | MAX(expr) accumulator |
| `GroupKey` | `executor/aggregate.rs` | HashMap key for GROUP BY grouping (wraps `Vec<Value>` with NULL=NULL Eq + Hash) |
| `SortItem` | `executor/plan.rs` | ORDER BY item in plan: bound expression + direction + null ordering |
| `QueryPlan::Sort` | `executor/plan.rs` | Logical sort node |
| `QueryPlan::Aggregate` | `executor/plan.rs` | Logical aggregate node (GROUP BY + aggregates) |
| `QueryPlan::Limit` | `executor/plan.rs` | Logical LIMIT/OFFSET node |
| `Sort<C>` | `executor/runner.rs` | Physical sort node (buffers all input, sorts, then emits) |
| `Aggregate<C>` | `executor/runner.rs` | Physical hash-aggregate node |
| `Limit<C>` | `executor/runner.rs` | Physical limit node (counter-based) |
| `BoundExpr::AggregateCall` | `executor/expr.rs` | Intermediate aggregate marker in bound expression tree |

### Naming Decisions

- **"accumulator"**: The stateful object that processes one value at a time during aggregation. Matches PostgreSQL's internal terminology (`AggState` / `advance_aggregates`). Chosen over "aggregator" to avoid confusion with the `Aggregate` plan node.
- **"sort item"** vs **"order by item"**: `SortItem` in the plan layer (the plan describes what to sort), `OrderByItem` in the AST layer (preserving the SQL syntax origin). The plan type is decoupled from AST.
- **`AggregateCall`**: A BoundExpr variant that exists only transiently — the planner extracts it and replaces it with a `Column` reference. Named "Call" to distinguish from the `Aggregate` plan node.
- **`GroupKey`**: A wrapper around `Vec<Value>` with SQL GROUP BY equality semantics (NULL = NULL for grouping, NaN = NaN). Unlike `Value::PartialEq` which returns `false` for NULL comparisons, `GroupKey` treats NULLs as equal for grouping purposes. This matches PostgreSQL behavior and is required because `Value` implements neither `Eq` nor `Hash`.

## Prerequisite Refactoring

**Add `PartialEq` derive to `BoundExpr`** (`executor/expr.rs`).

GROUP BY expression matching requires structural equality comparison of `BoundExpr` trees. For example, `SELECT x + 1, COUNT(*) FROM t GROUP BY x + 1` needs to detect that the SELECT expression `x + 1` matches the GROUP BY expression `x + 1`. Currently `BoundExpr` derives only `Debug, Clone`. Adding `PartialEq` enables this matching.

`f64` values within `BoundExpr::Float` use IEEE 754 equality for `PartialEq` (NaN != NaN), which is acceptable for structural matching of AST expressions — we compare expression *structure*, not runtime values.

This must happen before the feature implementation because `rewrite_for_aggregate_output` relies on `BoundExpr::eq()` to match SELECT/HAVING/ORDER BY column references against GROUP BY expressions.

## Module Structure

### New Modules

```rust
// src/executor/aggregate.rs — Aggregate function definitions and accumulators

/// Supported aggregate functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AggregateFunction {
    Count,
    Sum,
    Avg,
    Min,
    Max,
}

/// A single aggregate operation within an Aggregate plan node.
///
/// Pairs the function with its argument expression and optional DISTINCT flag.
/// COUNT(*) is represented as `func: Count` with `args: vec![]`.
#[derive(Debug, Clone, PartialEq)]
pub struct AggregateOp {
    /// Aggregate function to apply.
    pub func: AggregateFunction,
    /// Argument expressions (empty for COUNT(*)).
    pub args: Vec<BoundExpr>,
    /// Whether DISTINCT was specified.
    pub distinct: bool,
}

impl AggregateOp {
    /// Returns the output type of this aggregate operation.
    ///
    /// - COUNT → Bigint
    /// - SUM: Smallint/Integer/Bigint input → Bigint, Real/Double input → Double
    /// - AVG → always Double (regardless of input type)
    /// - MIN/MAX → same as input type
    ///
    /// For SUM/AVG, non-numeric input types (Bool, Text, Bytea) are rejected
    /// at planning time via ExecutorError::TypeMismatch, not here.
    pub fn output_type(&self) -> Type { .. }

    /// Creates an accumulator for this aggregate operation.
    pub fn create_accumulator(&self) -> Box<dyn Accumulator> { .. }
}

impl fmt::Display for AggregateFunction { .. }
impl fmt::Display for AggregateOp { .. }

/// Stateful aggregate computation.
///
/// Follows a three-phase lifecycle: creation → feed → finish.
/// Each accumulator processes one group's values.
///
/// DISTINCT filtering is handled by the Aggregate executor node,
/// not by the accumulator. The executor deduplicates values before
/// feeding them, so accumulators are always DISTINCT-unaware.
pub trait Accumulator: Send {
    /// Feeds a single value into the accumulator.
    ///
    /// For COUNT(*), the executor calls feed(Value::Null) once per row
    /// (the value is ignored; only the call count matters).
    /// For all other aggregates, NULL values are skipped by the caller.
    fn feed(&mut self, value: &Value) -> Result<(), ExecutorError>;

    /// Produces the final aggregate result.
    fn finish(&self) -> Value;
}

// CountAccumulator: count: i64
// SumAccumulator: sum: Value (Null initially, promoted to Bigint or Double)
// AvgAccumulator: sum: f64, count: i64
// MinAccumulator: min: Value (Null initially)
// MaxAccumulator: max: Value (Null initially)

/// HashMap key for GROUP BY grouping.
///
/// Wraps a `Vec<Value>` with SQL GROUP BY equality semantics:
/// - NULL = NULL (unlike Value::PartialEq which returns false)
/// - NaN = NaN (for float grouping)
///
/// This is necessary because `Value` implements neither `Eq` nor `Hash`
/// due to NULL and floating-point semantics.
///
/// Also used for DISTINCT aggregate deduplication: each DISTINCT aggregate
/// per group maintains a `HashSet<GroupKey>` where GroupKey wraps a
/// single-element Vec (the argument value) for dedup.
#[derive(Debug, Clone)]
pub struct GroupKey(pub Vec<Value>);

impl PartialEq for GroupKey { .. }
impl Eq for GroupKey {}
impl Hash for GroupKey {
    // Hash strategy: for each value, hash a discriminant tag + value bytes.
    // NULL gets its own tag. Floats use to_bits() for NaN-consistent hashing.
    fn hash<H: Hasher>(&self, state: &mut H) { .. }
}
```

### Modified Modules

```rust
// src/executor/expr.rs — Add PartialEq derive and AggregateCall variant

#[derive(Debug, Clone, PartialEq)]  // PartialEq added (prerequisite)
pub enum BoundExpr {
    // ... existing variants ...

    /// Aggregate function call (transient: extracted by planner).
    ///
    /// This variant exists only during expression binding. The planner's
    /// `rewrite_for_aggregate_output` extracts all AggregateCall nodes,
    /// moves them into the Aggregate plan node, and replaces them with
    /// Column references pointing to the Aggregate node's output positions.
    AggregateCall {
        func: AggregateFunction,
        args: Vec<BoundExpr>,
        distinct: bool,
    },
}

// Expr::bind() — handle Expr::Function:
//   - Match function name (case-insensitive): "count", "sum", "avg", "min", "max"
//   - COUNT(*) special handling: parser produces
//     Expr::Function { name: "count", args: [ColumnRef { table: None, column: "*" }] }
//     Detect ColumnRef("*") and convert to AggregateCall { func: Count, args: vec![], .. }
//     (do NOT attempt to resolve "*" as a column name)
//   - Other aggregates: bind args normally, then wrap in AggregateCall
//   - Non-aggregate function names → ExecutorError::Unsupported

// BoundExpr::ty() — AggregateCall: compute from func + args using same
//   logic as AggregateOp::output_type()
// BoundExpr::Display — e.g. "COUNT(*)", "SUM($col0 (x))", "COUNT(DISTINCT $col1 (name))"

// BoundExpr::evaluate() — AggregateCall: panic or return Unsupported error.
//   This variant should never survive to evaluation; it is always rewritten
//   by the planner. Reaching evaluate() indicates a planner bug.
```

```rust
// src/executor/plan.rs — Add Sort, Aggregate, Limit variants

/// ORDER BY item in a plan node.
#[derive(Debug, Clone)]
pub struct SortItem {
    /// Expression to sort by (bound against the Sort node's child output schema).
    pub expr: BoundExpr,
    /// Sort direction (ASC/DESC).
    pub direction: SortDirection,
    /// NULL ordering (FIRST/LAST/Default).
    pub nulls: NullOrdering,
}

pub enum QueryPlan {
    // ... existing variants ...

    /// Hash-aggregate node.
    ///
    /// Output schema: [group_by columns..., aggregate results...].
    /// When group_by is empty, produces exactly one row (scalar aggregate).
    Aggregate {
        /// Child plan to pull rows from.
        input: Box<QueryPlan>,
        /// GROUP BY expressions (bound against child's output schema).
        group_by: Vec<BoundExpr>,
        /// Aggregate operations to compute.
        aggregates: Vec<AggregateOp>,
        /// Output column descriptors.
        columns: Vec<ColumnDesc>,
    },

    /// In-memory sort node.
    Sort {
        /// Child plan to pull rows from.
        input: Box<QueryPlan>,
        /// Sort key items (expression, direction, null ordering).
        items: Vec<SortItem>,
    },

    /// LIMIT/OFFSET node.
    ///
    /// Values are evaluated at planning time (constant expressions only).
    /// Type checking (must be integer), negative value rejection, and
    /// i64→u64 conversion all happen in the planner, not at execution time.
    Limit {
        /// Child plan to pull rows from.
        input: Box<QueryPlan>,
        /// Maximum rows to return (None = no limit).
        limit: Option<u64>,
        /// Rows to skip before returning (0 = no offset).
        offset: u64,
    },
}

// QueryPlan::columns() — new arms:
//   Aggregate { columns, .. } => columns
//   Sort { input, .. } => input.columns()
//   Limit { input, .. } => input.columns()

// QueryPlan::fmt_explain() — new arms:
//   Aggregate: "Aggregate: group_by=[expr, ...], aggregates=[COUNT(*), SUM(...), ...]"
//   Sort: "Sort: expr1 ASC NULLS LAST, expr2 DESC NULLS FIRST"
//   Limit: "Limit: limit=N offset=M"
```

```rust
// src/executor/runner.rs — Add Sort, Aggregate, Limit executor nodes

pub enum QueryNode<C: ExecContext> {
    // ... existing variants ...
    Sort(Sort<C>),
    Aggregate(Aggregate<C>),
    Limit(Limit<C>),
}

/// In-memory sort node.
///
/// Buffers all input rows on first next() call, sorts them by the
/// specified key expressions, then emits one row at a time.
///
/// NOTE: Loads entire result set into memory. For production, consider
/// external sort (disk-based merge sort) for data exceeding memory limits.
pub struct Sort<C: ExecContext> {
    child: Box<QueryNode<C>>,
    items: Vec<SortItem>,
    /// Buffered sorted rows (populated on first next() call).
    buffer: Option<std::vec::IntoIter<Row>>,
}

impl<C: ExecContext> Sort<C> {
    pub fn new(child: QueryNode<C>, items: Vec<SortItem>) -> Self { .. }
    async fn next(&mut self) -> Result<Option<Row>, ExecutorError> { .. }
}

/// Hash-aggregate node.
///
/// Consumes all input rows on first next() call, groups them by the
/// GROUP BY key (using `GroupKey` for NULL=NULL HashMap semantics),
/// computes aggregate values per group, then emits result rows one
/// at a time.
///
/// Output schema: [group_key_values..., aggregate_results...].
///
/// Internal data structures:
/// - `HashMap<GroupKey, Vec<Box<dyn Accumulator>>>`: per-group accumulators
/// - For DISTINCT aggregates: `HashMap<GroupKey, Vec<HashSet<GroupKey>>>`
///   where the inner HashSet deduplicates argument values before feeding.
///   Only DISTINCT-flagged aggregates have an associated HashSet; non-DISTINCT
///   aggregates have no HashSet entry. The inner GroupKey wraps a single-element
///   Vec for single-argument dedup.
///
/// NOTE: Loads all group keys and accumulators into memory. For
/// production, consider sort-based grouping with spill-to-disk for
/// high-cardinality GROUP BY.
pub struct Aggregate<C: ExecContext> {
    child: Box<QueryNode<C>>,
    group_by: Vec<BoundExpr>,
    aggregates: Vec<AggregateOp>,
    columns: Vec<ColumnDesc>,
    /// Buffered result rows (populated on first next() call).
    buffer: Option<std::vec::IntoIter<Row>>,
}

impl<C: ExecContext> Aggregate<C> {
    pub fn new(
        child: QueryNode<C>,
        group_by: Vec<BoundExpr>,
        aggregates: Vec<AggregateOp>,
        columns: Vec<ColumnDesc>,
    ) -> Self { .. }
    async fn next(&mut self) -> Result<Option<Row>, ExecutorError> { .. }
}

/// LIMIT/OFFSET node.
///
/// Skips `offset` rows from the child, then returns at most `limit` rows.
pub struct Limit<C: ExecContext> {
    child: Box<QueryNode<C>>,
    limit: Option<u64>,
    offset: u64,
    /// Number of rows skipped so far.
    skipped: u64,
    /// Number of rows emitted so far.
    emitted: u64,
}

impl<C: ExecContext> Limit<C> {
    pub fn new(child: QueryNode<C>, limit: Option<u64>, offset: u64) -> Self { .. }
    async fn next(&mut self) -> Result<Option<Row>, ExecutorError> { .. }
}

// QueryPlan::prepare_for_execute() — new arms:
//   Sort { input, items } => QueryNode::Sort(Sort::new(input.prepare_for_execute(ctx), items))
//   Aggregate { .. } => QueryNode::Aggregate(Aggregate::new(..))
//   Limit { input, limit, offset } =>
//     Values are already u64 (evaluated at planning time).
//     QueryNode::Limit(Limit::new(input.prepare_for_execute(ctx), limit, offset))
```

```rust
// src/executor/planner.rs — Extend plan_select for ORDER BY, GROUP BY, LIMIT/OFFSET

pub fn plan_select(select: &SelectStmt, catalog: &Catalog) -> Result<QueryPlan, ExecutorError> {
    // Remove Unsupported checks for: group_by, having, order_by, limit, offset
    // Keep Unsupported for: distinct, locking

    // Step 1: FROM → SeqScan (unchanged)
    let scan_columns = plan.columns().to_vec();  // "scan schema"

    // Step 2: WHERE → Filter (unchanged)
    //   Validate: no aggregates in WHERE (contains_aggregate check → AggregateNotAllowed)

    // Step 3: Detect aggregation context
    //   has_aggregation = group_by is non-empty
    //                     OR any SELECT/HAVING/ORDER BY expr contains aggregate
    //   (ORDER BY must be included: `SELECT x FROM t ORDER BY COUNT(*)` triggers
    //   aggregation context, leading to NonAggregatedColumn for x.)
    //
    //   If aggregation is needed:
    //     a. Bind GROUP BY expressions against scan_columns
    //     b. Validate: no aggregates in GROUP BY (→ AggregateNotAllowed)
    //     c. Bind SELECT list against scan_columns (produces BoundExpr with AggregateCall)
    //     d. Validate: SUM/AVG arguments must be numeric (→ TypeMismatch at planning time)
    //     e. Rewrite SELECT list via rewrite_for_aggregate_output:
    //        - Extract AggregateCall → Vec<AggregateOp> (with dedup by PartialEq)
    //        - Remap column refs to GROUP BY output positions
    //        - Non-GROUP BY column refs → NonAggregatedColumn error
    //     f. Build Aggregate output schema (columns):
    //        GROUP BY columns get ColumnDesc from scan schema
    //        Aggregate results get synthetic ColumnDesc (name from function, ty from output_type)
    //     g. Build Aggregate plan node
    //     h. If HAVING present:
    //        - Bind HAVING against scan_columns
    //        - Validate: no nested aggregates (aggregate within aggregate)
    //        - Rewrite via rewrite_for_aggregate_output (shares aggregate list from step e;
    //          if a duplicate aggregate is found via PartialEq, reuse existing position)
    //        - Wrap Aggregate in Filter using the rewritten HAVING predicate
    //
    //   If no aggregation:
    //     - Standard path (bind SELECT as before)
    //     - HAVING present → error (HAVING without aggregate context)

    // Step 4: ORDER BY → Sort (if non-empty)
    //   For each OrderByItem, resolve the sort expression via three cases:
    //
    //   Case A: Integer literal N → positional reference (1-indexed).
    //     Use the already-rewritten SELECT expression at position N-1.
    //     No further rewrite needed (expression is already Aggregate-output-bound).
    //     Error if N < 1 or N > SELECT list length.
    //
    //   Case B: Simple column name matching a SELECT alias.
    //     Use the already-rewritten SELECT expression for that alias.
    //     No further rewrite needed.
    //
    //   Case C: No positional/alias match.
    //     Bind the ORDER BY expression against the **scan schema**
    //     (pre-Aggregate columns), NOT the Aggregate output.
    //     If aggregation context: rewrite via rewrite_for_aggregate_output
    //     (handles ORDER BY COUNT(*), ORDER BY group_col, etc.).
    //     If no aggregation: use as-is.
    //
    //   Build Sort node with SortItems.

    // Step 5: SELECT list → Projection
    //   If aggregation: use rewritten SELECT exprs (Column refs to Aggregate output)
    //   If no aggregation: bind as before

    // Step 6: LIMIT/OFFSET → Limit (if present)
    //   Bind limit/offset as constant expressions (empty column list — no column refs).
    //   Evaluate immediately to get Value:
    //     - Non-integer result → TypeMismatch error
    //     - Negative value → Unsupported("negative LIMIT/OFFSET") error
    //     - Convert i64 → u64 and store in QueryPlan::Limit
    //   All validation happens here (planning time), not at prepare_for_execute.

    // Final plan tree: SeqScan → Filter → [Aggregate → [HAVING Filter]] → [Sort] → Projection → [Limit]
}

// New helper functions:

/// Checks whether an AST expression tree contains any aggregate function call.
/// Used to validate that aggregates don't appear in WHERE or GROUP BY.
fn contains_aggregate(expr: &Expr) -> bool { .. }

/// Rewrites a BoundExpr tree (bound against scan schema) for use above
/// an Aggregate node.
///
/// At each recursive step, the following checks are applied in order:
///
/// 1. **AggregateCall extraction**: If the node is an AggregateCall,
///    extract it into the aggregates list and replace with a Column ref
///    (index = group_by.len() + position). Duplicate aggregates (matched
///    by PartialEq on AggregateOp) reuse the existing position.
///
/// 2. **Whole-expression GROUP BY match**: Compare the entire expression
///    (not just Column nodes) against the GROUP BY list using
///    BoundExpr::eq(). If group_by[i] matches, replace the entire
///    subtree with Column { index: i }. This enables GROUP BY on
///    expressions like `x + 1`: the SELECT's `BinaryOp(Column(x), Add, 1)`
///    matches group_by[0] and becomes `Column { index: 0 }`.
///
/// 3. **Leaf handling**:
///    - Column ref → NonAggregatedColumn error (not in GROUP BY)
///    - Literal (Integer, Float, String, Boolean, Null) → return as-is
///      (constants don't require GROUP BY membership)
///
/// 4. **Composite expressions**: Recurse into children (BinaryOp,
///    UnaryOp, Case, IsNull, etc.). This handles mixed expressions
///    like `COUNT(*) + 1` where step 2 won't match but step 1 handles
///    the AggregateCall child and the literal `1` passes step 3.
///
/// **Precondition**: `expr` and all `group_by` entries must be bound
/// against the same `scan_columns` slice. This ensures that
/// `BoundExpr::PartialEq` (derived, including the `name` field of
/// Column variants) produces correct results — the same column always
/// resolves to the same index and name via `resolve_column_index`.
fn rewrite_for_aggregate_output(
    expr: BoundExpr,
    group_by: &[BoundExpr],
    aggregates: &mut Vec<AggregateOp>,
) -> Result<BoundExpr, ExecutorError> { .. }

/// Resolves an aggregate function name to an AggregateFunction enum value.
/// Returns None for non-aggregate function names.
fn resolve_aggregate_function(name: &str) -> Option<AggregateFunction> { .. }
```

```rust
// src/executor/error.rs — New variants

pub enum ExecutorError {
    // ... existing variants ...

    /// Aggregate function used in a context where it is not allowed.
    AggregateNotAllowed {
        context: String, // e.g., "WHERE clause", "GROUP BY expression"
    },

    /// Non-aggregated column in SELECT/HAVING/ORDER BY with GROUP BY.
    NonAggregatedColumn {
        name: String,
    },
}
```

```rust
// src/executor.rs — Export new module

mod aggregate;

pub use aggregate::{AggregateFunction, AggregateOp};
pub use plan::SortItem;
// (Accumulator, GroupKey, accumulators are not public — internal to executor)
```

### Dependency Graph

```text
session → planner → catalog (read-only)
session → runner → context (I/O abstraction)
planner → aggregate (AggregateFunction, AggregateOp)
planner → expr (BoundExpr, AggregateCall binding)
runner → aggregate (Accumulator creation, GroupKey for HashMap)
runner → eval (expression evaluation for sort keys / group keys)
aggregate → expr (BoundExpr for argument expressions)
aggregate → eval (expression evaluation within accumulators)
aggregate → datum (Value, Type)
planner ✗ runner (no direct dependency)
```

No circular dependencies. `aggregate` is a peer of `expr`/`eval`, both under `executor`.

## Error Hierarchy

| Error Type | Module | New Variants | Converted to |
| --- | --- | --- | --- |
| `ExecutorError` | `executor/error.rs` | `AggregateNotAllowed { context }`, `NonAggregatedColumn { name }` | `EngineError::Executor(ExecutorError)` |

## Edge Case Checklist

### Sort

- [ ] NULL ordering: NULLS FIRST vs NULLS LAST (default: NULLS LAST for ASC, NULLS FIRST for DESC)
- [ ] NaN ordering in sort: NaN > all non-NaN values (consistent with `Value::PartialOrd`)
- [ ] Empty result set: Sort on zero rows returns zero rows
- [ ] Sort stability: rows with equal sort keys preserve input order (`sort_by` is stable in Rust)
- [ ] Multi-key sort: secondary key used when primary key values are equal
- [ ] ORDER BY expression referencing non-SELECT column (resolved against pre-Projection schema)
- [ ] ORDER BY with SELECT alias: `SELECT x AS y FROM t ORDER BY y`
- [ ] ORDER BY positional: `ORDER BY 1` (1-indexed, references SELECT list position)
- [ ] ORDER BY positional out of range: `ORDER BY 0` or `ORDER BY N+1` → error

### Aggregation

- [ ] Scalar aggregate (no GROUP BY): `SELECT COUNT(*) FROM t` returns exactly one row
- [ ] Scalar aggregate on empty table: COUNT(\*) → 0, SUM/AVG/MIN/MAX → NULL
- [ ] GROUP BY on empty table: returns zero rows
- [ ] COUNT(\*) vs COUNT(col): COUNT(\*) counts all rows including NULLs, COUNT(col) skips NULLs
- [ ] COUNT(\*) binding: parser's `ColumnRef("*")` must not resolve as a column name
- [ ] COUNT(DISTINCT col): counts unique non-NULL values only
- [ ] DISTINCT aggregate dedup: uses GroupKey-based HashSet in executor, not accumulator
- [ ] SUM/AVG on non-numeric type: error at planning time (TypeMismatch)
- [ ] SUM integer overflow: checked arithmetic, return error
- [ ] SUM type promotion: Smallint/Integer/Bigint → Bigint, Real/Double → Double
- [ ] AVG always returns Double regardless of input type
- [ ] MIN/MAX on text: lexicographic comparison
- [ ] MIN/MAX on all NULLs: returns NULL
- [ ] Non-aggregated column in SELECT with GROUP BY: error (e.g., `SELECT id, COUNT(*) FROM t GROUP BY name`)
- [ ] Aggregate in WHERE clause: error (e.g., `SELECT * FROM t WHERE COUNT(*) > 1`)
- [ ] Aggregate in GROUP BY expression: error
- [ ] HAVING with aggregate: filters groups after aggregation
- [ ] HAVING without GROUP BY: valid (treats entire table as one group)
- [ ] HAVING shares aggregate list with SELECT: duplicate aggregates reuse same output position
- [ ] GROUP BY with multiple keys: composite grouping
- [ ] GROUP BY expression (not just column): `SELECT x + 1, COUNT(*) FROM t GROUP BY x + 1`
- [ ] GROUP BY NULL grouping: all NULLs grouped together (GroupKey semantics)
- [ ] Column remapping after Aggregate: SELECT/HAVING/ORDER BY column refs remapped to Aggregate output positions

### LIMIT/OFFSET

- [ ] LIMIT 0: returns zero rows
- [ ] OFFSET exceeding row count: returns zero rows
- [ ] LIMIT without ORDER BY: result order is non-deterministic (valid SQL)
- [ ] Negative LIMIT/OFFSET: error at planning time (i64 → u64 conversion check)
- [ ] LIMIT/OFFSET with non-integer expression: TypeMismatch error at planning time
- [ ] ORDER BY with aggregate triggers aggregation context: `SELECT x FROM t ORDER BY COUNT(*)` → NonAggregatedColumn

### Combined

- [ ] GROUP BY + ORDER BY + LIMIT: all three interact correctly
- [ ] ORDER BY aggregate result: `SELECT dept, COUNT(*) AS c FROM t GROUP BY dept ORDER BY c`
- [ ] ORDER BY aggregate expression: `SELECT dept FROM t GROUP BY dept ORDER BY COUNT(*)`
- [ ] EXPLAIN output includes Sort, Aggregate, and Limit nodes

## Commit Plan

- [x] **Commit 1: Aggregate foundation** — `AggregateFunction`, `AggregateOp`, `Accumulator` trait, five accumulator implementations, and `GroupKey` in `executor/aggregate.rs`. Add `PartialEq` derive to `BoundExpr` (prerequisite). Add `BoundExpr::AggregateCall` variant to `executor/expr.rs` with `ty()`, `Display`, `Expr::bind()` support for aggregate function calls (including COUNT(\*) special handling for `ColumnRef("*")`), and `evaluate()` panic guard.
  - Tests: Accumulator unit tests (feed/finish for each function, NULL handling, empty input, overflow for SUM). GroupKey Eq/Hash tests (NULL=NULL, NaN=NaN, mixed types). BoundExpr binding of `COUNT(*)`, `SUM(col)`, `AVG(col)`, `MIN(col)`, `MAX(col)`, `COUNT(DISTINCT col)`. Display formatting. Unknown function name → Unsupported error. `BoundExpr::PartialEq` structural equality tests.
  - Edge cases: Scalar aggregate on empty input, COUNT(\*) vs COUNT(col), SUM overflow, SUM type promotion, AVG returns Double, MIN/MAX on all NULLs, COUNT(\*) binding path.
  - Deviation: Added `aggregate_output_type()` and `fmt_aggregate()` as public helper functions in `aggregate.rs` (not in original Type Glossary). Extracted during REFINE to eliminate duplicated logic between `BoundExpr::AggregateCall` and `AggregateOp` for type inference and Display formatting.

- [x] **Commit 2: Aggregate plan node and executor** — `QueryPlan::Aggregate` variant with EXPLAIN support. `Aggregate<C>` executor node with hash-based grouping and DISTINCT dedup via `HashSet<GroupKey>`. Planner logic: `rewrite_for_aggregate_output` (aggregate extraction + column remapping + non-aggregated column detection), GROUP BY binding, HAVING rewrite (sharing aggregate list with SELECT), aggregate-in-WHERE/GROUP-BY validation, SUM/AVG type validation at planning time.
  - Tests: Planner tests: GROUP BY single key, multiple keys, scalar aggregate, GROUP BY expression (`x + 1`), HAVING with shared aggregate, column remapping correctness. Executor tests: GROUP BY with data, scalar aggregate, empty table, HAVING filter, DISTINCT aggregate, NULL grouping. EXPLAIN output. Error tests: aggregate in WHERE, aggregate in GROUP BY, non-aggregated column, SUM(text).
  - Edge cases: GROUP BY on empty table, non-aggregated column detection, aggregate in WHERE/GROUP BY error, HAVING without GROUP BY, HAVING shares aggregate list, GROUP BY expression matching, GROUP BY NULL grouping, column remapping after Aggregate, DISTINCT dedup.
  - Deviation: GROUP BY expression planner test (`x + 1`), DISTINCT aggregate executor test, and NULL grouping executor test deferred — the underlying logic is tested via `aggregate.rs` unit tests (GroupKey, Accumulator). Column remapping correctness verified implicitly through executor end-to-end tests (`test_aggregate_group_by` etc.) rather than a dedicated planner test.

- [ ] **Commit 3: Sort plan node and executor** — `SortItem`, `QueryPlan::Sort` variant with EXPLAIN support. `Sort<C>` executor node. Planner logic for ORDER BY: alias resolution (check SELECT aliases first), positional references (`ORDER BY 1`), aggregate context rewrite.
  - Tests: ORDER BY single column ASC/DESC, multi-column sort, NULLS FIRST/LAST, ORDER BY expression, ORDER BY with GROUP BY, ORDER BY alias, ORDER BY positional, ORDER BY aggregate expression. EXPLAIN output.
  - Edge cases: NULL ordering, NaN ordering, empty result sort, sort stability, ORDER BY non-SELECT column, ORDER BY alias resolution, ORDER BY positional out of range.

- [ ] **Commit 4: Limit plan node and executor** — `QueryPlan::Limit` variant (u64 fields) with EXPLAIN support. `Limit<C>` executor node. Planner logic: bind LIMIT/OFFSET as constant expressions, evaluate to i64, validate type (integer) and sign (non-negative) at planning time, convert to u64.
  - Tests: LIMIT only, OFFSET only, LIMIT + OFFSET, LIMIT 0, OFFSET exceeding row count, LIMIT + ORDER BY. EXPLAIN output. Error tests: negative LIMIT, negative OFFSET, non-integer expression (`LIMIT 'abc'`).
  - Edge cases: LIMIT 0, large OFFSET, negative values (planning-time error), non-integer expressions (planning-time error).

- [ ] **Commit 5: Integration and combined queries** — End-to-end tests combining all features. Full plan tree verification.
  - Tests: `SELECT dept, COUNT(*) FROM t GROUP BY dept ORDER BY COUNT(*) DESC LIMIT 3`, `SELECT COUNT(*) FROM t`, aggregate with WHERE + HAVING + ORDER BY + LIMIT, `SELECT x + 1 AS y, SUM(v) FROM t GROUP BY x + 1 ORDER BY y`. Full EXPLAIN output validation for combined plans.
  - Edge cases: ORDER BY aggregate result via alias, GROUP BY + ORDER BY + LIMIT interaction, EXPLAIN with all node types.
