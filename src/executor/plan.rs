//! Plan nodes for query execution.
//!
//! This module implements the Volcano-style iterator model where each plan node
//! provides a `next()` method that returns one tuple at a time.

use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use async_trait::async_trait;

use crate::catalog::ColumnInfo;
use crate::executor::value::{compare_values, evaluate, is_float, is_truthy, value_to_f64};
use crate::executor::ExecutorError;
use crate::heap::{HeapPage, Value};
use crate::protocol::type_oid;
use crate::sql::{Expr, NullOrdering, SortDirection};
use crate::storage::{BufferPool, PageId, Replacer, Storage};
use crate::tx::{Snapshot, TransactionManager};

/// Output column metadata for executor results.
#[derive(Debug, Clone)]
pub struct OutputColumn {
    /// Column name (may be alias or generated).
    pub name: String,
    /// PostgreSQL type OID.
    pub type_oid: i32,
}

impl OutputColumn {
    /// Creates a new output column.
    pub fn new(name: String, type_oid: i32) -> Self {
        Self { name, type_oid }
    }
}

/// A tuple of values produced by an executor.
#[derive(Debug, Clone)]
pub struct Tuple {
    /// The values in this tuple.
    pub values: Vec<Value>,
}

impl Tuple {
    /// Creates a new tuple with the given values.
    pub fn new(values: Vec<Value>) -> Self {
        Self { values }
    }
}

// =============================================================================
// Sort Data Structures
// =============================================================================

/// A key for sorting tuples.
#[derive(Debug, Clone)]
pub struct SortKey {
    /// Expression to evaluate for comparison.
    pub expr: Expr,
    /// Sort direction (ASC or DESC).
    pub direction: SortDirection,
    /// NULL ordering (FIRST, LAST, or default).
    pub nulls: NullOrdering,
}

impl SortKey {
    /// Creates a new sort key.
    pub fn new(expr: Expr, direction: SortDirection, nulls: NullOrdering) -> Self {
        Self {
            expr,
            direction,
            nulls,
        }
    }

    /// Returns the effective NULL ordering.
    ///
    /// PostgreSQL default: NULLS LAST for ASC, NULLS FIRST for DESC.
    pub fn effective_null_ordering(&self) -> NullOrdering {
        match self.nulls {
            NullOrdering::Default => match self.direction {
                SortDirection::Asc => NullOrdering::Last,
                SortDirection::Desc => NullOrdering::First,
            },
            other => other,
        }
    }
}

// =============================================================================
// Aggregate Data Structures
// =============================================================================

/// Aggregate functions supported by the executor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AggregateFunction {
    /// COUNT(*) or COUNT(expr) - counts non-NULL values (or all rows for COUNT(*)).
    Count,
    /// SUM(expr) - sum of numeric values.
    Sum,
    /// AVG(expr) - average of numeric values.
    Avg,
    /// MIN(expr) - minimum value.
    Min,
    /// MAX(expr) - maximum value.
    Max,
}

impl AggregateFunction {
    /// Parses a function name into an aggregate function.
    ///
    /// Returns `None` if the name is not a known aggregate function.
    pub fn from_name(name: &str) -> Option<Self> {
        match name.to_lowercase().as_str() {
            "count" => Some(AggregateFunction::Count),
            "sum" => Some(AggregateFunction::Sum),
            "avg" => Some(AggregateFunction::Avg),
            "min" => Some(AggregateFunction::Min),
            "max" => Some(AggregateFunction::Max),
            _ => None,
        }
    }

    /// Returns the name of this aggregate function.
    pub fn name(&self) -> &'static str {
        match self {
            AggregateFunction::Count => "count",
            AggregateFunction::Sum => "sum",
            AggregateFunction::Avg => "avg",
            AggregateFunction::Min => "min",
            AggregateFunction::Max => "max",
        }
    }
}

/// An aggregate expression in a SELECT list.
#[derive(Debug, Clone)]
pub struct AggregateExpr {
    /// The aggregate function.
    pub function: AggregateFunction,
    /// Argument expression (None for COUNT(*)).
    pub arg: Option<Expr>,
    /// Whether DISTINCT was specified.
    pub distinct: bool,
    /// Output alias.
    pub alias: String,
}

impl AggregateExpr {
    /// Creates a new aggregate expression.
    pub fn new(function: AggregateFunction, arg: Option<Expr>, distinct: bool, alias: String) -> Self {
        Self {
            function,
            arg,
            distinct,
            alias,
        }
    }
}

/// Group key for hash-based aggregation.
///
/// This wrapper provides Hash/Eq implementations that:
/// - Treat floats by their bit representation (for consistent hashing)
/// - Treat NULL = NULL for grouping purposes (unlike SQL comparison)
#[derive(Debug, Clone)]
pub struct GroupKey(pub Vec<Value>);

impl PartialEq for GroupKey {
    fn eq(&self, other: &Self) -> bool {
        if self.0.len() != other.0.len() {
            return false;
        }
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            if !values_equal_for_grouping(a, b) {
                return false;
            }
        }
        true
    }
}

impl Eq for GroupKey {}

impl Hash for GroupKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for value in &self.0 {
            hash_value_for_grouping(value, state);
        }
    }
}

/// Checks if two values are equal for grouping purposes.
///
/// Unlike SQL comparison where NULL != NULL, for grouping NULL = NULL.
fn values_equal_for_grouping(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Null, Value::Null) => true,
        (Value::Boolean(x), Value::Boolean(y)) => x == y,
        (Value::Int16(x), Value::Int16(y)) => x == y,
        (Value::Int32(x), Value::Int32(y)) => x == y,
        (Value::Int64(x), Value::Int64(y)) => x == y,
        (Value::Float32(x), Value::Float32(y)) => x.to_bits() == y.to_bits(),
        (Value::Float64(x), Value::Float64(y)) => x.to_bits() == y.to_bits(),
        (Value::Text(x), Value::Text(y)) => x == y,
        (Value::Bytea(x), Value::Bytea(y)) => x == y,
        // Different types are not equal
        _ => false,
    }
}

/// Hashes a value for grouping purposes.
fn hash_value_for_grouping<H: Hasher>(value: &Value, state: &mut H) {
    // Hash the discriminant first
    std::mem::discriminant(value).hash(state);

    match value {
        Value::Null => {} // Just the discriminant
        Value::Boolean(b) => b.hash(state),
        Value::Int16(n) => n.hash(state),
        Value::Int32(n) => n.hash(state),
        Value::Int64(n) => n.hash(state),
        Value::Float32(f) => f.to_bits().hash(state),
        Value::Float64(f) => f.to_bits().hash(state),
        Value::Text(s) => s.hash(state),
        Value::Bytea(b) => b.hash(state),
    }
}

/// Accumulator for computing aggregate values.
#[derive(Debug, Clone)]
pub enum Accumulator {
    /// COUNT accumulator.
    Count { count: i64 },
    /// SUM accumulator for integers.
    SumInt { sum: Option<i64> },
    /// SUM accumulator for floats.
    SumFloat { sum: Option<f64> },
    /// AVG accumulator.
    Avg { sum: f64, count: i64 },
    /// MIN accumulator.
    Min { value: Option<Value> },
    /// MAX accumulator.
    Max { value: Option<Value> },
}

impl Accumulator {
    /// Creates a new accumulator for the given aggregate function.
    pub fn new(function: AggregateFunction) -> Self {
        match function {
            AggregateFunction::Count => Accumulator::Count { count: 0 },
            AggregateFunction::Sum => Accumulator::SumInt { sum: None },
            AggregateFunction::Avg => Accumulator::Avg { sum: 0.0, count: 0 },
            AggregateFunction::Min => Accumulator::Min { value: None },
            AggregateFunction::Max => Accumulator::Max { value: None },
        }
    }

    /// Accumulates a value.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to accumulate.
    /// * `is_count_star` - True if this is COUNT(*), which counts all rows including NULLs.
    pub fn accumulate(&mut self, value: &Value, is_count_star: bool) -> Result<(), ExecutorError> {
        match self {
            Accumulator::Count { count } => {
                // COUNT(*) counts all rows, COUNT(expr) skips NULLs
                if is_count_star || !value.is_null() {
                    *count += 1;
                }
            }
            Accumulator::SumInt { sum } => {
                if !value.is_null() {
                    // Check if we need to switch to float
                    if is_float(value) {
                        // Convert to float accumulator
                        let current = sum.map(|s| s as f64);
                        let new_val = value_to_f64(value).unwrap_or(0.0);
                        *self = Accumulator::SumFloat {
                            sum: Some(current.unwrap_or(0.0) + new_val),
                        };
                    } else {
                        // Integer accumulation
                        let n = match value {
                            Value::Int16(n) => *n as i64,
                            Value::Int32(n) => *n as i64,
                            Value::Int64(n) => *n,
                            _ => {
                                return Err(ExecutorError::TypeMismatch {
                                    expected: "numeric".to_string(),
                                    found: format!("{:?}", value),
                                });
                            }
                        };
                        *sum = Some(sum.unwrap_or(0) + n);
                    }
                }
            }
            Accumulator::SumFloat { sum } => {
                if !value.is_null() {
                    if let Some(f) = value_to_f64(value) {
                        *sum = Some(sum.unwrap_or(0.0) + f);
                    } else {
                        return Err(ExecutorError::TypeMismatch {
                            expected: "numeric".to_string(),
                            found: format!("{:?}", value),
                        });
                    }
                }
            }
            Accumulator::Avg { sum, count } => {
                if !value.is_null() {
                    if let Some(f) = value_to_f64(value) {
                        *sum += f;
                        *count += 1;
                    } else {
                        return Err(ExecutorError::TypeMismatch {
                            expected: "numeric".to_string(),
                            found: format!("{:?}", value),
                        });
                    }
                }
            }
            Accumulator::Min { value: current } => {
                if !value.is_null() {
                    match current {
                        None => *current = Some(value.clone()),
                        Some(cur) => {
                            if let Ok(std::cmp::Ordering::Less) = compare_values(value, cur) {
                                *current = Some(value.clone());
                            }
                        }
                    }
                }
            }
            Accumulator::Max { value: current } => {
                if !value.is_null() {
                    match current {
                        None => *current = Some(value.clone()),
                        Some(cur) => {
                            if let Ok(std::cmp::Ordering::Greater) = compare_values(value, cur) {
                                *current = Some(value.clone());
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Finalizes the accumulator and returns the result value.
    pub fn finalize(&self) -> Value {
        match self {
            Accumulator::Count { count } => Value::Int64(*count),
            Accumulator::SumInt { sum } => match sum {
                Some(s) => Value::Int64(*s),
                None => Value::Null,
            },
            Accumulator::SumFloat { sum } => match sum {
                Some(s) => Value::Float64(*s),
                None => Value::Null,
            },
            Accumulator::Avg { sum, count } => {
                if *count == 0 {
                    Value::Null
                } else {
                    Value::Float64(*sum / *count as f64)
                }
            }
            Accumulator::Min { value } => value.clone().unwrap_or(Value::Null),
            Accumulator::Max { value } => value.clone().unwrap_or(Value::Null),
        }
    }
}

/// The Executor trait defines the Volcano-style iterator interface.
///
/// Each executor produces tuples one at a time via `next()`.
#[async_trait]
pub trait Executor: Send {
    /// Returns the next tuple, or None if exhausted.
    async fn next(&mut self) -> Result<Option<Tuple>, ExecutorError>;

    /// Returns output column metadata.
    fn schema(&self) -> &[OutputColumn];

    /// Returns EXPLAIN text for this operator.
    fn explain(&self, indent: usize) -> String;
}

/// Implement Executor for boxed trait objects.
///
/// This allows chaining executors without knowing their concrete types at compile time.
#[async_trait]
impl Executor for Box<dyn Executor> {
    async fn next(&mut self) -> Result<Option<Tuple>, ExecutorError> {
        (**self).next().await
    }

    fn schema(&self) -> &[OutputColumn] {
        (**self).schema()
    }

    fn explain(&self, indent: usize) -> String {
        (**self).explain(indent)
    }
}

/// Sequential scan of a heap table.
///
/// Iterates through all tuples in a table's heap page(s) with MVCC visibility checks.
pub struct SeqScan<S: Storage, R: Replacer> {
    /// Table name for EXPLAIN output.
    table_name: String,
    /// Output column metadata.
    output_columns: Vec<OutputColumn>,
    /// Column info from catalog (for expression evaluation).
    columns: Vec<ColumnInfo>,
    /// Type OIDs for record deserialization.
    schema: Vec<i32>,
    /// First page of the table.
    first_page: PageId,
    /// MVCC snapshot.
    snapshot: Snapshot,
    /// Buffer pool reference.
    pool: Arc<BufferPool<S, R>>,
    /// Transaction manager reference.
    tx_manager: Arc<TransactionManager>,
    /// Current position: (page_loaded, slot_index).
    /// When page_loaded is false, we haven't loaded the page yet.
    state: ScanState,
    /// Loaded tuples from current page (with visibility already checked).
    buffer: Vec<Tuple>,
    /// Current index into buffer.
    buffer_idx: usize,
}

enum ScanState {
    /// Haven't started scanning yet.
    NotStarted,
    /// Currently scanning a page.
    Scanning,
    /// Finished scanning all pages.
    Finished,
}

impl<S: Storage, R: Replacer> SeqScan<S, R> {
    /// Creates a new sequential scan executor.
    pub fn new(
        table_name: String,
        columns: Vec<ColumnInfo>,
        first_page: PageId,
        snapshot: Snapshot,
        pool: Arc<BufferPool<S, R>>,
        tx_manager: Arc<TransactionManager>,
    ) -> Self {
        let output_columns: Vec<OutputColumn> = columns
            .iter()
            .map(|c| OutputColumn::new(c.column_name.clone(), c.type_oid))
            .collect();
        let schema: Vec<i32> = columns.iter().map(|c| c.type_oid).collect();

        Self {
            table_name,
            output_columns,
            columns,
            schema,
            first_page,
            snapshot,
            pool,
            tx_manager,
            state: ScanState::NotStarted,
            buffer: Vec::new(),
            buffer_idx: 0,
        }
    }

    /// Returns the columns info for expression evaluation.
    pub fn columns(&self) -> &[ColumnInfo] {
        &self.columns
    }

    /// Loads all visible tuples from the current page into the buffer.
    async fn load_page(&mut self) -> Result<(), ExecutorError> {
        let guard = self.pool.fetch_page(self.first_page).await?;
        let page = HeapPage::new(guard.data());

        self.buffer.clear();
        self.buffer_idx = 0;

        for (_slot_id, header, record) in page.scan(&self.schema) {
            if self.snapshot.is_tuple_visible(&header, &self.tx_manager) {
                self.buffer.push(Tuple::new(record.values));
            }
        }

        Ok(())
    }
}

#[async_trait]
impl<S: Storage, R: Replacer> Executor for SeqScan<S, R> {
    async fn next(&mut self) -> Result<Option<Tuple>, ExecutorError> {
        loop {
            match self.state {
                ScanState::NotStarted => {
                    self.load_page().await?;
                    self.state = ScanState::Scanning;
                }
                ScanState::Scanning => {
                    if self.buffer_idx < self.buffer.len() {
                        let tuple = self.buffer[self.buffer_idx].clone();
                        self.buffer_idx += 1;
                        return Ok(Some(tuple));
                    }
                    // NOTE: Multi-page tables will be supported in Step 15 (FSM).
                    // For now, tables are limited to a single page.
                    self.state = ScanState::Finished;
                }
                ScanState::Finished => {
                    return Ok(None);
                }
            }
        }
    }

    fn schema(&self) -> &[OutputColumn] {
        &self.output_columns
    }

    fn explain(&self, indent: usize) -> String {
        format!("{}Seq Scan on {}", " ".repeat(indent), self.table_name)
    }
}

/// Filter executor that applies a WHERE predicate.
///
/// Wraps a child executor and only passes through tuples where the predicate
/// evaluates to TRUE.
pub struct Filter<E: Executor> {
    /// Child executor.
    child: E,
    /// Column info for expression evaluation.
    columns: Vec<ColumnInfo>,
    /// Filter predicate.
    predicate: Expr,
}

impl<E: Executor> Filter<E> {
    /// Creates a new filter executor.
    pub fn new(child: E, columns: Vec<ColumnInfo>, predicate: Expr) -> Self {
        Self {
            child,
            columns,
            predicate,
        }
    }
}

#[async_trait]
impl<E: Executor> Executor for Filter<E> {
    async fn next(&mut self) -> Result<Option<Tuple>, ExecutorError> {
        loop {
            match self.child.next().await? {
                Some(tuple) => {
                    let result = evaluate(&self.predicate, &tuple.values, &self.columns)?;
                    if is_truthy(&result) {
                        return Ok(Some(tuple));
                    }
                    // Tuple filtered out, continue to next
                }
                None => return Ok(None),
            }
        }
    }

    fn schema(&self) -> &[OutputColumn] {
        self.child.schema()
    }

    fn explain(&self, indent: usize) -> String {
        let filter_str = format_expr(&self.predicate);
        format!(
            "{}Filter: {}\n{}",
            " ".repeat(indent),
            filter_str,
            self.child.explain(indent + 2)
        )
    }
}

/// Projection executor that computes output columns from expressions.
pub struct Projection<E: Executor> {
    /// Child executor.
    child: E,
    /// Column info for expression evaluation.
    columns: Vec<ColumnInfo>,
    /// Output column definitions (expression + alias).
    output_exprs: Vec<(Expr, String)>,
    /// Output column metadata.
    output_columns: Vec<OutputColumn>,
}

impl<E: Executor> Projection<E> {
    /// Creates a new projection executor.
    pub fn new(
        child: E,
        columns: Vec<ColumnInfo>,
        output_exprs: Vec<(Expr, String)>,
        output_columns: Vec<OutputColumn>,
    ) -> Self {
        Self {
            child,
            columns,
            output_exprs,
            output_columns,
        }
    }
}

#[async_trait]
impl<E: Executor> Executor for Projection<E> {
    async fn next(&mut self) -> Result<Option<Tuple>, ExecutorError> {
        match self.child.next().await? {
            Some(tuple) => {
                let mut output_values = Vec::with_capacity(self.output_exprs.len());
                for (expr, _alias) in &self.output_exprs {
                    let val = evaluate(expr, &tuple.values, &self.columns)?;
                    output_values.push(val);
                }
                Ok(Some(Tuple::new(output_values)))
            }
            None => Ok(None),
        }
    }

    fn schema(&self) -> &[OutputColumn] {
        &self.output_columns
    }

    fn explain(&self, indent: usize) -> String {
        // For SELECT *, don't add explicit Projection in EXPLAIN
        // For other projections, show the column list
        self.child.explain(indent)
    }
}

// =============================================================================
// Sort Executor
// =============================================================================

/// Sort executor that orders tuples by specified keys.
///
/// This is a blocking executor that materializes all input tuples before sorting.
/// NOTE: For production, implement external sort for large datasets.
pub struct Sort<E: Executor> {
    /// Child executor.
    child: E,
    /// Column info for expression evaluation.
    columns: Vec<ColumnInfo>,
    /// Sort keys with direction and null ordering.
    sort_keys: Vec<SortKey>,
    /// Materialized and sorted tuples.
    sorted_tuples: Vec<Tuple>,
    /// Current position in sorted tuples.
    position: usize,
    /// Whether we've materialized and sorted the input.
    initialized: bool,
}

impl<E: Executor> Sort<E> {
    /// Creates a new sort executor.
    pub fn new(child: E, columns: Vec<ColumnInfo>, sort_keys: Vec<SortKey>) -> Self {
        Self {
            child,
            columns,
            sort_keys,
            sorted_tuples: Vec::new(),
            position: 0,
            initialized: false,
        }
    }
}

/// Compares two tuples by the sort keys.
///
/// This is a standalone function to avoid borrow checker issues with self-referential closures.
fn compare_tuples_by_keys(
    a: &Tuple,
    b: &Tuple,
    sort_keys: &[SortKey],
    columns: &[ColumnInfo],
) -> std::cmp::Ordering {
    use std::cmp::Ordering;

    for key in sort_keys {
        // Evaluate the sort expression for both tuples
        let val_a = evaluate(&key.expr, &a.values, columns).ok();
        let val_b = evaluate(&key.expr, &b.values, columns).ok();

        let a_is_null = val_a.as_ref().map(|v| v.is_null()).unwrap_or(true);
        let b_is_null = val_b.as_ref().map(|v| v.is_null()).unwrap_or(true);

        // Handle NULL ordering
        let null_ordering = key.effective_null_ordering();
        match (a_is_null, b_is_null) {
            (true, true) => continue, // Both NULL, check next key
            (true, false) => {
                return match null_ordering {
                    NullOrdering::First | NullOrdering::Default => Ordering::Less,
                    NullOrdering::Last => Ordering::Greater,
                };
            }
            (false, true) => {
                return match null_ordering {
                    NullOrdering::First | NullOrdering::Default => Ordering::Greater,
                    NullOrdering::Last => Ordering::Less,
                };
            }
            (false, false) => {
                // Compare non-NULL values
                if let (Some(va), Some(vb)) = (&val_a, &val_b) {
                    match compare_values(va, vb) {
                        Ok(ord) if ord != Ordering::Equal => {
                            return match key.direction {
                                SortDirection::Asc => ord,
                                SortDirection::Desc => ord.reverse(),
                            };
                        }
                        _ => continue, // Equal or incomparable, check next key
                    }
                }
            }
        }
    }

    Ordering::Equal
}

#[async_trait]
impl<E: Executor> Executor for Sort<E> {
    async fn next(&mut self) -> Result<Option<Tuple>, ExecutorError> {
        // Phase 1: Materialize and sort all input tuples
        if !self.initialized {
            // Collect all tuples from child
            while let Some(tuple) = self.child.next().await? {
                self.sorted_tuples.push(tuple);
            }

            // Sort the tuples
            // NOTE: For large datasets, implement external sort with tuple count limit
            let sort_keys = &self.sort_keys;
            let columns = &self.columns;
            self.sorted_tuples
                .sort_by(|a, b| compare_tuples_by_keys(a, b, sort_keys, columns));
            self.initialized = true;
        }

        // Phase 2: Return sorted tuples one at a time
        if self.position < self.sorted_tuples.len() {
            let tuple = self.sorted_tuples[self.position].clone();
            self.position += 1;
            Ok(Some(tuple))
        } else {
            Ok(None)
        }
    }

    fn schema(&self) -> &[OutputColumn] {
        self.child.schema()
    }

    fn explain(&self, indent: usize) -> String {
        let keys: Vec<String> = self
            .sort_keys
            .iter()
            .map(|k| {
                let dir = match k.direction {
                    SortDirection::Asc => "ASC",
                    SortDirection::Desc => "DESC",
                };
                let nulls = match k.effective_null_ordering() {
                    NullOrdering::First => " NULLS FIRST",
                    NullOrdering::Last => " NULLS LAST",
                    NullOrdering::Default => "",
                };
                format!("{} {}{}", format_expr(&k.expr), dir, nulls)
            })
            .collect();
        format!(
            "{}Sort: {}\n{}",
            " ".repeat(indent),
            keys.join(", "),
            self.child.explain(indent + 2)
        )
    }
}

// =============================================================================
// Aggregate Executor
// =============================================================================

/// Aggregate executor for GROUP BY and aggregate functions.
///
/// This is a blocking executor that materializes all input tuples to compute
/// group aggregations. Returns one tuple per group (or one tuple for scalar aggregation).
pub struct Aggregate<E: Executor> {
    /// Child executor.
    child: E,
    /// Column info from the source for evaluating GROUP BY expressions.
    source_columns: Vec<ColumnInfo>,
    /// GROUP BY expressions.
    group_by: Vec<Expr>,
    /// Aggregate expressions.
    aggregates: Vec<AggregateExpr>,
    /// Non-aggregate expressions (for direct column references in SELECT).
    /// NOTE: Reserved for supporting non-aggregate columns in GROUP BY queries.
    #[allow(dead_code)]
    non_agg_exprs: Vec<(Expr, String)>,
    /// HAVING clause.
    having: Option<Expr>,
    /// Output column metadata.
    output_columns: Vec<OutputColumn>,
    /// Groups with their accumulators.
    groups: HashMap<GroupKey, (Vec<Value>, Vec<Accumulator>)>,
    /// Output tuples after finalization.
    output_tuples: Vec<Tuple>,
    /// Current output position.
    output_position: usize,
    /// Whether we've processed all input and finalized.
    initialized: bool,
}

impl<E: Executor> Aggregate<E> {
    /// Creates a new aggregate executor.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        child: E,
        source_columns: Vec<ColumnInfo>,
        group_by: Vec<Expr>,
        aggregates: Vec<AggregateExpr>,
        non_agg_exprs: Vec<(Expr, String)>,
        having: Option<Expr>,
        output_columns: Vec<OutputColumn>,
    ) -> Self {
        Self {
            child,
            source_columns,
            group_by,
            aggregates,
            non_agg_exprs,
            having,
            output_columns,
            groups: HashMap::new(),
            output_tuples: Vec::new(),
            output_position: 0,
            initialized: false,
        }
    }

    /// Creates accumulators for the aggregate expressions.
    fn create_accumulators(&self) -> Vec<Accumulator> {
        self.aggregates
            .iter()
            .map(|agg| Accumulator::new(agg.function))
            .collect()
    }

    /// Processes all input tuples and computes aggregates.
    async fn process_input(&mut self) -> Result<(), ExecutorError> {
        // Collect all tuples and compute aggregates
        while let Some(tuple) = self.child.next().await? {
            // Evaluate GROUP BY expressions to get the group key
            let mut key_values = Vec::with_capacity(self.group_by.len());
            for expr in &self.group_by {
                let val = evaluate(expr, &tuple.values, &self.source_columns)?;
                key_values.push(val);
            }
            let group_key = GroupKey(key_values.clone());

            // Create accumulators outside the closure to avoid borrow issues
            let new_accumulators = self.create_accumulators();

            // Get or create the group entry
            let entry = self
                .groups
                .entry(group_key)
                .or_insert_with(|| (key_values, new_accumulators));

            // Accumulate values for each aggregate
            for (i, agg) in self.aggregates.iter().enumerate() {
                let is_count_star = agg.function == AggregateFunction::Count && agg.arg.is_none();
                let value = if let Some(ref arg_expr) = agg.arg {
                    evaluate(arg_expr, &tuple.values, &self.source_columns)?
                } else {
                    // COUNT(*) uses a dummy value
                    Value::Int32(1)
                };
                entry.1[i].accumulate(&value, is_count_star)?;
            }
        }

        // Handle scalar aggregation (no GROUP BY, but with aggregates)
        if self.group_by.is_empty() && self.groups.is_empty() {
            // Return a single row with default aggregate values
            let accumulators = self.create_accumulators();
            self.groups.insert(GroupKey(vec![]), (vec![], accumulators));
        }

        Ok(())
    }

    /// Finalizes aggregates and produces output tuples.
    fn finalize_output(&mut self) -> Result<(), ExecutorError> {
        // Build output column info for HAVING evaluation
        // The columns are: GROUP BY columns + aggregate results
        let mut having_columns = Vec::new();
        for (i, expr) in self.group_by.iter().enumerate() {
            let name = match expr {
                Expr::ColumnRef { column, .. } => column.clone(),
                _ => format!("group_{}", i),
            };
            having_columns.push(ColumnInfo::new(0, i as u32, name, type_oid::UNKNOWN, 0));
        }
        for (i, agg) in self.aggregates.iter().enumerate() {
            having_columns.push(ColumnInfo::new(
                0,
                (self.group_by.len() + i) as u32,
                agg.alias.clone(),
                type_oid::UNKNOWN,
                0,
            ));
        }

        for (key_values, accumulators) in self.groups.values() {
            // Build the tuple values: group key values + aggregate results
            let mut values: Vec<Value> = key_values.clone();
            for acc in accumulators {
                values.push(acc.finalize());
            }

            // Apply HAVING clause
            if let Some(ref having_expr) = self.having {
                let result = evaluate(having_expr, &values, &having_columns)?;
                if !is_truthy(&result) {
                    continue; // Filter out this group
                }
            }

            // Build output tuple
            // The output order matches output_columns which comes from the SELECT list
            self.output_tuples.push(Tuple::new(values));
        }

        // NOTE: The output is in arbitrary order (HashMap iteration order).
        // If ORDER BY is needed, it should be applied via a Sort executor.

        Ok(())
    }
}

#[async_trait]
impl<E: Executor> Executor for Aggregate<E> {
    async fn next(&mut self) -> Result<Option<Tuple>, ExecutorError> {
        // Phase 1: Process all input and finalize
        if !self.initialized {
            self.process_input().await?;
            self.finalize_output()?;
            self.initialized = true;
        }

        // Phase 2: Return output tuples one at a time
        if self.output_position < self.output_tuples.len() {
            let tuple = self.output_tuples[self.output_position].clone();
            self.output_position += 1;
            Ok(Some(tuple))
        } else {
            Ok(None)
        }
    }

    fn schema(&self) -> &[OutputColumn] {
        &self.output_columns
    }

    fn explain(&self, indent: usize) -> String {
        let mut parts = Vec::new();

        if !self.group_by.is_empty() {
            let keys: Vec<String> = self.group_by.iter().map(format_expr).collect();
            parts.push(format!("Group By: {}", keys.join(", ")));
        }

        if !self.aggregates.is_empty() {
            let aggs: Vec<String> = self
                .aggregates
                .iter()
                .map(|a| {
                    let arg_str = match &a.arg {
                        Some(expr) => format_expr(expr),
                        None => "*".to_string(),
                    };
                    format!("{}({})", a.function.name(), arg_str)
                })
                .collect();
            parts.push(format!("Aggregates: {}", aggs.join(", ")));
        }

        if let Some(ref having) = self.having {
            parts.push(format!("Having: {}", format_expr(having)));
        }

        format!(
            "{}Aggregate: {}\n{}",
            " ".repeat(indent),
            parts.join(", "),
            self.child.explain(indent + 2)
        )
    }
}

/// Formats an expression for EXPLAIN output.
fn format_expr(expr: &Expr) -> String {
    match expr {
        Expr::Null => "NULL".to_string(),
        Expr::Boolean(b) => b.to_string().to_uppercase(),
        Expr::Integer(n) => n.to_string(),
        Expr::Float(f) => f.to_string(),
        Expr::String(s) => format!("'{}'", s.replace('\'', "''")),
        Expr::ColumnRef { table, column } => {
            if let Some(t) = table {
                format!("{}.{}", t, column)
            } else {
                column.clone()
            }
        }
        Expr::Parameter(n) => format!("${}", n),
        Expr::BinaryOp { left, op, right } => {
            format!(
                "({} {} {})",
                format_expr(left),
                op.as_str(),
                format_expr(right)
            )
        }
        Expr::UnaryOp { op, operand } => {
            format!("{} {}", op.as_str(), format_expr(operand))
        }
        Expr::IsNull { expr, negated } => {
            if *negated {
                format!("({} IS NOT NULL)", format_expr(expr))
            } else {
                format!("({} IS NULL)", format_expr(expr))
            }
        }
        Expr::Between {
            expr,
            low,
            high,
            negated,
        } => {
            if *negated {
                format!(
                    "({} NOT BETWEEN {} AND {})",
                    format_expr(expr),
                    format_expr(low),
                    format_expr(high)
                )
            } else {
                format!(
                    "({} BETWEEN {} AND {})",
                    format_expr(expr),
                    format_expr(low),
                    format_expr(high)
                )
            }
        }
        Expr::InList {
            expr,
            list,
            negated,
        } => {
            let items: Vec<String> = list.iter().map(format_expr).collect();
            if *negated {
                format!("({} NOT IN ({}))", format_expr(expr), items.join(", "))
            } else {
                format!("({} IN ({}))", format_expr(expr), items.join(", "))
            }
        }
        _ => "<expr>".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_output_column() {
        let col = OutputColumn::new("id".to_string(), 23);
        assert_eq!(col.name, "id");
        assert_eq!(col.type_oid, 23);
    }

    #[test]
    fn test_tuple() {
        let tuple = Tuple::new(vec![Value::Int32(1), Value::Text("Alice".to_string())]);
        assert_eq!(tuple.values.len(), 2);
        assert_eq!(tuple.values[0], Value::Int32(1));
    }

    #[test]
    fn test_format_expr() {
        let expr = Expr::BinaryOp {
            left: Box::new(Expr::ColumnRef {
                table: None,
                column: "id".to_string(),
            }),
            op: crate::sql::BinaryOperator::Gt,
            right: Box::new(Expr::Integer(5)),
        };
        assert_eq!(format_expr(&expr), "(id > 5)");
    }

    #[test]
    fn test_format_expr_is_null() {
        let expr = Expr::IsNull {
            expr: Box::new(Expr::ColumnRef {
                table: None,
                column: "name".to_string(),
            }),
            negated: false,
        };
        assert_eq!(format_expr(&expr), "(name IS NULL)");

        let expr = Expr::IsNull {
            expr: Box::new(Expr::ColumnRef {
                table: None,
                column: "name".to_string(),
            }),
            negated: true,
        };
        assert_eq!(format_expr(&expr), "(name IS NOT NULL)");
    }

    // ==========================================================================
    // Sort Key Tests
    // ==========================================================================

    #[test]
    fn test_sort_key_effective_null_ordering() {
        // ASC default -> NULLS LAST
        let key = SortKey::new(Expr::Integer(1), SortDirection::Asc, NullOrdering::Default);
        assert_eq!(key.effective_null_ordering(), NullOrdering::Last);

        // DESC default -> NULLS FIRST
        let key = SortKey::new(Expr::Integer(1), SortDirection::Desc, NullOrdering::Default);
        assert_eq!(key.effective_null_ordering(), NullOrdering::First);

        // Explicit NULLS FIRST
        let key = SortKey::new(Expr::Integer(1), SortDirection::Asc, NullOrdering::First);
        assert_eq!(key.effective_null_ordering(), NullOrdering::First);

        // Explicit NULLS LAST
        let key = SortKey::new(Expr::Integer(1), SortDirection::Desc, NullOrdering::Last);
        assert_eq!(key.effective_null_ordering(), NullOrdering::Last);
    }

    // ==========================================================================
    // Aggregate Function Tests
    // ==========================================================================

    #[test]
    fn test_aggregate_function_from_name() {
        assert_eq!(AggregateFunction::from_name("count"), Some(AggregateFunction::Count));
        assert_eq!(AggregateFunction::from_name("COUNT"), Some(AggregateFunction::Count));
        assert_eq!(AggregateFunction::from_name("sum"), Some(AggregateFunction::Sum));
        assert_eq!(AggregateFunction::from_name("avg"), Some(AggregateFunction::Avg));
        assert_eq!(AggregateFunction::from_name("min"), Some(AggregateFunction::Min));
        assert_eq!(AggregateFunction::from_name("max"), Some(AggregateFunction::Max));
        assert_eq!(AggregateFunction::from_name("unknown"), None);
    }

    #[test]
    fn test_aggregate_function_name() {
        assert_eq!(AggregateFunction::Count.name(), "count");
        assert_eq!(AggregateFunction::Sum.name(), "sum");
        assert_eq!(AggregateFunction::Avg.name(), "avg");
        assert_eq!(AggregateFunction::Min.name(), "min");
        assert_eq!(AggregateFunction::Max.name(), "max");
    }

    // ==========================================================================
    // GroupKey Tests
    // ==========================================================================

    #[test]
    fn test_group_key_equality() {
        // Same values should be equal
        let key1 = GroupKey(vec![Value::Int32(1), Value::Text("a".to_string())]);
        let key2 = GroupKey(vec![Value::Int32(1), Value::Text("a".to_string())]);
        assert_eq!(key1, key2);

        // Different values should not be equal
        let key3 = GroupKey(vec![Value::Int32(2), Value::Text("a".to_string())]);
        assert_ne!(key1, key3);

        // NULL = NULL for grouping
        let key4 = GroupKey(vec![Value::Null]);
        let key5 = GroupKey(vec![Value::Null]);
        assert_eq!(key4, key5);
    }

    #[test]
    fn test_group_key_hash_consistency() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::Hash;

        fn hash<T: Hash>(t: &T) -> u64 {
            let mut hasher = DefaultHasher::new();
            t.hash(&mut hasher);
            hasher.finish()
        }

        // Equal keys should have equal hashes
        let key1 = GroupKey(vec![Value::Int32(42)]);
        let key2 = GroupKey(vec![Value::Int32(42)]);
        assert_eq!(hash(&key1), hash(&key2));

        // Float hashing uses bit representation
        let key3 = GroupKey(vec![Value::Float64(3.14)]);
        let key4 = GroupKey(vec![Value::Float64(3.14)]);
        assert_eq!(hash(&key3), hash(&key4));
    }

    // ==========================================================================
    // Accumulator Tests
    // ==========================================================================

    #[test]
    fn test_accumulator_count() {
        let mut acc = Accumulator::new(AggregateFunction::Count);

        // COUNT(*) counts all rows
        acc.accumulate(&Value::Int32(1), true).unwrap();
        acc.accumulate(&Value::Null, true).unwrap();
        acc.accumulate(&Value::Int32(3), true).unwrap();
        assert_eq!(acc.finalize(), Value::Int64(3));

        // COUNT(expr) skips NULLs
        let mut acc2 = Accumulator::new(AggregateFunction::Count);
        acc2.accumulate(&Value::Int32(1), false).unwrap();
        acc2.accumulate(&Value::Null, false).unwrap();
        acc2.accumulate(&Value::Int32(3), false).unwrap();
        assert_eq!(acc2.finalize(), Value::Int64(2));
    }

    #[test]
    fn test_accumulator_count_empty() {
        let acc = Accumulator::new(AggregateFunction::Count);
        assert_eq!(acc.finalize(), Value::Int64(0));
    }

    #[test]
    fn test_accumulator_sum_integers() {
        let mut acc = Accumulator::new(AggregateFunction::Sum);
        acc.accumulate(&Value::Int32(10), false).unwrap();
        acc.accumulate(&Value::Int32(20), false).unwrap();
        acc.accumulate(&Value::Int32(30), false).unwrap();
        assert_eq!(acc.finalize(), Value::Int64(60));
    }

    #[test]
    fn test_accumulator_sum_with_nulls() {
        let mut acc = Accumulator::new(AggregateFunction::Sum);
        acc.accumulate(&Value::Int32(10), false).unwrap();
        acc.accumulate(&Value::Null, false).unwrap();
        acc.accumulate(&Value::Int32(20), false).unwrap();
        assert_eq!(acc.finalize(), Value::Int64(30));
    }

    #[test]
    fn test_accumulator_sum_all_nulls() {
        let mut acc = Accumulator::new(AggregateFunction::Sum);
        acc.accumulate(&Value::Null, false).unwrap();
        acc.accumulate(&Value::Null, false).unwrap();
        assert_eq!(acc.finalize(), Value::Null);
    }

    #[test]
    fn test_accumulator_sum_floats() {
        let mut acc = Accumulator::new(AggregateFunction::Sum);
        acc.accumulate(&Value::Float64(1.5), false).unwrap();
        acc.accumulate(&Value::Float64(2.5), false).unwrap();
        assert_eq!(acc.finalize(), Value::Float64(4.0));
    }

    #[test]
    fn test_accumulator_sum_mixed_types() {
        let mut acc = Accumulator::new(AggregateFunction::Sum);
        acc.accumulate(&Value::Int32(10), false).unwrap();
        acc.accumulate(&Value::Float64(2.5), false).unwrap();
        // After seeing a float, switches to float accumulator
        assert_eq!(acc.finalize(), Value::Float64(12.5));
    }

    #[test]
    fn test_accumulator_avg() {
        let mut acc = Accumulator::new(AggregateFunction::Avg);
        acc.accumulate(&Value::Int32(10), false).unwrap();
        acc.accumulate(&Value::Int32(20), false).unwrap();
        acc.accumulate(&Value::Int32(30), false).unwrap();
        assert_eq!(acc.finalize(), Value::Float64(20.0));
    }

    #[test]
    fn test_accumulator_avg_with_nulls() {
        let mut acc = Accumulator::new(AggregateFunction::Avg);
        acc.accumulate(&Value::Int32(10), false).unwrap();
        acc.accumulate(&Value::Null, false).unwrap();
        acc.accumulate(&Value::Int32(20), false).unwrap();
        // AVG(10, 20) = 15, NULL is skipped
        assert_eq!(acc.finalize(), Value::Float64(15.0));
    }

    #[test]
    fn test_accumulator_avg_empty() {
        let acc = Accumulator::new(AggregateFunction::Avg);
        assert_eq!(acc.finalize(), Value::Null);
    }

    #[test]
    fn test_accumulator_min() {
        let mut acc = Accumulator::new(AggregateFunction::Min);
        acc.accumulate(&Value::Int32(30), false).unwrap();
        acc.accumulate(&Value::Int32(10), false).unwrap();
        acc.accumulate(&Value::Int32(20), false).unwrap();
        assert_eq!(acc.finalize(), Value::Int32(10));
    }

    #[test]
    fn test_accumulator_min_with_nulls() {
        let mut acc = Accumulator::new(AggregateFunction::Min);
        acc.accumulate(&Value::Int32(30), false).unwrap();
        acc.accumulate(&Value::Null, false).unwrap();
        acc.accumulate(&Value::Int32(10), false).unwrap();
        assert_eq!(acc.finalize(), Value::Int32(10));
    }

    #[test]
    fn test_accumulator_min_all_nulls() {
        let mut acc = Accumulator::new(AggregateFunction::Min);
        acc.accumulate(&Value::Null, false).unwrap();
        acc.accumulate(&Value::Null, false).unwrap();
        assert_eq!(acc.finalize(), Value::Null);
    }

    #[test]
    fn test_accumulator_max() {
        let mut acc = Accumulator::new(AggregateFunction::Max);
        acc.accumulate(&Value::Int32(10), false).unwrap();
        acc.accumulate(&Value::Int32(30), false).unwrap();
        acc.accumulate(&Value::Int32(20), false).unwrap();
        assert_eq!(acc.finalize(), Value::Int32(30));
    }

    #[test]
    fn test_accumulator_max_text() {
        let mut acc = Accumulator::new(AggregateFunction::Max);
        acc.accumulate(&Value::Text("apple".to_string()), false).unwrap();
        acc.accumulate(&Value::Text("cherry".to_string()), false).unwrap();
        acc.accumulate(&Value::Text("banana".to_string()), false).unwrap();
        assert_eq!(acc.finalize(), Value::Text("cherry".to_string()));
    }

    // ==========================================================================
    // Tuple Comparison Tests
    // ==========================================================================

    #[test]
    fn test_compare_tuples_single_key_asc() {
        let columns = vec![ColumnInfo::new(1, 0, "id".to_string(), 23, 0)];
        let sort_keys = vec![SortKey::new(
            Expr::ColumnRef { table: None, column: "id".to_string() },
            SortDirection::Asc,
            NullOrdering::Default,
        )];

        let tuple1 = Tuple::new(vec![Value::Int32(1)]);
        let tuple2 = Tuple::new(vec![Value::Int32(2)]);
        let tuple3 = Tuple::new(vec![Value::Int32(1)]);

        assert_eq!(
            compare_tuples_by_keys(&tuple1, &tuple2, &sort_keys, &columns),
            std::cmp::Ordering::Less
        );
        assert_eq!(
            compare_tuples_by_keys(&tuple2, &tuple1, &sort_keys, &columns),
            std::cmp::Ordering::Greater
        );
        assert_eq!(
            compare_tuples_by_keys(&tuple1, &tuple3, &sort_keys, &columns),
            std::cmp::Ordering::Equal
        );
    }

    #[test]
    fn test_compare_tuples_single_key_desc() {
        let columns = vec![ColumnInfo::new(1, 0, "id".to_string(), 23, 0)];
        let sort_keys = vec![SortKey::new(
            Expr::ColumnRef { table: None, column: "id".to_string() },
            SortDirection::Desc,
            NullOrdering::Default,
        )];

        let tuple1 = Tuple::new(vec![Value::Int32(1)]);
        let tuple2 = Tuple::new(vec![Value::Int32(2)]);

        // DESC reverses the ordering
        assert_eq!(
            compare_tuples_by_keys(&tuple1, &tuple2, &sort_keys, &columns),
            std::cmp::Ordering::Greater
        );
        assert_eq!(
            compare_tuples_by_keys(&tuple2, &tuple1, &sort_keys, &columns),
            std::cmp::Ordering::Less
        );
    }

    #[test]
    fn test_compare_tuples_nulls_last() {
        let columns = vec![ColumnInfo::new(1, 0, "id".to_string(), 23, 0)];
        let sort_keys = vec![SortKey::new(
            Expr::ColumnRef { table: None, column: "id".to_string() },
            SortDirection::Asc,
            NullOrdering::Last,
        )];

        let tuple_null = Tuple::new(vec![Value::Null]);
        let tuple_value = Tuple::new(vec![Value::Int32(1)]);

        // With NULLS LAST, NULL comes after non-NULL
        assert_eq!(
            compare_tuples_by_keys(&tuple_null, &tuple_value, &sort_keys, &columns),
            std::cmp::Ordering::Greater
        );
        assert_eq!(
            compare_tuples_by_keys(&tuple_value, &tuple_null, &sort_keys, &columns),
            std::cmp::Ordering::Less
        );
    }

    #[test]
    fn test_compare_tuples_nulls_first() {
        let columns = vec![ColumnInfo::new(1, 0, "id".to_string(), 23, 0)];
        let sort_keys = vec![SortKey::new(
            Expr::ColumnRef { table: None, column: "id".to_string() },
            SortDirection::Asc,
            NullOrdering::First,
        )];

        let tuple_null = Tuple::new(vec![Value::Null]);
        let tuple_value = Tuple::new(vec![Value::Int32(1)]);

        // With NULLS FIRST, NULL comes before non-NULL
        assert_eq!(
            compare_tuples_by_keys(&tuple_null, &tuple_value, &sort_keys, &columns),
            std::cmp::Ordering::Less
        );
        assert_eq!(
            compare_tuples_by_keys(&tuple_value, &tuple_null, &sort_keys, &columns),
            std::cmp::Ordering::Greater
        );
    }

    #[test]
    fn test_compare_tuples_multiple_keys() {
        let columns = vec![
            ColumnInfo::new(1, 0, "dept".to_string(), 25, 0),
            ColumnInfo::new(1, 1, "name".to_string(), 25, 0),
        ];
        let sort_keys = vec![
            SortKey::new(
                Expr::ColumnRef { table: None, column: "dept".to_string() },
                SortDirection::Asc,
                NullOrdering::Default,
            ),
            SortKey::new(
                Expr::ColumnRef { table: None, column: "name".to_string() },
                SortDirection::Asc,
                NullOrdering::Default,
            ),
        ];

        // Same dept, different name
        let tuple1 = Tuple::new(vec![
            Value::Text("A".to_string()),
            Value::Text("Alice".to_string()),
        ]);
        let tuple2 = Tuple::new(vec![
            Value::Text("A".to_string()),
            Value::Text("Bob".to_string()),
        ]);

        // Should compare by second key when first is equal
        assert_eq!(
            compare_tuples_by_keys(&tuple1, &tuple2, &sort_keys, &columns),
            std::cmp::Ordering::Less
        );

        // Different dept, same name
        let tuple3 = Tuple::new(vec![
            Value::Text("B".to_string()),
            Value::Text("Alice".to_string()),
        ]);

        // Should compare by first key
        assert_eq!(
            compare_tuples_by_keys(&tuple1, &tuple3, &sort_keys, &columns),
            std::cmp::Ordering::Less
        );
    }
}
