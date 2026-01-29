//! Query executor for processing SQL statements.
//!
//! This module implements the Volcano-style iterator model for query execution.
//! Each plan node provides a `next()` method that returns one tuple at a time,
//! enabling efficient pipelined execution without materializing intermediate results.
//!
//! # Architecture
//!
//! The executor consists of:
//!
//! - **Plan nodes** ([`plan`]): Executable operators (SeqScan, Filter, Projection)
//! - **Planner** ([`planner`]): Converts SQL AST to execution plan
//! - **Expression evaluation** ([`value`]): Evaluates SQL expressions with NULL handling
//! - **Execution context** ([`context`]): Provides access to MVCC, catalog, and storage
//! - **DML operations** ([`dml`]): INSERT, UPDATE, DELETE with MVCC support
//!
//! # Example
//!
//! ```ignore
//! let snapshot = tx_manager.snapshot(txid, cid);
//! let mut executor = plan_select(&stmt, snapshot, catalog, pool, tx_manager).await?;
//!
//! while let Some(tuple) = executor.next().await? {
//!     // Process tuple
//! }
//! ```
//!
//! # MVCC Integration
//!
//! All scan operators check tuple visibility using the MVCC snapshot. Only tuples
//! that are visible according to READ COMMITTED isolation rules are returned.
//!
//! # Limitations (Current Step)
//!
//! - Single-page tables only (multi-page support in Step 15)
//! - No optimization (rule-based planner in Step 17)
//! - No aggregation (Step 12)
//! - No joins (Step 19)

mod context;
mod dml;
mod error;
mod plan;
mod planner;
mod value;

pub use context::ExecutionContext;
pub use dml::{
    execute_delete, execute_insert, execute_update, DeleteResult, InsertResult, UpdateResult,
};
pub use error::ExecutorError;
pub use plan::{Executor, Filter, OutputColumn, Projection, SeqScan, Tuple};
pub use planner::plan_select;
pub use value::{coerce_to_type, evaluate, is_truthy};
