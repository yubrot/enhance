//! Query executor implementing the Volcano iterator model.
//!
//! This module provides the execution engine that evaluates SQL queries
//! against heap-stored data with MVCC visibility checks.
//!
//! # Architecture
//!
//! ```text
//! AST (SelectStmt)
//!       |
//! [Planner] -- resolves tables via Catalog, builds executor tree
//!       |
//! ExecutorNode tree:
//!   Projection
//!     └── Filter
//!           └── SeqScan (pre-loads visible tuples from heap page)
//! ```
//!
//! # Components
//!
//! - [`planner::plan_select`]: Transforms a SELECT AST into an executor node tree
//! - [`ExecutorNode`]: Enum-dispatched executor nodes (SeqScan, Filter, Projection, ValuesScan)
//! - [`eval::eval_expr`]: Expression evaluator for WHERE/SELECT expressions
//! - [`ColumnDesc`]: Output column metadata
//! - [`Row`]: A single result row

mod error;
mod eval;
mod node;
mod planner;
mod types;

pub use error::ExecutorError;
pub use node::ExecutorNode;
pub use planner::plan_select;
pub use types::{ColumnDesc, Row};
