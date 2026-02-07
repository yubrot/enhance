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
//! - [`eval::BoundExpr`]: Bound expression tree with compile-time column resolution
//! - [`ColumnDesc`]: Output column metadata
//! - [`Tuple`]: A single result tuple with optional physical location

mod error;
mod eval;
mod node;
mod planner;
mod types;

pub use error::ExecutorError;
pub use eval::{bind_expr, format_bound_expr, BoundExpr};
pub use node::ExecutorNode;
pub use planner::plan_select;
pub use types::{ColumnDesc, Tuple, TupleId};
