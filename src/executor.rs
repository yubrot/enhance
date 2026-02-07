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
//! [Planner] -- resolves tables via Catalog, produces logical Plan
//!       |
//! Plan tree (no data):
//!   Projection
//!     └── Filter
//!           └── SeqScan
//!       |
//! [build_executor] -- materializes Plan into ExecutorNode
//!       |
//! ExecutorNode tree (with data):
//!   Projection
//!     └── Filter
//!           └── SeqScan (pre-loads visible tuples from heap page)
//! ```
//!
//! # Components
//!
//! - [`planner::plan_select`]: Transforms a SELECT AST into a logical Plan
//! - [`planner::build_executor`]: Materializes a Plan into an ExecutorNode tree
//! - [`Plan`]: Logical query plan (no data)
//! - [`ExecutorNode`]: Physical executor nodes with async `next()` (Volcano model)
//! - [`explain::explain_plan`]: EXPLAIN output from logical Plan
//! - [`eval::BoundExpr`]: Bound expression tree with compile-time column resolution
//! - [`ColumnDesc`]: Output column metadata
//! - [`Tuple`]: A single result tuple with optional physical location

mod error;
mod eval;
mod explain;
mod node;
mod plan;
mod planner;
mod types;

pub use error::ExecutorError;
pub use eval::{bind_expr, format_bound_expr, BoundExpr};
pub use explain::explain_plan;
pub use node::ExecutorNode;
pub use plan::Plan;
pub use planner::{build_executor, plan_select};
pub use types::{ColumnDesc, Tuple, TupleId};
