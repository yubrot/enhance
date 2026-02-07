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
//! - [`expr::BoundExpr`]: Bound expression tree with compile-time column resolution
//! - [`ColumnDesc`]: Output column metadata

mod error;
mod eval;
mod explain;
mod expr;
mod node;
mod plan;
mod planner;

use crate::datum::Type;

pub use error::ExecutorError;
pub use eval::{bind_expr, format_bound_expr};
pub use expr::BoundExpr;
pub use explain::explain_plan;
pub use node::ExecutorNode;
pub use plan::Plan;
pub use planner::{build_executor, plan_select};

/// Metadata describing a result column.
#[derive(Debug, Clone)]
pub struct ColumnDesc {
    /// Column name (or alias).
    pub name: String,
    /// OID of the source table (0 if not from a table).
    pub table_oid: i32,
    /// Column attribute number within the source table (0 if not from a table).
    pub column_id: i16,
    /// Data type.
    pub data_type: Type,
}
