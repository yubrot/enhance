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
//! [ExecutorNode::build] -- materializes Plan into ExecutorNode
//!       |
//! ExecutorNode tree (with data):
//!   Projection
//!     └── Filter
//!           └── SeqScan (lazily loads visible tuples page-by-page)
//! ```
//!
//! # Components
//!
//! - [`planner::plan_select`]: Transforms a SELECT AST into a logical Plan
//! - [`ExecutorNode::build`]: Materializes a Plan into an ExecutorNode tree
//! - [`Plan`]: Logical query plan (no data)
//! - [`ExecutorNode`]: Physical executor nodes with async `next()` (Volcano model)
//! - [`Plan::explain`]: EXPLAIN output from logical Plan
//! - [`expr::BoundExpr`]: Bound expression tree with compile-time column resolution
//! - [`ColumnDesc`]: Output column metadata

mod context;
mod error;
mod eval;
mod expr;
mod node;
mod plan;
mod planner;
mod row;

use crate::datum::Type;

pub use context::{ExecContext, ExecContextImpl};
pub use error::ExecutorError;
pub use expr::BoundExpr;
pub use node::ExecutorNode;
pub use plan::Plan;
pub use planner::plan_select;
pub use row::Row;

/// Metadata describing a result column.
#[derive(Debug, Clone)]
pub struct ColumnDesc {
    /// Column name (or alias).
    pub name: String,
    /// Source table name (if from a table, for qualified column resolution).
    pub table_name: Option<String>,
    /// OID of the source table (0 if not from a table).
    pub table_oid: i32,
    /// Column attribute number within the source table (0 if not from a table).
    pub column_id: i16,
    /// Data type.
    pub data_type: Type,
}

impl ColumnDesc {
    /// Returns the display name for this column.
    ///
    /// If the column has a source table name, returns `table.column`,
    /// otherwise returns just the column name.
    pub fn display_name(&self) -> String {
        match &self.table_name {
            Some(t) => format!("{}.{}", t, self.name),
            None => self.name.clone(),
        }
    }
}
