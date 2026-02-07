//! Query executor implementing the Volcano iterator model.
//!
//! This module provides the execution engine that evaluates SQL queries
//! against heap-stored data with MVCC visibility checks.
//!
//! # Architecture
//!
//! ```text
//! +------------------------+
//! |    AST (SelectStmt)    |  <- Expr: column names as strings
//! +-----------+------------+
//!             | plan_select (resolves tables, binds Expr to BoundExpr)
//!             v
//! +------------------------+
//! |          Plan          |  <- BoundExpr: column names resolved to indices
//! |  Projection            |
//! |    └── Filter          |
//! |          └── SeqScan   |
//! +-----------+------------+
//!             | ExecutorNode::build (converts Plan into ExecutorNode)
//!             v
//! +------------------------+
//! |      ExecutorNode      |  <- Physical tree (lazy page I/O via next())
//! |  Projection            |
//! |    └── Filter          |
//! |          └── SeqScan   |
//! +------------------------+
//! ```
//!
//! # Components
//!
//! - [`Plan`]: Logical query plan (no data)
//! - [`ExecutorNode`]: Physical executor nodes with async `next()` (Volcano model)
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

/// Source table metadata for columns originating from a table scan.
#[derive(Debug, Clone)]
pub struct ColumnSource {
    /// Source table name (for qualified column resolution).
    pub table_name: String,
    /// OID of the source table.
    pub table_oid: u32,
    /// Column attribute number within the source table (1-indexed).
    pub column_id: i16,
}

/// Metadata describing a result column.
#[derive(Debug, Clone)]
pub struct ColumnDesc {
    /// Column name (or alias).
    pub name: String,
    /// Source table info. `None` for computed/expression columns.
    pub source: Option<ColumnSource>,
    /// Data type.
    pub data_type: Type,
}

impl ColumnDesc {
    /// Returns the display name for this column.
    ///
    /// If the column has a source table, returns `table.column`,
    /// otherwise returns just the column name.
    pub fn display_name(&self) -> String {
        match &self.source {
            Some(s) => format!("{}.{}", s.table_name, self.name),
            None => self.name.clone(),
        }
    }
}
