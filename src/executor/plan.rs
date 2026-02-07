//! Logical query plan representation.
//!
//! A [`Plan`] describes *what* to execute without loading any data.
//! It is produced by the planner and then materialized into an
//! [`ExecutorNode`](super::node::ExecutorNode) by [`build_executor`](super::planner::build_executor).

use crate::datum::Type;
use crate::storage::PageId;

use super::expr::BoundExpr;
use super::ColumnDesc;

/// A logical query plan node.
///
/// Unlike [`ExecutorNode`](super::node::ExecutorNode), a `Plan` contains no
/// pre-loaded data — only the metadata needed to describe the scan, filter,
/// and projection operations.
pub enum Plan {
    /// Sequential heap scan targeting a single table.
    SeqScan {
        /// Table name (for EXPLAIN output).
        table_name: String,
        /// Catalog table ID.
        table_id: u32,
        /// First heap page to scan.
        first_page: PageId,
        /// Column data types for record deserialization.
        schema: Vec<Type>,
        /// Output column descriptors.
        columns: Vec<ColumnDesc>,
    },
    /// Tuple filter (WHERE clause).
    Filter {
        /// Child plan to pull tuples from.
        input: Box<Plan>,
        /// Bound predicate expression.
        predicate: BoundExpr,
    },
    /// Column projection (SELECT list).
    Projection {
        /// Child plan to pull tuples from.
        input: Box<Plan>,
        /// Bound expressions to evaluate for each output column.
        exprs: Vec<BoundExpr>,
        /// Output column descriptors.
        columns: Vec<ColumnDesc>,
    },
    /// Single-row scan for queries without FROM (e.g., `SELECT 1+1`).
    ValuesScan,
}

impl Plan {
    /// Returns the output column descriptors for this plan node.
    pub fn columns(&self) -> &[ColumnDesc] {
        match self {
            Plan::SeqScan { columns, .. } => columns,
            Plan::Filter { input, .. } => input.columns(),
            Plan::Projection { columns, .. } => columns,
            Plan::ValuesScan => &[],
        }
    }
}
