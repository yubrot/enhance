//! Query planning and execution engine.
//!
//! This module translates AST nodes into logical plans ([`QueryPlan`] / [`DmlPlan`]),
//! then executes them against heap-stored data with MVCC visibility checks.
//! Row-producing queries use the Volcano iterator model ([`QueryNode`]);
//! DML operations drive the iterator internally and return a scalar result ([`DmlResult`]).
//!
//! # Architecture
//!
//! ```text
//! +------------------------+
//! |    AST (Statement)     |  <- Expr: column names as strings
//! +-----------+------------+
//!             | plan_select / plan_insert / plan_update / plan_delete
//!             v
//! +------------------------+       +------------------------+
//! |       QueryPlan        |       |        DmlPlan         |
//! |  Projection            |       |  Insert / Update /     |
//! |    └── Filter          |       |  Delete                |
//! |          └── SeqScan   |       +----------+-------------+
//! +-----------+------------+                  |
//!             | prepare_for_execute()         | execute_dml() -> DmlResult
//!             v                               v
//! +------------------------+       +------------------------+
//! |      QueryNode         |       |       DmlResult        |
//! |  (lazy page I/O)       |       |  (affected row count)  |
//! +------------------------+       +------------------------+
//! ```
//!
//! # Components
//!
//! - [`QueryPlan`]: Logical query plan for row-producing operations (no data)
//! - [`QueryNode`]: Physical executor nodes with async `next()` (Volcano model)
//! - [`DmlPlan`]: Logical plan for data-modifying operations (INSERT/UPDATE/DELETE)
//! - [`DmlResult`]: Result of executing a DML plan (affected row count + command tag)
//! - [`ExecContext`]: Trait providing catalog/heap/transaction access to executor nodes
//! - [`Row`]: A single row produced by executor nodes (record + optional physical location)
//! - [`ColumnDesc`]: Metadata describing a result column (name, type, source table info)

mod column;
mod context;
mod error;
mod eval;
mod expr;
mod plan;
mod planner;
mod row;
mod runner;

pub use column::{ColumnDesc, ColumnSource};
pub use context::ExecContext;
pub use error::ExecutorError;
pub use expr::BoundExpr;
pub use plan::{DmlPlan, QueryPlan};
pub use planner::{plan_delete, plan_insert, plan_select, plan_update};
pub use row::Row;
pub use runner::{DmlResult, QueryNode};

/// Test helpers for executor-layer tests used across multiple test modules.
#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::datum::Type;
    use crate::sql::tests::parse_expr;

    /// Parses and binds a SQL expression against the given column descriptors.
    ///
    /// # Panics
    ///
    /// Panics if parsing or binding fails.
    pub fn bind_expr(sql: &str, columns: &[ColumnDesc]) -> BoundExpr {
        parse_expr(sql).bind(columns).expect("bind error")
    }

    /// Creates a [`ColumnDesc`] with `Type::Bigint` and no source table.
    pub fn int_col(name: &str) -> ColumnDesc {
        ColumnDesc {
            name: name.to_string(),
            source: None,
            ty: Type::Bigint,
        }
    }
}
