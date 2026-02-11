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
pub use context::{ExecContext, ExecContextImpl};
pub use error::ExecutorError;
pub use expr::BoundExpr;
pub use plan::{DmlPlan, QueryPlan};
pub use planner::{plan_delete, plan_insert, plan_select, plan_update};
pub use row::Row;
pub use runner::{DmlResult, QueryNode};
