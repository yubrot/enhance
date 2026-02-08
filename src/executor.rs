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
//!             | Plan::prepare_for_execute() (converts Plan into ExecutorNode)
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
//! - [`ExecContext`]: Trait providing catalog/heap/transaction access to executor nodes
//! - [`Row`]: A single row produced by executor nodes (record + optional physical location)
//! - [`ColumnDesc`]: Metadata describing a result column (name, type, source table info)

mod column;
mod context;
mod error;
mod eval;
mod expr;
mod node;
mod plan;
mod planner;
mod row;

pub use column::{ColumnDesc, ColumnSource};
pub use context::{ExecContext, ExecContextImpl};
pub use error::ExecutorError;
pub use expr::BoundExpr;
pub use node::ExecutorNode;
pub use plan::Plan;
pub use planner::{plan_delete, plan_insert, plan_select, plan_update};
pub use row::Row;
