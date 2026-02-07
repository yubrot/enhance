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
pub use planner::plan_select;
pub use row::Row;
