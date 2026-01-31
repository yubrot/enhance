//! Query executor module.
//!
//! This module implements the Volcano-style iterator model for query execution.
//! The executor processes queries by building a tree of operators that produce
//! tuples on demand via the `next()` method.
//!
//! # Architecture
//!
//! - [`BoundExpr`]: Expressions with column references resolved to indices
//! - [`Plan`]: Query execution plan (tree of operators)
//! - [`Executor`]: Runtime executor that iterates through tuples
//! - [`Planner`]: Converts AST to Plan, resolving names and types
//!
//! # Example Flow
//!
//! ```text
//! SQL → Parser → AST → Planner → Plan → Executor → Tuples
//! ```

mod error;
mod explain;
mod expr;
mod plan;
mod planner;
mod runtime;
mod tuple;

pub use error::ExecutorError;
pub use explain::explain_plan;
pub use expr::BoundExpr;
pub use plan::{ColumnDesc, Plan};
pub use planner::Planner;
pub use runtime::{ExecutionContext, Executor};
pub use tuple::{Tuple, TupleId};
