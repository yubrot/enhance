//! Bound expression tree with compile-time column resolution.
//!
//! [`BoundExpr`] is the executor's internal representation of SQL expressions.
//! Unlike the AST [`Expr`](crate::sql::Expr), column references are resolved
//! to positional indices at bind time, enabling O(1) access during evaluation.

use crate::datum::Type;
use crate::sql::{BinaryOperator, UnaryOperator};

/// An expression tree with column references resolved to positional indices.
///
/// Unlike the AST [`Expr`](crate::sql::Expr), `BoundExpr` replaces
/// `ColumnRef { table, column }` with `Column(usize)`, enabling O(1) column
/// access during evaluation instead of O(n) name matching on every row.
#[derive(Debug, Clone)]
pub enum BoundExpr {
    /// NULL literal.
    Null,
    /// Boolean literal.
    Boolean(bool),
    /// Integer literal.
    Integer(i64),
    /// Float literal.
    Float(f64),
    /// String literal.
    String(String),
    /// Column reference resolved to a positional index.
    Column(usize),
    /// Binary operation.
    BinaryOp {
        left: Box<BoundExpr>,
        op: BinaryOperator,
        right: Box<BoundExpr>,
    },
    /// Unary operation.
    UnaryOp {
        op: UnaryOperator,
        operand: Box<BoundExpr>,
    },
    /// IS [NOT] NULL test.
    IsNull {
        expr: Box<BoundExpr>,
        negated: bool,
    },
    /// IN list test.
    InList {
        expr: Box<BoundExpr>,
        list: Vec<BoundExpr>,
        negated: bool,
    },
    /// BETWEEN range test.
    Between {
        expr: Box<BoundExpr>,
        low: Box<BoundExpr>,
        high: Box<BoundExpr>,
        negated: bool,
    },
    /// LIKE / ILIKE pattern matching.
    Like {
        expr: Box<BoundExpr>,
        pattern: Box<BoundExpr>,
        escape: Option<Box<BoundExpr>>,
        negated: bool,
        case_insensitive: bool,
    },
    /// CASE expression (searched or simple).
    Case {
        operand: Option<Box<BoundExpr>>,
        when_clauses: Vec<BoundWhenClause>,
        else_result: Option<Box<BoundExpr>>,
    },
    /// CAST expression.
    Cast {
        expr: Box<BoundExpr>,
        data_type: Type,
    },
}

/// A WHEN clause in a bound CASE expression.
#[derive(Debug, Clone)]
pub struct BoundWhenClause {
    /// Condition (searched CASE) or comparison value (simple CASE).
    pub condition: BoundExpr,
    /// Result expression when the condition matches.
    pub result: BoundExpr,
}
