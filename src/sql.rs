//! SQL parsing module.
//!
//! This module provides a SQL parser for the enhance RDBMS. It converts SQL strings
//! into an Abstract Syntax Tree (AST) that can be processed by the query planner
//! and executor.
//!
//! # Supported Statements
//!
//! - `CREATE TABLE` - with column definitions and constraints
//! - `SELECT` - with FROM, WHERE, GROUP BY, HAVING, ORDER BY, LIMIT/OFFSET
//! - `INSERT` - with column list and VALUES
//! - `UPDATE` - with SET and WHERE
//! - `DELETE` - with WHERE
//! - `BEGIN`/`START TRANSACTION`, `COMMIT`, `ROLLBACK`
//! - `SET` - session variable assignment
//! - `EXPLAIN` - query plan visualization
//!
//! # Example
//!
//! ```
//! use enhance::sql::{Parser, Statement};
//!
//! let sql = "SELECT id, name FROM users WHERE active = TRUE";
//! let mut parser = Parser::new(sql);
//! let statement = parser.parse().unwrap();
//!
//! match statement {
//!     Statement::Select(select) => {
//!         assert_eq!(select.columns.len(), 2);
//!     }
//!     _ => panic!("expected SELECT"),
//! }
//! ```

mod ast;
mod error;
mod expr;
mod lexer;
mod parser;
mod token;

pub use ast::*;
pub use error::{ParseError, ParseErrorKind, Span};
pub use lexer::Lexer;
pub use parser::Parser;
pub use token::{Keyword, Token, TokenKind};
