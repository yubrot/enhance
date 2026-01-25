//! SQL parsing module.
//!
//! This module provides a SQL parser for the enhance RDBMS. It converts SQL strings
//! into an Abstract Syntax Tree (AST) that can be processed by the query planner
//! and executor.
//!
//! # Example
//!
//! ```
//! use enhance::sql::{Parser, Statement};
//!
//! let sql = "SELECT id, name FROM users WHERE active = TRUE";
//! let mut parser = Parser::new(sql);
//! let statement = parser.parse().unwrap().unwrap();
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
mod lexer;
mod parser;
mod token;

pub use ast::*;
pub use error::{Span, SyntaxError};
pub use lexer::Lexer;
pub use parser::Parser;
pub use token::{Token, TokenKind};
