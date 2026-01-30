//! SQL parsing module.
//!
//! This module provides a handwritten recursive descent parser that converts
//! SQL strings into an Abstract Syntax Tree (AST) for query processing.

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
