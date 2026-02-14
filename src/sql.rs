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

/// Test helpers for SQL parsing used across multiple test modules.
#[cfg(test)]
pub mod tests {
    use super::*;

    /// Parses a SQL expression string into an AST [`Expr`].
    ///
    /// # Panics
    ///
    /// Panics if parsing fails.
    pub fn parse_expr(sql: &str) -> Expr {
        Parser::new(sql).parse_expr().expect("parse error")
    }

    /// Parses a SQL string and extracts a [`SelectStmt`].
    pub fn parse_select(sql: &str) -> SelectStmt {
        let stmt = Parser::new(sql).parse().unwrap().unwrap();
        let Statement::Select(select) = stmt else {
            panic!("expected SELECT statement from: {sql}");
        };
        *select
    }

    /// Parses a SQL string and extracts an [`InsertStmt`].
    pub fn parse_insert(sql: &str) -> InsertStmt {
        let stmt = Parser::new(sql).parse().unwrap().unwrap();
        let Statement::Insert(insert) = stmt else {
            panic!("expected INSERT statement from: {sql}");
        };
        *insert
    }

    /// Parses a SQL string and extracts an [`UpdateStmt`].
    pub fn parse_update(sql: &str) -> UpdateStmt {
        let stmt = Parser::new(sql).parse().unwrap().unwrap();
        let Statement::Update(update) = stmt else {
            panic!("expected UPDATE statement from: {sql}");
        };
        *update
    }

    /// Parses a SQL string and extracts a [`DeleteStmt`].
    pub fn parse_delete(sql: &str) -> DeleteStmt {
        let stmt = Parser::new(sql).parse().unwrap().unwrap();
        let Statement::Delete(delete) = stmt else {
            panic!("expected DELETE statement from: {sql}");
        };
        *delete
    }

    /// Parses a SQL string and extracts a [`CreateTableStmt`].
    pub fn parse_create_table(sql: &str) -> CreateTableStmt {
        let stmt = Parser::new(sql).parse().unwrap().unwrap();
        let Statement::CreateTable(create) = stmt else {
            panic!("expected CREATE TABLE statement from: {sql}");
        };
        *create
    }
}
