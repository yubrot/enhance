//! SQL parsing error types.
//!
//! This module provides the [`ParseError`] type for representing SQL syntax errors
//! with source position information for user-friendly error messages.

use std::fmt;

use crate::protocol::sql_state;

/// A span in the source SQL string.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    /// Byte offset from the start of the input.
    pub start: usize,
    /// Byte offset of the end of the span (exclusive).
    pub end: usize,
}

impl Span {
    /// Creates a new span.
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// Creates a zero-length span at the given position.
    pub fn at(pos: usize) -> Self {
        Self {
            start: pos,
            end: pos,
        }
    }

    /// Extends this span to include another span.
    pub fn extend(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

/// SQL parsing error with source position information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    /// Error message.
    pub message: String,
    /// Position in the source where the error occurred.
    pub span: Span,
    /// Error kind for SQL state code determination.
    pub kind: ParseErrorKind,
}

/// Kind of parse error for determining SQL state code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseErrorKind {
    /// General syntax error.
    SyntaxError,
    /// Undefined table reference.
    UndefinedTable,
    /// Undefined column reference.
    UndefinedColumn,
    /// Undefined function reference.
    UndefinedFunction,
}

impl ParseError {
    /// Creates a new syntax error at the given position.
    pub fn syntax_error(message: impl Into<String>, span: Span) -> Self {
        Self {
            message: message.into(),
            span,
            kind: ParseErrorKind::SyntaxError,
        }
    }

    /// Creates a new error for an unexpected token.
    pub fn unexpected_token(expected: &str, found: &str, span: Span) -> Self {
        Self::syntax_error(format!("expected {expected}, found {found}"), span)
    }

    /// Creates a new error for an unexpected end of input.
    pub fn unexpected_eof(expected: &str, pos: usize) -> Self {
        Self::syntax_error(
            format!("unexpected end of input, expected {expected}"),
            Span::at(pos),
        )
    }

    /// Creates a new error for an invalid number literal.
    pub fn invalid_number(span: Span) -> Self {
        Self::syntax_error("invalid number literal", span)
    }

    /// Creates a new error for an unterminated string literal.
    pub fn unterminated_string(span: Span) -> Self {
        Self::syntax_error("unterminated string literal", span)
    }

    /// Creates a new error for an invalid escape sequence.
    pub fn invalid_escape(span: Span) -> Self {
        Self::syntax_error("invalid escape sequence", span)
    }

    /// Returns the PostgreSQL SQL state code for this error.
    pub fn sql_state(&self) -> &'static str {
        match self.kind {
            ParseErrorKind::SyntaxError => sql_state::SYNTAX_ERROR,
            ParseErrorKind::UndefinedTable => sql_state::UNDEFINED_TABLE,
            ParseErrorKind::UndefinedColumn => sql_state::UNDEFINED_COLUMN,
            ParseErrorKind::UndefinedFunction => sql_state::UNDEFINED_FUNCTION,
        }
    }

    /// Returns the 1-based character position for PostgreSQL error reporting.
    ///
    /// PostgreSQL uses 1-based character positions in error messages.
    pub fn position(&self) -> usize {
        self.span.start + 1
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at position {}", self.message, self.position())
    }
}

impl std::error::Error for ParseError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_span_at() {
        let span = Span::at(5);
        assert_eq!(span.start, 5);
        assert_eq!(span.end, 5);
    }

    #[test]
    fn test_span_extend() {
        let span1 = Span::new(5, 10);
        let span2 = Span::new(15, 20);
        let extended = span1.extend(span2);
        assert_eq!(extended.start, 5);
        assert_eq!(extended.end, 20);
    }

    #[test]
    fn test_parse_error_sql_state() {
        let err = ParseError::syntax_error("test", Span::at(0));
        assert_eq!(err.sql_state(), sql_state::SYNTAX_ERROR);
    }

    #[test]
    fn test_parse_error_position() {
        let err = ParseError::syntax_error("test", Span::at(10));
        assert_eq!(err.position(), 11); // 1-based
    }

    #[test]
    fn test_parse_error_display() {
        let err = ParseError::syntax_error("unexpected token", Span::at(5));
        assert_eq!(err.to_string(), "unexpected token at position 6");
    }
}
