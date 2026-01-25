//! SQL syntax error types.
//!
//! This module provides the [`SyntaxError`] type for representing SQL syntax errors
//! with source position information for user-friendly error messages.

use std::fmt;

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

/// SQL syntax error with source position information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxError {
    /// Error message.
    pub message: String,
    /// Position in the source where the error occurred.
    pub span: Span,
}

impl SyntaxError {
    /// Creates a new syntax error at the given position.
    pub fn new(message: impl Into<String>, span: Span) -> Self {
        Self {
            message: message.into(),
            span,
        }
    }

    /// Creates a new error for an unexpected token.
    pub fn unexpected_token(expected: &str, found: &str, span: Span) -> Self {
        Self::new(format!("expected {expected}, found {found}"), span)
    }

    /// Creates a new error for an unexpected end of input.
    pub fn unexpected_eof(expected: &str, pos: usize) -> Self {
        Self::new(
            format!("unexpected end of input, expected {expected}"),
            Span::at(pos),
        )
    }

    /// Creates a new error for an invalid number literal.
    pub fn invalid_number(span: Span) -> Self {
        Self::new("invalid number literal", span)
    }

    /// Creates a new error for an unterminated string literal.
    pub fn unterminated_string(span: Span) -> Self {
        Self::new("unterminated string literal", span)
    }

    /// Creates a new error for an invalid escape sequence.
    pub fn invalid_escape(span: Span) -> Self {
        Self::new("invalid escape sequence", span)
    }

    /// Returns the 1-based character position for error reporting.
    pub fn position(&self) -> usize {
        self.span.start + 1
    }
}

impl fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at position {}", self.message, self.position())
    }
}

impl std::error::Error for SyntaxError {}

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
    fn test_syntax_error_position() {
        let err = SyntaxError::new("test", Span::at(10));
        assert_eq!(err.position(), 11); // 1-based
    }

    #[test]
    fn test_syntax_error_display() {
        let err = SyntaxError::new("unexpected token", Span::at(5));
        assert_eq!(err.to_string(), "unexpected token at position 6");
    }
}
