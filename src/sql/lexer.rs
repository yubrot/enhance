//! SQL lexer/tokenizer.
//!
//! The [`Lexer`] converts a SQL string into a stream of [`Token`]s.
//! It handles keywords, identifiers, literals, operators, and comments.

use super::error::Span;
use super::token::{Token, TokenKind};

/// SQL lexer that tokenizes input strings.
///
/// The lexer implements `Iterator<Item = Token>`. It handles:
/// - Keywords (case-insensitive)
/// - Identifiers (unquoted and double-quoted)
/// - Numeric literals (integers and floats)
/// - String literals (single-quoted with '' escape)
/// - Operators and punctuation
/// - Comments (-- line comments and /* */ block comments)
/// - Positional parameters ($1, $2, etc.)
///
/// Lexical errors are returned as `TokenKind::Error` tokens rather than
/// being accumulated separately.
pub struct Lexer<'a> {
    input: &'a str,
    pos: usize,
    /// Whether EOF has been returned.
    eof_returned: bool,
}

impl<'a> Lexer<'a> {
    /// Creates a new lexer for the given input string.
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            pos: 0,
            eof_returned: false,
        }
    }

    fn is_eof(&self) -> bool {
        self.pos >= self.input.len()
    }

    fn starts_with(&self, prefix: &str) -> bool {
        self.input[self.pos..].starts_with(prefix)
    }

    /// Returns the character at `pos + offset` without consuming it.
    fn peek(&self, offset: usize) -> Option<char> {
        self.input[self.pos..].chars().nth(offset)
    }

    /// Advances the position by `n` characters.
    fn advance(&mut self, n: usize) {
        for _ in 0..n {
            if let Some(ch) = self.peek(0) {
                self.pos += ch.len_utf8();
            }
        }
    }

    /// Skips whitespace and comments.
    ///
    /// Returns `Some(Token)` if an error was encountered (e.g., unterminated block comment),
    /// `None` otherwise.
    fn skip_whitespace_and_comments(&mut self) -> Option<Token> {
        loop {
            self.skip_whitespace();
            match self.skip_comment() {
                Ok(true) => continue,
                Ok(false) => return None,
                Err(token) => return Some(token),
            }
        }
    }

    fn skip_whitespace(&mut self) {
        while self.peek(0).is_some_and(|ch| ch.is_whitespace()) {
            self.advance(1);
        }
    }

    /// Attempts to skip a comment.
    ///
    /// Returns `Ok(true)` if a comment was skipped, `Ok(false)` if no comment was present,
    /// or `Err(Token)` if an error occurred (e.g., unterminated block comment).
    fn skip_comment(&mut self) -> Result<bool, Token> {
        // Line comment: -- to end of line
        if self.starts_with("--") {
            self.advance(2);
            while let Some(ch) = self.peek(0) {
                self.advance(1);
                if ch == '\n' {
                    break;
                }
            }
            return Ok(true);
        }

        // Block comment: /* to */
        if self.starts_with("/*") {
            let start = self.pos;
            self.advance(2);
            let mut depth = 1;
            while depth > 0 && !self.is_eof() {
                if self.starts_with("/*") {
                    depth += 1;
                    self.advance(2);
                } else if self.starts_with("*/") {
                    depth -= 1;
                    self.advance(2);
                } else {
                    self.advance(1);
                }
            }
            if depth > 0 {
                return Err(Token::new(
                    TokenKind::Error("unterminated block comment".to_string()),
                    Span::new(start, self.pos),
                ));
            }
            return Ok(true);
        }

        Ok(false)
    }

    /// Scans the next token from the input.
    fn scan_token(&mut self) -> Token {
        // Skip whitespace and comments, returning error token if found
        if let Some(error_token) = self.skip_whitespace_and_comments() {
            return error_token;
        }

        let start = self.pos;

        if self.is_eof() {
            return Token::new(TokenKind::Eof, Span::at(start));
        }

        let ch = self.peek(0).unwrap();

        // String literal
        if ch == '\'' {
            return self.scan_string_literal();
        }

        // Quoted identifier
        if ch == '"' {
            return self.scan_quoted_identifier();
        }

        // Positional parameter ($1, $2, etc.)
        if ch == '$' {
            return self.scan_parameter();
        }

        // Number literal
        if ch.is_ascii_digit() || (ch == '.' && self.peek(1).is_some_and(|c| c.is_ascii_digit())) {
            return self.scan_number();
        }

        // Identifier or keyword
        if is_ident_start(ch) {
            return self.scan_identifier_or_keyword();
        }

        // Operators and punctuation
        self.scan_operator_or_punctuation()
    }

    fn scan_string_literal(&mut self) -> Token {
        let start = self.pos;
        self.advance(1); // consume opening quote

        let mut value = String::new();
        let mut unterminated = false;

        loop {
            match self.peek(0) {
                None => {
                    unterminated = true;
                    break;
                }
                Some('\'') => {
                    self.advance(1);
                    // Check for escaped quote ('')
                    if self.peek(0) == Some('\'') {
                        value.push('\'');
                        self.advance(1);
                    } else {
                        // End of string
                        break;
                    }
                }
                Some(ch) => {
                    value.push(ch);
                    self.advance(1);
                }
            }
        }

        let span = Span::new(start, self.pos);
        if unterminated {
            Token::new(
                TokenKind::Error("unterminated string literal".to_string()),
                span,
            )
        } else {
            Token::new(TokenKind::StringLit(value), span)
        }
    }

    fn scan_quoted_identifier(&mut self) -> Token {
        let start = self.pos;
        self.advance(1); // consume opening quote

        let mut value = String::new();
        let mut unterminated = false;

        loop {
            match self.peek(0) {
                None => {
                    unterminated = true;
                    break;
                }
                Some('"') => {
                    self.advance(1);
                    // Check for escaped quote ("")
                    if self.peek(0) == Some('"') {
                        value.push('"');
                        self.advance(1);
                    } else {
                        // End of identifier
                        break;
                    }
                }
                Some(ch) => {
                    value.push(ch);
                    self.advance(1);
                }
            }
        }

        let span = Span::new(start, self.pos);
        if unterminated {
            Token::new(
                TokenKind::Error("unterminated quoted identifier".to_string()),
                span,
            )
        } else {
            Token::new(TokenKind::Identifier(value), span)
        }
    }

    fn scan_parameter(&mut self) -> Token {
        let start = self.pos;
        self.advance(1); // consume '$'

        let num_start = self.pos;
        while let Some(ch) = self.peek(0) {
            if ch.is_ascii_digit() {
                self.advance(1);
            } else {
                break;
            }
        }

        let num_str = &self.input[num_start..self.pos];
        let span = Span::new(start, self.pos);

        if num_str.is_empty() {
            return Token::new(
                TokenKind::Error("expected parameter number after '$'".to_string()),
                span,
            );
        }

        match num_str.parse::<u32>() {
            Ok(n) => Token::new(TokenKind::Parameter(n), span),
            Err(_) => Token::new(
                TokenKind::Error("parameter number too large".to_string()),
                span,
            ),
        }
    }

    fn scan_number(&mut self) -> Token {
        let start = self.pos;

        // Scan integer part
        while let Some(ch) = self.peek(0) {
            if ch.is_ascii_digit() {
                self.advance(1);
            } else {
                break;
            }
        }

        // Check for decimal point
        let mut is_float = false;
        if self.peek(0) == Some('.') {
            // Check if this is really a decimal or just a dot operator
            if self.peek(1).is_some_and(|c| c.is_ascii_digit()) {
                is_float = true;
                self.advance(1); // consume '.'
                while let Some(ch) = self.peek(0) {
                    if ch.is_ascii_digit() {
                        self.advance(1);
                    } else {
                        break;
                    }
                }
            }
        }

        // Check for exponent
        let mut invalid_exponent = false;
        if let Some('e' | 'E') = self.peek(0) {
            is_float = true;
            self.advance(1);
            if let Some('+' | '-') = self.peek(0) {
                self.advance(1);
            }
            let exp_start = self.pos;
            while let Some(ch) = self.peek(0) {
                if ch.is_ascii_digit() {
                    self.advance(1);
                } else {
                    break;
                }
            }
            if self.pos == exp_start {
                invalid_exponent = true;
            }
        }

        let num_str = &self.input[start..self.pos];
        let span = Span::new(start, self.pos);

        if invalid_exponent {
            return Token::new(TokenKind::Error("invalid number literal".to_string()), span);
        }

        if is_float {
            match num_str.parse::<f64>() {
                Ok(n) => Token::new(TokenKind::FloatLit(n), span),
                Err(_) => Token::new(TokenKind::Error("invalid number literal".to_string()), span),
            }
        } else {
            match num_str.parse::<i64>() {
                Ok(n) => Token::new(TokenKind::IntegerLit(n), span),
                Err(_) => Token::new(TokenKind::Error("invalid number literal".to_string()), span),
            }
        }
    }

    fn scan_identifier_or_keyword(&mut self) -> Token {
        let start = self.pos;

        while let Some(ch) = self.peek(0) {
            if is_ident_continue(ch) {
                self.advance(1);
            } else {
                break;
            }
        }

        let ident = &self.input[start..self.pos];
        let span = Span::new(start, self.pos);

        // Check if this is a keyword
        if let Some(kind) = TokenKind::from_keyword(ident) {
            Token::new(kind, span)
        } else {
            Token::new(TokenKind::Identifier(ident.to_string()), span)
        }
    }

    fn scan_operator_or_punctuation(&mut self) -> Token {
        let start = self.pos;

        // Two-character operators
        if self.input.len() >= self.pos + 2 {
            let two_chars = &self.input[self.pos..self.pos + 2];
            let kind = match two_chars {
                "<>" | "!=" => Some(TokenKind::Neq),
                "<=" => Some(TokenKind::LtEq),
                ">=" => Some(TokenKind::GtEq),
                "||" => Some(TokenKind::Concat),
                "::" => Some(TokenKind::DoubleColon),
                _ => None,
            };
            if let Some(kind) = kind {
                self.pos += 2;
                return Token::new(kind, Span::new(start, self.pos));
            }
        }

        // Single-character operators and punctuation
        let ch = self.peek(0).unwrap();
        self.advance(1);
        let kind = match ch {
            '+' => TokenKind::Plus,
            '-' => TokenKind::Minus,
            '*' => TokenKind::Asterisk,
            '/' => TokenKind::Slash,
            '%' => TokenKind::Percent,
            '=' => TokenKind::Eq,
            '<' => TokenKind::Lt,
            '>' => TokenKind::Gt,
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            ',' => TokenKind::Comma,
            ';' => TokenKind::Semicolon,
            '.' => TokenKind::Dot,
            ':' => TokenKind::Colon,
            _ => {
                return Token::new(
                    TokenKind::Error(format!("unexpected character '{ch}'")),
                    Span::new(start, self.pos),
                );
            }
        };

        Token::new(kind, Span::new(start, self.pos))
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        if self.eof_returned {
            return None;
        }

        let token = self.scan_token();
        if token.is_eof() {
            self.eof_returned = true;
        }
        Some(token)
    }
}

/// Returns true if the character can start an identifier.
fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

/// Returns true if the character can continue an identifier.
fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(input: &str) -> Vec<TokenKind> {
        Lexer::new(input).map(|t| t.kind).collect()
    }

    #[test]
    fn test_empty_input() {
        assert_eq!(lex(""), vec![TokenKind::Eof]);
        assert_eq!(lex("   "), vec![TokenKind::Eof]);
        assert_eq!(lex("  \n\t  "), vec![TokenKind::Eof]);
    }

    #[test]
    fn test_keywords() {
        assert_eq!(
            lex("SELECT FROM WHERE"),
            vec![
                TokenKind::Select,
                TokenKind::From,
                TokenKind::Where,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_keywords_case_insensitive() {
        assert_eq!(
            lex("select SELECT SeLeCt"),
            vec![
                TokenKind::Select,
                TokenKind::Select,
                TokenKind::Select,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_identifiers() {
        assert_eq!(
            lex("foo bar_baz _test"),
            vec![
                TokenKind::Identifier("foo".to_string()),
                TokenKind::Identifier("bar_baz".to_string()),
                TokenKind::Identifier("_test".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_quoted_identifiers() {
        assert_eq!(
            lex(r#""my table" "has""quotes""#),
            vec![
                TokenKind::Identifier("my table".to_string()),
                TokenKind::Identifier("has\"quotes".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_integers() {
        assert_eq!(
            lex("0 42 12345"),
            vec![
                TokenKind::IntegerLit(0),
                TokenKind::IntegerLit(42),
                TokenKind::IntegerLit(12345),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_floats() {
        assert_eq!(
            lex("3.5 0.5 1e10 2.5e-3"),
            vec![
                TokenKind::FloatLit(3.5),
                TokenKind::FloatLit(0.5),
                TokenKind::FloatLit(1e10),
                TokenKind::FloatLit(2.5e-3),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_string_literals() {
        assert_eq!(
            lex("'hello' 'it''s' ''"),
            vec![
                TokenKind::StringLit("hello".to_string()),
                TokenKind::StringLit("it's".to_string()),
                TokenKind::StringLit("".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_parameters() {
        assert_eq!(
            lex("$1 $2 $123"),
            vec![
                TokenKind::Parameter(1),
                TokenKind::Parameter(2),
                TokenKind::Parameter(123),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_operators() {
        assert_eq!(
            lex("+ - * / % = <> != < <= > >= ||"),
            vec![
                TokenKind::Plus,
                TokenKind::Minus,
                TokenKind::Asterisk,
                TokenKind::Slash,
                TokenKind::Percent,
                TokenKind::Eq,
                TokenKind::Neq,
                TokenKind::Neq,
                TokenKind::Lt,
                TokenKind::LtEq,
                TokenKind::Gt,
                TokenKind::GtEq,
                TokenKind::Concat,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_punctuation() {
        assert_eq!(
            lex("( ) , ; ."),
            vec![
                TokenKind::LParen,
                TokenKind::RParen,
                TokenKind::Comma,
                TokenKind::Semicolon,
                TokenKind::Dot,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_line_comments() {
        assert_eq!(
            lex("SELECT -- this is a comment\nFROM"),
            vec![TokenKind::Select, TokenKind::From, TokenKind::Eof,]
        );
    }

    #[test]
    fn test_block_comments() {
        assert_eq!(
            lex("SELECT /* comment */ FROM"),
            vec![TokenKind::Select, TokenKind::From, TokenKind::Eof,]
        );
    }

    #[test]
    fn test_nested_block_comments() {
        assert_eq!(
            lex("SELECT /* outer /* nested */ comment */ FROM"),
            vec![TokenKind::Select, TokenKind::From, TokenKind::Eof,]
        );
    }

    #[test]
    fn test_complex_query() {
        let tokens = lex("SELECT id, name FROM users WHERE age >= 18 AND active = TRUE");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Select,
                TokenKind::Identifier("id".to_string()),
                TokenKind::Comma,
                TokenKind::Identifier("name".to_string()),
                TokenKind::From,
                TokenKind::Identifier("users".to_string()),
                TokenKind::Where,
                TokenKind::Identifier("age".to_string()),
                TokenKind::GtEq,
                TokenKind::IntegerLit(18),
                TokenKind::And,
                TokenKind::Identifier("active".to_string()),
                TokenKind::Eq,
                TokenKind::True,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_unterminated_string() {
        let tokens = lex("'unterminated");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Error("unterminated string literal".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_unterminated_block_comment() {
        let tokens = lex("SELECT /* unterminated");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Select,
                TokenKind::Error("unterminated block comment".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_invalid_parameter() {
        let tokens = lex("$");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Error("expected parameter number after '$'".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_unexpected_character() {
        let tokens = lex("SELECT @ FROM");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Select,
                TokenKind::Error("unexpected character '@'".to_string()),
                TokenKind::From,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_token_spans() {
        let tokens: Vec<_> = Lexer::new("SELECT foo").collect();

        assert_eq!(tokens[0].span, Span::new(0, 6)); // SELECT
        assert_eq!(tokens[1].span, Span::new(7, 10)); // foo
        assert_eq!(tokens[2].span, Span::at(10)); // EOF
    }

    #[test]
    fn test_iterator_stops_after_eof() {
        let mut lexer = Lexer::new("SELECT");
        assert!(lexer.next().is_some()); // SELECT
        assert!(lexer.next().is_some()); // EOF
        assert!(lexer.next().is_none()); // Iterator exhausted
        assert!(lexer.next().is_none()); // Still exhausted
    }
}
