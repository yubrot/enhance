//! SQL lexer/tokenizer.
//!
//! The [`Lexer`] converts a SQL string into a stream of [`Token`]s.
//! It handles keywords, identifiers, literals, operators, and comments.

use super::error::{ParseError, Span};
use super::token::{Keyword, Token, TokenKind};

/// SQL lexer that tokenizes input strings.
///
/// The lexer is an iterator over tokens. It handles:
/// - Keywords (case-insensitive)
/// - Identifiers (unquoted and double-quoted)
/// - Numeric literals (integers and floats)
/// - String literals (single-quoted with '' escape)
/// - Operators and punctuation
/// - Comments (-- line comments and /* */ block comments)
/// - Positional parameters ($1, $2, etc.)
pub struct Lexer<'a> {
    input: &'a str,
    pos: usize,
    /// Accumulated errors during tokenization.
    errors: Vec<ParseError>,
}

impl<'a> Lexer<'a> {
    /// Creates a new lexer for the given input string.
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            pos: 0,
            errors: Vec::new(),
        }
    }

    /// Returns all errors accumulated during tokenization.
    pub fn errors(&self) -> &[ParseError] {
        &self.errors
    }

    /// Takes all errors, leaving an empty error list.
    pub fn take_errors(&mut self) -> Vec<ParseError> {
        std::mem::take(&mut self.errors)
    }

    /// Tokenizes the entire input and returns all tokens.
    ///
    /// The returned vector always ends with an EOF token.
    pub fn tokenize(&mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        loop {
            let token = self.next_token();
            let is_eof = token.is_eof();
            tokens.push(token);
            if is_eof {
                break;
            }
        }
        tokens
    }

    /// Returns the next token from the input.
    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace_and_comments();

        let start = self.pos;

        if self.is_eof() {
            return Token::new(TokenKind::Eof, Span::at(start));
        }

        let ch = self.current_char().unwrap();

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
        if ch.is_ascii_digit() || (ch == '.' && self.peek_char().is_some_and(|c| c.is_ascii_digit()))
        {
            return self.scan_number();
        }

        // Identifier or keyword
        if is_ident_start(ch) {
            return self.scan_identifier_or_keyword();
        }

        // Operators and punctuation
        self.scan_operator_or_punctuation()
    }

    fn is_eof(&self) -> bool {
        self.pos >= self.input.len()
    }

    fn current_char(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    fn peek_char(&self) -> Option<char> {
        let mut chars = self.input[self.pos..].chars();
        chars.next();
        chars.next()
    }

    fn advance(&mut self) {
        if let Some(ch) = self.current_char() {
            self.pos += ch.len_utf8();
        }
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            self.skip_whitespace();
            if !self.skip_comment() {
                break;
            }
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.current_char() {
            if ch.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn skip_comment(&mut self) -> bool {
        // Line comment: -- to end of line
        if self.starts_with("--") {
            self.advance();
            self.advance();
            while let Some(ch) = self.current_char() {
                self.advance();
                if ch == '\n' {
                    break;
                }
            }
            return true;
        }

        // Block comment: /* to */
        if self.starts_with("/*") {
            let start = self.pos;
            self.advance();
            self.advance();
            let mut depth = 1;
            while depth > 0 && !self.is_eof() {
                if self.starts_with("/*") {
                    depth += 1;
                    self.advance();
                    self.advance();
                } else if self.starts_with("*/") {
                    depth -= 1;
                    self.advance();
                    self.advance();
                } else {
                    self.advance();
                }
            }
            if depth > 0 {
                self.errors.push(ParseError::syntax_error(
                    "unterminated block comment",
                    Span::new(start, self.pos),
                ));
            }
            return true;
        }

        false
    }

    fn starts_with(&self, prefix: &str) -> bool {
        self.input[self.pos..].starts_with(prefix)
    }

    fn scan_string_literal(&mut self) -> Token {
        let start = self.pos;
        self.advance(); // consume opening quote

        let mut value = String::new();

        loop {
            match self.current_char() {
                None => {
                    self.errors
                        .push(ParseError::unterminated_string(Span::new(start, self.pos)));
                    break;
                }
                Some('\'') => {
                    self.advance();
                    // Check for escaped quote ('')
                    if self.current_char() == Some('\'') {
                        value.push('\'');
                        self.advance();
                    } else {
                        // End of string
                        break;
                    }
                }
                Some(ch) => {
                    value.push(ch);
                    self.advance();
                }
            }
        }

        Token::new(TokenKind::String(value), Span::new(start, self.pos))
    }

    fn scan_quoted_identifier(&mut self) -> Token {
        let start = self.pos;
        self.advance(); // consume opening quote

        let mut value = String::new();

        loop {
            match self.current_char() {
                None => {
                    self.errors.push(ParseError::syntax_error(
                        "unterminated quoted identifier",
                        Span::new(start, self.pos),
                    ));
                    break;
                }
                Some('"') => {
                    self.advance();
                    // Check for escaped quote ("")
                    if self.current_char() == Some('"') {
                        value.push('"');
                        self.advance();
                    } else {
                        // End of identifier
                        break;
                    }
                }
                Some(ch) => {
                    value.push(ch);
                    self.advance();
                }
            }
        }

        Token::new(TokenKind::QuotedIdentifier(value), Span::new(start, self.pos))
    }

    fn scan_parameter(&mut self) -> Token {
        let start = self.pos;
        self.advance(); // consume '$'

        let num_start = self.pos;
        while let Some(ch) = self.current_char() {
            if ch.is_ascii_digit() {
                self.advance();
            } else {
                break;
            }
        }

        let num_str = &self.input[num_start..self.pos];
        if num_str.is_empty() {
            self.errors.push(ParseError::syntax_error(
                "expected parameter number after '$'",
                Span::new(start, self.pos),
            ));
            return Token::new(TokenKind::Parameter(0), Span::new(start, self.pos));
        }

        match num_str.parse::<u32>() {
            Ok(n) => Token::new(TokenKind::Parameter(n), Span::new(start, self.pos)),
            Err(_) => {
                self.errors.push(ParseError::syntax_error(
                    "parameter number too large",
                    Span::new(start, self.pos),
                ));
                Token::new(TokenKind::Parameter(0), Span::new(start, self.pos))
            }
        }
    }

    fn scan_number(&mut self) -> Token {
        let start = self.pos;

        // Scan integer part
        while let Some(ch) = self.current_char() {
            if ch.is_ascii_digit() {
                self.advance();
            } else {
                break;
            }
        }

        // Check for decimal point
        let mut is_float = false;
        if self.current_char() == Some('.') {
            // Check if this is really a decimal or just a dot operator
            if self.peek_char().is_some_and(|c| c.is_ascii_digit()) {
                is_float = true;
                self.advance(); // consume '.'
                while let Some(ch) = self.current_char() {
                    if ch.is_ascii_digit() {
                        self.advance();
                    } else {
                        break;
                    }
                }
            }
        }

        // Check for exponent
        if let Some('e' | 'E') = self.current_char() {
            is_float = true;
            self.advance();
            if let Some('+' | '-') = self.current_char() {
                self.advance();
            }
            let exp_start = self.pos;
            while let Some(ch) = self.current_char() {
                if ch.is_ascii_digit() {
                    self.advance();
                } else {
                    break;
                }
            }
            if self.pos == exp_start {
                self.errors
                    .push(ParseError::invalid_number(Span::new(start, self.pos)));
            }
        }

        let num_str = &self.input[start..self.pos];
        let span = Span::new(start, self.pos);

        if is_float {
            match num_str.parse::<f64>() {
                Ok(n) => Token::new(TokenKind::Float(n), span),
                Err(_) => {
                    self.errors.push(ParseError::invalid_number(span));
                    Token::new(TokenKind::Float(0.0), span)
                }
            }
        } else {
            match num_str.parse::<i64>() {
                Ok(n) => Token::new(TokenKind::Integer(n), span),
                Err(_) => {
                    self.errors.push(ParseError::invalid_number(span));
                    Token::new(TokenKind::Integer(0), span)
                }
            }
        }
    }

    fn scan_identifier_or_keyword(&mut self) -> Token {
        let start = self.pos;

        while let Some(ch) = self.current_char() {
            if is_ident_continue(ch) {
                self.advance();
            } else {
                break;
            }
        }

        let ident = &self.input[start..self.pos];
        let span = Span::new(start, self.pos);

        // Check if this is a keyword
        if let Some(keyword) = Keyword::parse(ident) {
            Token::new(TokenKind::Keyword(keyword), span)
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
        let ch = self.current_char().unwrap();
        self.advance();
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
                self.errors.push(ParseError::syntax_error(
                    format!("unexpected character '{ch}'"),
                    Span::new(start, self.pos),
                ));
                return self.next_token();
            }
        };

        Token::new(kind, Span::new(start, self.pos))
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

    fn tokenize(input: &str) -> Vec<TokenKind> {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize();
        assert!(lexer.errors().is_empty(), "unexpected errors: {:?}", lexer.errors());
        tokens.into_iter().map(|t| t.kind).collect()
    }

    fn tokenize_with_errors(input: &str) -> (Vec<TokenKind>, Vec<ParseError>) {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize();
        let errors = lexer.take_errors();
        (tokens.into_iter().map(|t| t.kind).collect(), errors)
    }

    #[test]
    fn test_empty_input() {
        assert_eq!(tokenize(""), vec![TokenKind::Eof]);
        assert_eq!(tokenize("   "), vec![TokenKind::Eof]);
        assert_eq!(tokenize("  \n\t  "), vec![TokenKind::Eof]);
    }

    #[test]
    fn test_keywords() {
        assert_eq!(
            tokenize("SELECT FROM WHERE"),
            vec![
                TokenKind::Keyword(Keyword::Select),
                TokenKind::Keyword(Keyword::From),
                TokenKind::Keyword(Keyword::Where),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_keywords_case_insensitive() {
        assert_eq!(
            tokenize("select SELECT SeLeCt"),
            vec![
                TokenKind::Keyword(Keyword::Select),
                TokenKind::Keyword(Keyword::Select),
                TokenKind::Keyword(Keyword::Select),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_identifiers() {
        assert_eq!(
            tokenize("foo bar_baz _test"),
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
            tokenize(r#""my table" "has""quotes""#),
            vec![
                TokenKind::QuotedIdentifier("my table".to_string()),
                TokenKind::QuotedIdentifier("has\"quotes".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_integers() {
        assert_eq!(
            tokenize("0 42 12345"),
            vec![
                TokenKind::Integer(0),
                TokenKind::Integer(42),
                TokenKind::Integer(12345),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_floats() {
        assert_eq!(
            tokenize("3.14 0.5 1e10 2.5e-3"),
            vec![
                TokenKind::Float(3.14),
                TokenKind::Float(0.5),
                TokenKind::Float(1e10),
                TokenKind::Float(2.5e-3),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_string_literals() {
        assert_eq!(
            tokenize("'hello' 'it''s' ''"),
            vec![
                TokenKind::String("hello".to_string()),
                TokenKind::String("it's".to_string()),
                TokenKind::String("".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_parameters() {
        assert_eq!(
            tokenize("$1 $2 $123"),
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
            tokenize("+ - * / % = <> != < <= > >= ||"),
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
            tokenize("( ) , ; ."),
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
            tokenize("SELECT -- this is a comment\nFROM"),
            vec![
                TokenKind::Keyword(Keyword::Select),
                TokenKind::Keyword(Keyword::From),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_block_comments() {
        assert_eq!(
            tokenize("SELECT /* comment */ FROM"),
            vec![
                TokenKind::Keyword(Keyword::Select),
                TokenKind::Keyword(Keyword::From),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_nested_block_comments() {
        assert_eq!(
            tokenize("SELECT /* outer /* nested */ comment */ FROM"),
            vec![
                TokenKind::Keyword(Keyword::Select),
                TokenKind::Keyword(Keyword::From),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_complex_query() {
        let tokens = tokenize("SELECT id, name FROM users WHERE age >= 18 AND active = TRUE");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Keyword(Keyword::Select),
                TokenKind::Identifier("id".to_string()),
                TokenKind::Comma,
                TokenKind::Identifier("name".to_string()),
                TokenKind::Keyword(Keyword::From),
                TokenKind::Identifier("users".to_string()),
                TokenKind::Keyword(Keyword::Where),
                TokenKind::Identifier("age".to_string()),
                TokenKind::GtEq,
                TokenKind::Integer(18),
                TokenKind::Keyword(Keyword::And),
                TokenKind::Identifier("active".to_string()),
                TokenKind::Eq,
                TokenKind::Keyword(Keyword::True),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_unterminated_string() {
        let (tokens, errors) = tokenize_with_errors("'unterminated");
        assert_eq!(tokens, vec![TokenKind::String("unterminated".to_string()), TokenKind::Eof]);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains("unterminated string"));
    }

    #[test]
    fn test_unterminated_block_comment() {
        let (tokens, errors) = tokenize_with_errors("SELECT /* unterminated");
        assert_eq!(tokens, vec![TokenKind::Keyword(Keyword::Select), TokenKind::Eof]);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains("unterminated block comment"));
    }

    #[test]
    fn test_invalid_parameter() {
        let (tokens, errors) = tokenize_with_errors("$");
        assert_eq!(tokens, vec![TokenKind::Parameter(0), TokenKind::Eof]);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains("expected parameter number"));
    }

    #[test]
    fn test_unexpected_character() {
        let (tokens, errors) = tokenize_with_errors("SELECT @ FROM");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Keyword(Keyword::Select),
                TokenKind::Keyword(Keyword::From),
                TokenKind::Eof,
            ]
        );
        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains("unexpected character '@'"));
    }

    #[test]
    fn test_token_spans() {
        let mut lexer = Lexer::new("SELECT foo");
        let tokens = lexer.tokenize();

        assert_eq!(tokens[0].span, Span::new(0, 6)); // SELECT
        assert_eq!(tokens[1].span, Span::new(7, 10)); // foo
        assert_eq!(tokens[2].span, Span::at(10)); // EOF
    }
}
