//! SQL token types.
//!
//! This module defines the [`Token`] enum representing all possible SQL tokens
//! produced by the lexer, including keywords, operators, literals, and identifiers.

use super::error::Span;

/// A SQL token with its span in the source.
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    /// The token kind.
    pub kind: TokenKind,
    /// The span of this token in the source.
    pub span: Span,
}

impl Token {
    /// Creates a new token.
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }

    /// Returns true if this is an end-of-file token.
    pub fn is_eof(&self) -> bool {
        matches!(self.kind, TokenKind::Eof)
    }
}

/// The kind of a SQL token.
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // Literals
    /// Integer literal (e.g., 42, -123).
    IntegerLit(i64),
    /// Floating-point literal (e.g., 3.14, -1.5e10).
    FloatLit(f64),
    /// String literal (e.g., 'hello').
    StringLit(String),

    /// Identifier (e.g., foo, my_table, "my table").
    Identifier(String),
    /// Positional parameter (e.g., $1, $2).
    Parameter(u32),

    // Data type keywords
    Boolean,
    Smallint,
    Integer,
    Int,
    Bigint,
    Real,
    Double,
    Precision,
    Text,
    Varchar,
    Bytea,
    Serial,

    // DDL keywords
    Create,
    Table,
    Drop,
    Alter,
    Index,
    If,
    Exists,

    // DML keywords
    Select,
    Insert,
    Update,
    Delete,
    Into,
    Values,
    Set,
    From,
    Where,
    Returning,

    // SELECT clause keywords
    As,
    Distinct,
    All,
    Group,
    Having,
    Order,
    By,
    Asc,
    Desc,
    Limit,
    Offset,
    Nulls,
    First,
    Last,

    // JOIN keywords
    Join,
    Inner,
    Left,
    Right,
    Full,
    Outer,
    Cross,
    On,
    Using,

    // Logical / Comparison keywords
    And,
    Or,
    Not,
    Is,
    Null,
    True,
    False,
    In,
    Between,
    Like,
    Ilike,
    Escape,

    // CASE expression keywords
    Case,
    When,
    Then,
    Else,
    End,

    // Type cast keyword
    Cast,

    // Constraint keywords
    Primary,
    Key,
    Unique,
    References,
    Foreign,
    Check,
    Default,
    Constraint,

    // Transaction keywords
    Begin,
    Start,
    Transaction,
    Commit,
    Rollback,

    // Misc keywords
    Explain,
    For,
    Share,

    // Operators
    /// +
    Plus,
    /// -
    Minus,
    /// *
    Asterisk,
    /// /
    Slash,
    /// %
    Percent,
    /// =
    Eq,
    /// <> or !=
    Neq,
    /// <
    Lt,
    /// <=
    LtEq,
    /// >
    Gt,
    /// >=
    GtEq,
    /// ||
    Concat,
    /// ::
    DoubleColon,

    // Punctuation
    /// (
    LParen,
    /// )
    RParen,
    /// ,
    Comma,
    /// ;
    Semicolon,
    /// .
    Dot,
    /// :
    Colon,

    /// End of file/input.
    Eof,

    /// Lexer error (e.g., unterminated string, invalid character).
    Error(String),
}

impl TokenKind {
    /// Returns the display name for error messages.
    pub fn display_name(&self) -> String {
        match self {
            TokenKind::IntegerLit(n) => format!("integer '{n}'"),
            TokenKind::FloatLit(n) => format!("float '{n}'"),
            TokenKind::StringLit(s) => format!("string '{s}'"),
            TokenKind::Identifier(s) => format!("identifier '{s}'"),
            TokenKind::Parameter(n) => format!("parameter '${n}'"),
            TokenKind::Boolean => "BOOLEAN".to_string(),
            TokenKind::Smallint => "SMALLINT".to_string(),
            TokenKind::Integer => "INTEGER".to_string(),
            TokenKind::Int => "INT".to_string(),
            TokenKind::Bigint => "BIGINT".to_string(),
            TokenKind::Real => "REAL".to_string(),
            TokenKind::Double => "DOUBLE".to_string(),
            TokenKind::Precision => "PRECISION".to_string(),
            TokenKind::Text => "TEXT".to_string(),
            TokenKind::Varchar => "VARCHAR".to_string(),
            TokenKind::Bytea => "BYTEA".to_string(),
            TokenKind::Serial => "SERIAL".to_string(),
            TokenKind::Create => "CREATE".to_string(),
            TokenKind::Table => "TABLE".to_string(),
            TokenKind::Drop => "DROP".to_string(),
            TokenKind::Alter => "ALTER".to_string(),
            TokenKind::Index => "INDEX".to_string(),
            TokenKind::If => "IF".to_string(),
            TokenKind::Exists => "EXISTS".to_string(),
            TokenKind::Select => "SELECT".to_string(),
            TokenKind::Insert => "INSERT".to_string(),
            TokenKind::Update => "UPDATE".to_string(),
            TokenKind::Delete => "DELETE".to_string(),
            TokenKind::Into => "INTO".to_string(),
            TokenKind::Values => "VALUES".to_string(),
            TokenKind::Set => "SET".to_string(),
            TokenKind::From => "FROM".to_string(),
            TokenKind::Where => "WHERE".to_string(),
            TokenKind::Returning => "RETURNING".to_string(),
            TokenKind::As => "AS".to_string(),
            TokenKind::Distinct => "DISTINCT".to_string(),
            TokenKind::All => "ALL".to_string(),
            TokenKind::Group => "GROUP".to_string(),
            TokenKind::Having => "HAVING".to_string(),
            TokenKind::Order => "ORDER".to_string(),
            TokenKind::By => "BY".to_string(),
            TokenKind::Asc => "ASC".to_string(),
            TokenKind::Desc => "DESC".to_string(),
            TokenKind::Limit => "LIMIT".to_string(),
            TokenKind::Offset => "OFFSET".to_string(),
            TokenKind::Nulls => "NULLS".to_string(),
            TokenKind::First => "FIRST".to_string(),
            TokenKind::Last => "LAST".to_string(),
            TokenKind::Join => "JOIN".to_string(),
            TokenKind::Inner => "INNER".to_string(),
            TokenKind::Left => "LEFT".to_string(),
            TokenKind::Right => "RIGHT".to_string(),
            TokenKind::Full => "FULL".to_string(),
            TokenKind::Outer => "OUTER".to_string(),
            TokenKind::Cross => "CROSS".to_string(),
            TokenKind::On => "ON".to_string(),
            TokenKind::Using => "USING".to_string(),
            TokenKind::And => "AND".to_string(),
            TokenKind::Or => "OR".to_string(),
            TokenKind::Not => "NOT".to_string(),
            TokenKind::Is => "IS".to_string(),
            TokenKind::Null => "NULL".to_string(),
            TokenKind::True => "TRUE".to_string(),
            TokenKind::False => "FALSE".to_string(),
            TokenKind::In => "IN".to_string(),
            TokenKind::Between => "BETWEEN".to_string(),
            TokenKind::Like => "LIKE".to_string(),
            TokenKind::Ilike => "ILIKE".to_string(),
            TokenKind::Escape => "ESCAPE".to_string(),
            TokenKind::Case => "CASE".to_string(),
            TokenKind::When => "WHEN".to_string(),
            TokenKind::Then => "THEN".to_string(),
            TokenKind::Else => "ELSE".to_string(),
            TokenKind::End => "END".to_string(),
            TokenKind::Cast => "CAST".to_string(),
            TokenKind::Primary => "PRIMARY".to_string(),
            TokenKind::Key => "KEY".to_string(),
            TokenKind::Unique => "UNIQUE".to_string(),
            TokenKind::References => "REFERENCES".to_string(),
            TokenKind::Foreign => "FOREIGN".to_string(),
            TokenKind::Check => "CHECK".to_string(),
            TokenKind::Default => "DEFAULT".to_string(),
            TokenKind::Constraint => "CONSTRAINT".to_string(),
            TokenKind::Begin => "BEGIN".to_string(),
            TokenKind::Start => "START".to_string(),
            TokenKind::Transaction => "TRANSACTION".to_string(),
            TokenKind::Commit => "COMMIT".to_string(),
            TokenKind::Rollback => "ROLLBACK".to_string(),
            TokenKind::Explain => "EXPLAIN".to_string(),
            TokenKind::For => "FOR".to_string(),
            TokenKind::Share => "SHARE".to_string(),
            TokenKind::Plus => "'+'".to_string(),
            TokenKind::Minus => "'-'".to_string(),
            TokenKind::Asterisk => "'*'".to_string(),
            TokenKind::Slash => "'/'".to_string(),
            TokenKind::Percent => "'%'".to_string(),
            TokenKind::Eq => "'='".to_string(),
            TokenKind::Neq => "'<>'".to_string(),
            TokenKind::Lt => "'<'".to_string(),
            TokenKind::LtEq => "'<='".to_string(),
            TokenKind::Gt => "'>'".to_string(),
            TokenKind::GtEq => "'>='".to_string(),
            TokenKind::Concat => "'||'".to_string(),
            TokenKind::DoubleColon => "'::'".to_string(),
            TokenKind::LParen => "'('".to_string(),
            TokenKind::RParen => "')'".to_string(),
            TokenKind::Comma => "','".to_string(),
            TokenKind::Semicolon => "';'".to_string(),
            TokenKind::Dot => "'.'".to_string(),
            TokenKind::Colon => "':'".to_string(),
            TokenKind::Eof => "end of input".to_string(),
            TokenKind::Error(msg) => format!("error: {msg}"),
        }
    }

    /// Attempts to parse a keyword from a string (case-insensitive).
    ///
    /// Returns `None` if the string is not a recognized keyword.
    pub fn from_keyword(s: &str) -> Option<Self> {
        // NOTE: A production implementation might use a perfect hash or phf crate.
        // This simple match is sufficient for learning purposes.
        Some(match s.to_uppercase().as_str() {
            "BOOLEAN" => TokenKind::Boolean,
            "SMALLINT" => TokenKind::Smallint,
            "INTEGER" => TokenKind::Integer,
            "INT" => TokenKind::Int,
            "BIGINT" => TokenKind::Bigint,
            "REAL" => TokenKind::Real,
            "DOUBLE" => TokenKind::Double,
            "PRECISION" => TokenKind::Precision,
            "TEXT" => TokenKind::Text,
            "VARCHAR" => TokenKind::Varchar,
            "BYTEA" => TokenKind::Bytea,
            "SERIAL" => TokenKind::Serial,
            "CREATE" => TokenKind::Create,
            "TABLE" => TokenKind::Table,
            "DROP" => TokenKind::Drop,
            "ALTER" => TokenKind::Alter,
            "INDEX" => TokenKind::Index,
            "IF" => TokenKind::If,
            "EXISTS" => TokenKind::Exists,
            "SELECT" => TokenKind::Select,
            "INSERT" => TokenKind::Insert,
            "UPDATE" => TokenKind::Update,
            "DELETE" => TokenKind::Delete,
            "INTO" => TokenKind::Into,
            "VALUES" => TokenKind::Values,
            "SET" => TokenKind::Set,
            "FROM" => TokenKind::From,
            "WHERE" => TokenKind::Where,
            "RETURNING" => TokenKind::Returning,
            "AS" => TokenKind::As,
            "DISTINCT" => TokenKind::Distinct,
            "ALL" => TokenKind::All,
            "GROUP" => TokenKind::Group,
            "HAVING" => TokenKind::Having,
            "ORDER" => TokenKind::Order,
            "BY" => TokenKind::By,
            "ASC" => TokenKind::Asc,
            "DESC" => TokenKind::Desc,
            "LIMIT" => TokenKind::Limit,
            "OFFSET" => TokenKind::Offset,
            "NULLS" => TokenKind::Nulls,
            "FIRST" => TokenKind::First,
            "LAST" => TokenKind::Last,
            "JOIN" => TokenKind::Join,
            "INNER" => TokenKind::Inner,
            "LEFT" => TokenKind::Left,
            "RIGHT" => TokenKind::Right,
            "FULL" => TokenKind::Full,
            "OUTER" => TokenKind::Outer,
            "CROSS" => TokenKind::Cross,
            "ON" => TokenKind::On,
            "USING" => TokenKind::Using,
            "AND" => TokenKind::And,
            "OR" => TokenKind::Or,
            "NOT" => TokenKind::Not,
            "IS" => TokenKind::Is,
            "NULL" => TokenKind::Null,
            "TRUE" => TokenKind::True,
            "FALSE" => TokenKind::False,
            "IN" => TokenKind::In,
            "BETWEEN" => TokenKind::Between,
            "LIKE" => TokenKind::Like,
            "ILIKE" => TokenKind::Ilike,
            "ESCAPE" => TokenKind::Escape,
            "CASE" => TokenKind::Case,
            "WHEN" => TokenKind::When,
            "THEN" => TokenKind::Then,
            "ELSE" => TokenKind::Else,
            "END" => TokenKind::End,
            "CAST" => TokenKind::Cast,
            "PRIMARY" => TokenKind::Primary,
            "KEY" => TokenKind::Key,
            "UNIQUE" => TokenKind::Unique,
            "REFERENCES" => TokenKind::References,
            "FOREIGN" => TokenKind::Foreign,
            "CHECK" => TokenKind::Check,
            "DEFAULT" => TokenKind::Default,
            "CONSTRAINT" => TokenKind::Constraint,
            "BEGIN" => TokenKind::Begin,
            "START" => TokenKind::Start,
            "TRANSACTION" => TokenKind::Transaction,
            "COMMIT" => TokenKind::Commit,
            "ROLLBACK" => TokenKind::Rollback,
            "EXPLAIN" => TokenKind::Explain,
            "FOR" => TokenKind::For,
            "SHARE" => TokenKind::Share,
            _ => return None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_keyword_from_str() {
        assert_eq!(TokenKind::from_keyword("SELECT"), Some(TokenKind::Select));
        assert_eq!(TokenKind::from_keyword("select"), Some(TokenKind::Select));
        assert_eq!(TokenKind::from_keyword("SeLeCt"), Some(TokenKind::Select));
        assert_eq!(TokenKind::from_keyword("unknown"), None);
    }

    #[test]
    fn test_keyword_roundtrip() {
        let keywords = [
            ("SELECT", TokenKind::Select),
            ("INSERT", TokenKind::Insert),
            ("UPDATE", TokenKind::Update),
            ("DELETE", TokenKind::Delete),
            ("CREATE", TokenKind::Create),
            ("TABLE", TokenKind::Table),
        ];
        for (s, kw) in keywords {
            assert_eq!(TokenKind::from_keyword(s), Some(kw));
        }
    }

    #[test]
    fn test_token_display_name() {
        assert_eq!(TokenKind::Select.display_name(), "SELECT");
        assert_eq!(
            TokenKind::Identifier("foo".to_string()).display_name(),
            "identifier 'foo'"
        );
        assert_eq!(TokenKind::IntegerLit(42).display_name(), "integer '42'");
        assert_eq!(TokenKind::Eof.display_name(), "end of input");
    }
}
