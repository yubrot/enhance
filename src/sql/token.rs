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
    Integer(i64),
    /// Floating-point literal (e.g., 3.14, -1.5e10).
    Float(f64),
    /// String literal (e.g., 'hello').
    String(String),

    // Identifiers and keywords
    /// Unquoted identifier (e.g., foo, my_table).
    Identifier(String),
    /// Quoted identifier (e.g., "my table").
    QuotedIdentifier(String),
    /// Positional parameter (e.g., $1, $2).
    Parameter(u32),

    // Keywords
    Keyword(Keyword),

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
}

impl TokenKind {
    /// Returns the display name for error messages.
    pub fn display_name(&self) -> String {
        match self {
            TokenKind::Integer(n) => format!("integer '{n}'"),
            TokenKind::Float(n) => format!("float '{n}'"),
            TokenKind::String(s) => format!("string '{s}'"),
            TokenKind::Identifier(s) => format!("identifier '{s}'"),
            TokenKind::QuotedIdentifier(s) => format!("identifier '\"{s}\"'"),
            TokenKind::Parameter(n) => format!("parameter '${n}'"),
            TokenKind::Keyword(kw) => format!("keyword '{}'", kw.as_str()),
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
        }
    }
}

/// SQL keywords.
///
/// Keywords are case-insensitive in SQL. The lexer normalizes them to uppercase
/// before matching against this enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Keyword {
    // Data types
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

    // DDL
    Create,
    Table,
    Drop,
    Alter,
    Index,
    If,
    Exists,

    // DML
    Select,
    Insert,
    Update,
    Delete,
    Into,
    Values,
    Set,
    From,
    Where,

    // SELECT clauses
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

    // JOIN
    Join,
    Inner,
    Left,
    Right,
    Full,
    Outer,
    Cross,
    On,
    Using,

    // Logical / Comparison
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

    // CASE expression
    Case,
    When,
    Then,
    Else,
    End,

    // Type cast
    Cast,

    // Constraints
    Primary,
    Key,
    Unique,
    References,
    Foreign,
    Check,
    Default,
    Constraint,

    // Transactions
    Begin,
    Start,
    Transaction,
    Commit,
    Rollback,

    // Misc
    Explain,
    For,
    Share,
}

impl Keyword {
    /// Returns the string representation of this keyword.
    pub fn as_str(&self) -> &'static str {
        match self {
            Keyword::Boolean => "BOOLEAN",
            Keyword::Smallint => "SMALLINT",
            Keyword::Integer => "INTEGER",
            Keyword::Int => "INT",
            Keyword::Bigint => "BIGINT",
            Keyword::Real => "REAL",
            Keyword::Double => "DOUBLE",
            Keyword::Precision => "PRECISION",
            Keyword::Text => "TEXT",
            Keyword::Varchar => "VARCHAR",
            Keyword::Bytea => "BYTEA",
            Keyword::Serial => "SERIAL",
            Keyword::Create => "CREATE",
            Keyword::Table => "TABLE",
            Keyword::Drop => "DROP",
            Keyword::Alter => "ALTER",
            Keyword::Index => "INDEX",
            Keyword::If => "IF",
            Keyword::Exists => "EXISTS",
            Keyword::Select => "SELECT",
            Keyword::Insert => "INSERT",
            Keyword::Update => "UPDATE",
            Keyword::Delete => "DELETE",
            Keyword::Into => "INTO",
            Keyword::Values => "VALUES",
            Keyword::Set => "SET",
            Keyword::From => "FROM",
            Keyword::Where => "WHERE",
            Keyword::As => "AS",
            Keyword::Distinct => "DISTINCT",
            Keyword::All => "ALL",
            Keyword::Group => "GROUP",
            Keyword::Having => "HAVING",
            Keyword::Order => "ORDER",
            Keyword::By => "BY",
            Keyword::Asc => "ASC",
            Keyword::Desc => "DESC",
            Keyword::Limit => "LIMIT",
            Keyword::Offset => "OFFSET",
            Keyword::Nulls => "NULLS",
            Keyword::First => "FIRST",
            Keyword::Last => "LAST",
            Keyword::Join => "JOIN",
            Keyword::Inner => "INNER",
            Keyword::Left => "LEFT",
            Keyword::Right => "RIGHT",
            Keyword::Full => "FULL",
            Keyword::Outer => "OUTER",
            Keyword::Cross => "CROSS",
            Keyword::On => "ON",
            Keyword::Using => "USING",
            Keyword::And => "AND",
            Keyword::Or => "OR",
            Keyword::Not => "NOT",
            Keyword::Is => "IS",
            Keyword::Null => "NULL",
            Keyword::True => "TRUE",
            Keyword::False => "FALSE",
            Keyword::In => "IN",
            Keyword::Between => "BETWEEN",
            Keyword::Like => "LIKE",
            Keyword::Ilike => "ILIKE",
            Keyword::Escape => "ESCAPE",
            Keyword::Case => "CASE",
            Keyword::When => "WHEN",
            Keyword::Then => "THEN",
            Keyword::Else => "ELSE",
            Keyword::End => "END",
            Keyword::Cast => "CAST",
            Keyword::Primary => "PRIMARY",
            Keyword::Key => "KEY",
            Keyword::Unique => "UNIQUE",
            Keyword::References => "REFERENCES",
            Keyword::Foreign => "FOREIGN",
            Keyword::Check => "CHECK",
            Keyword::Default => "DEFAULT",
            Keyword::Constraint => "CONSTRAINT",
            Keyword::Begin => "BEGIN",
            Keyword::Start => "START",
            Keyword::Transaction => "TRANSACTION",
            Keyword::Commit => "COMMIT",
            Keyword::Rollback => "ROLLBACK",
            Keyword::Explain => "EXPLAIN",
            Keyword::For => "FOR",
            Keyword::Share => "SHARE",
        }
    }

    /// Attempts to parse a keyword from a string (case-insensitive).
    pub fn parse(s: &str) -> Option<Self> {
        // NOTE: A production implementation might use a perfect hash or phf crate.
        // This simple match is sufficient for learning purposes.
        match s.to_uppercase().as_str() {
            "BOOLEAN" => Some(Keyword::Boolean),
            "SMALLINT" => Some(Keyword::Smallint),
            "INTEGER" => Some(Keyword::Integer),
            "INT" => Some(Keyword::Int),
            "BIGINT" => Some(Keyword::Bigint),
            "REAL" => Some(Keyword::Real),
            "DOUBLE" => Some(Keyword::Double),
            "PRECISION" => Some(Keyword::Precision),
            "TEXT" => Some(Keyword::Text),
            "VARCHAR" => Some(Keyword::Varchar),
            "BYTEA" => Some(Keyword::Bytea),
            "SERIAL" => Some(Keyword::Serial),
            "CREATE" => Some(Keyword::Create),
            "TABLE" => Some(Keyword::Table),
            "DROP" => Some(Keyword::Drop),
            "ALTER" => Some(Keyword::Alter),
            "INDEX" => Some(Keyword::Index),
            "IF" => Some(Keyword::If),
            "EXISTS" => Some(Keyword::Exists),
            "SELECT" => Some(Keyword::Select),
            "INSERT" => Some(Keyword::Insert),
            "UPDATE" => Some(Keyword::Update),
            "DELETE" => Some(Keyword::Delete),
            "INTO" => Some(Keyword::Into),
            "VALUES" => Some(Keyword::Values),
            "SET" => Some(Keyword::Set),
            "FROM" => Some(Keyword::From),
            "WHERE" => Some(Keyword::Where),
            "AS" => Some(Keyword::As),
            "DISTINCT" => Some(Keyword::Distinct),
            "ALL" => Some(Keyword::All),
            "GROUP" => Some(Keyword::Group),
            "HAVING" => Some(Keyword::Having),
            "ORDER" => Some(Keyword::Order),
            "BY" => Some(Keyword::By),
            "ASC" => Some(Keyword::Asc),
            "DESC" => Some(Keyword::Desc),
            "LIMIT" => Some(Keyword::Limit),
            "OFFSET" => Some(Keyword::Offset),
            "NULLS" => Some(Keyword::Nulls),
            "FIRST" => Some(Keyword::First),
            "LAST" => Some(Keyword::Last),
            "JOIN" => Some(Keyword::Join),
            "INNER" => Some(Keyword::Inner),
            "LEFT" => Some(Keyword::Left),
            "RIGHT" => Some(Keyword::Right),
            "FULL" => Some(Keyword::Full),
            "OUTER" => Some(Keyword::Outer),
            "CROSS" => Some(Keyword::Cross),
            "ON" => Some(Keyword::On),
            "USING" => Some(Keyword::Using),
            "AND" => Some(Keyword::And),
            "OR" => Some(Keyword::Or),
            "NOT" => Some(Keyword::Not),
            "IS" => Some(Keyword::Is),
            "NULL" => Some(Keyword::Null),
            "TRUE" => Some(Keyword::True),
            "FALSE" => Some(Keyword::False),
            "IN" => Some(Keyword::In),
            "BETWEEN" => Some(Keyword::Between),
            "LIKE" => Some(Keyword::Like),
            "ILIKE" => Some(Keyword::Ilike),
            "ESCAPE" => Some(Keyword::Escape),
            "CASE" => Some(Keyword::Case),
            "WHEN" => Some(Keyword::When),
            "THEN" => Some(Keyword::Then),
            "ELSE" => Some(Keyword::Else),
            "END" => Some(Keyword::End),
            "CAST" => Some(Keyword::Cast),
            "PRIMARY" => Some(Keyword::Primary),
            "KEY" => Some(Keyword::Key),
            "UNIQUE" => Some(Keyword::Unique),
            "REFERENCES" => Some(Keyword::References),
            "FOREIGN" => Some(Keyword::Foreign),
            "CHECK" => Some(Keyword::Check),
            "DEFAULT" => Some(Keyword::Default),
            "CONSTRAINT" => Some(Keyword::Constraint),
            "BEGIN" => Some(Keyword::Begin),
            "START" => Some(Keyword::Start),
            "TRANSACTION" => Some(Keyword::Transaction),
            "COMMIT" => Some(Keyword::Commit),
            "ROLLBACK" => Some(Keyword::Rollback),
            "EXPLAIN" => Some(Keyword::Explain),
            "FOR" => Some(Keyword::For),
            "SHARE" => Some(Keyword::Share),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_keyword_from_str() {
        assert_eq!(Keyword::parse("SELECT"), Some(Keyword::Select));
        assert_eq!(Keyword::parse("select"), Some(Keyword::Select));
        assert_eq!(Keyword::parse("SeLeCt"), Some(Keyword::Select));
        assert_eq!(Keyword::parse("unknown"), None);
    }

    #[test]
    fn test_keyword_roundtrip() {
        let keywords = [
            Keyword::Select,
            Keyword::Insert,
            Keyword::Update,
            Keyword::Delete,
            Keyword::Create,
            Keyword::Table,
        ];
        for kw in keywords {
            assert_eq!(Keyword::parse(kw.as_str()), Some(kw));
        }
    }

    #[test]
    fn test_token_display_name() {
        assert_eq!(
            TokenKind::Keyword(Keyword::Select).display_name(),
            "keyword 'SELECT'"
        );
        assert_eq!(
            TokenKind::Identifier("foo".to_string()).display_name(),
            "identifier 'foo'"
        );
        assert_eq!(TokenKind::Integer(42).display_name(), "integer '42'");
        assert_eq!(TokenKind::Eof.display_name(), "end of input");
    }
}
