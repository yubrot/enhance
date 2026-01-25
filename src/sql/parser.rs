//! SQL parser using recursive descent.
//!
//! The [`Parser`] converts a stream of tokens into an Abstract Syntax Tree (AST).
//! It uses recursive descent for most constructs and precedence climbing for
//! expression parsing.

use super::ast::*;
use super::error::{Span, SyntaxError};
use super::lexer::Lexer;
use super::token::{Token, TokenKind};

/// Operator precedence levels (higher = binds tighter).
///
/// Precedence (low to high):
/// 1. OR
/// 2. AND
/// 3. NOT (unary)
/// 4. =, <>, <, <=, >, >=, IS NULL
/// 5. ||
/// 6. +, -
/// 7. *, /, %
/// 8. Unary -, +
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    Lowest = 0,
    Or = 1,
    And = 2,
    Not = 3,
    Comparison = 4,
    Concat = 5,
    AddSub = 6,
    MulDiv = 7,
    UnaryPlusMinus = 8,
}

impl Precedence {
    /// Returns the next higher precedence level.
    fn next(self) -> Self {
        match self {
            Precedence::Lowest => Precedence::Or,
            Precedence::Or => Precedence::And,
            Precedence::And => Precedence::Not,
            Precedence::Not => Precedence::Comparison,
            Precedence::Comparison => Precedence::Concat,
            Precedence::Concat => Precedence::AddSub,
            Precedence::AddSub => Precedence::MulDiv,
            Precedence::MulDiv => Precedence::UnaryPlusMinus,
            Precedence::UnaryPlusMinus => Precedence::UnaryPlusMinus,
        }
    }
}

/// SQL parser that converts tokens into an AST.
///
/// The parser implements recursive descent parsing for SQL statements
/// and precedence climbing for expression parsing.
pub struct Parser<'a> {
    tokens: Vec<Token>,
    pos: usize,
    input: &'a str,
}

impl<'a> Parser<'a> {
    // ==================== Public API ====================

    /// Creates a new parser for the given SQL input.
    pub fn new(input: &'a str) -> Self {
        // NOTE: Lexer errors are returned as TokenKind::Error tokens.
        // The parser will report them as syntax errors when encountered.
        let tokens = Lexer::new(input).collect();

        Self {
            tokens,
            pos: 0,
            input,
        }
    }

    /// Parses the input and returns a statement.
    ///
    /// Returns `Ok(None)` for empty queries (whitespace/comments only),
    /// `Ok(Some(stmt))` for valid SQL statements.
    ///
    /// # Errors
    ///
    /// Returns a [`SyntaxError`] if the input is not valid SQL.
    pub fn parse(&mut self) -> Result<Option<Statement>, SyntaxError> {
        // Empty query (only whitespace/comments)
        if matches!(self.peek(0), None | Some(TokenKind::Eof)) {
            return Ok(None);
        }

        let stmt = self.parse_statement()?;

        // Optional trailing semicolon
        if matches!(self.peek(0), Some(TokenKind::Semicolon)) {
            self.discard(1);
        }

        // Check for unexpected trailing tokens
        if !matches!(self.peek(0), None | Some(TokenKind::Eof)) {
            return Err(self.unexpected_token_error("end of input"));
        }

        Ok(Some(stmt))
    }

    // ==================== Statement parsing ====================

    /// Parses a single statement.
    fn parse_statement(&mut self) -> Result<Statement, SyntaxError> {
        match self.peek(0) {
            Some(TokenKind::Explain) => {
                self.discard(1);
                Ok(Statement::Explain(Box::new(self.parse_statement()?)))
            }
            Some(TokenKind::Begin) => self.parse_begin_stmt(),
            Some(TokenKind::Commit) => {
                self.discard(1);
                Ok(Statement::Commit)
            }
            Some(TokenKind::Rollback) => {
                self.discard(1);
                Ok(Statement::Rollback)
            }
            Some(TokenKind::Set) => self.parse_set_stmt(),
            Some(TokenKind::Create) => self.parse_create_stmt(),
            Some(TokenKind::Drop) => self.parse_drop_stmt(),
            Some(TokenKind::Select) => Ok(Statement::Select(Box::new(self.parse_select_stmt()?))),
            Some(TokenKind::Insert) => self.parse_insert_stmt(),
            Some(TokenKind::Update) => self.parse_update_stmt(),
            Some(TokenKind::Delete) => self.parse_delete_stmt(),
            _ => Err(self.unexpected_token_error("statement")),
        }
    }

    /// Parses a BEGIN statement.
    fn parse_begin_stmt(&mut self) -> Result<Statement, SyntaxError> {
        // BEGIN [TRANSACTION]
        self.consume(TokenKind::Begin)?;
        if self.starts_with([TokenKind::Transaction]) {
            self.discard(1);
        }
        Ok(Statement::Begin)
    }

    /// Parses a SET statement.
    fn parse_set_stmt(&mut self) -> Result<Statement, SyntaxError> {
        self.consume(TokenKind::Set)?;
        let name = self.consume_identifier()?;
        self.consume(TokenKind::Eq)?;
        let value = self.parse_expr()?;

        Ok(Statement::Set(SetStmt { name, value }))
    }

    /// Parses a CREATE statement (TABLE or INDEX).
    fn parse_create_stmt(&mut self) -> Result<Statement, SyntaxError> {
        if self.starts_with([TokenKind::Create, TokenKind::Table]) {
            return self.parse_create_table();
        }
        if self.starts_with([TokenKind::Create, TokenKind::Unique, TokenKind::Index])
            || self.starts_with([TokenKind::Create, TokenKind::Index])
        {
            return self.parse_create_index();
        }

        // Consume CREATE to give a better error message
        self.consume(TokenKind::Create)?;
        Err(self.unexpected_token_error("TABLE or INDEX"))
    }

    /// Parses a CREATE TABLE statement.
    fn parse_create_table(&mut self) -> Result<Statement, SyntaxError> {
        self.consume(TokenKind::Create)?;
        self.consume(TokenKind::Table)?;

        let if_not_exists = self.parse_if_not_exists()?;
        let name = self.consume_identifier()?;

        self.consume(TokenKind::LParen)?;

        let mut columns = Vec::new();
        let mut constraints = Vec::new();

        loop {
            // Check for table-level constraint
            if matches!(
                self.peek(0),
                Some(
                    TokenKind::Primary
                        | TokenKind::Unique
                        | TokenKind::Foreign
                        | TokenKind::Check
                        | TokenKind::Constraint
                )
            ) {
                constraints.push(self.parse_table_constraint()?);
            } else {
                columns.push(self.parse_column_def()?);
            }

            if matches!(self.peek(0), Some(TokenKind::Comma)) {
                self.discard(1);
            } else {
                break;
            }
        }

        self.consume(TokenKind::RParen)?;

        Ok(Statement::CreateTable(Box::new(CreateTableStmt {
            name,
            columns,
            constraints,
            if_not_exists,
        })))
    }

    /// Parses a column definition.
    fn parse_column_def(&mut self) -> Result<ColumnDef, SyntaxError> {
        let name = self.consume_identifier()?;
        let data_type = self.parse_data_type()?;
        let constraints = self.parse_column_constraints()?;

        Ok(ColumnDef {
            name,
            data_type,
            constraints,
        })
    }

    /// Parses a data type.
    pub(crate) fn parse_data_type(&mut self) -> Result<DataType, SyntaxError> {
        match self.peek(0) {
            Some(TokenKind::Boolean) => {
                self.discard(1);
                Ok(DataType::Boolean)
            }
            Some(TokenKind::Smallint) => {
                self.discard(1);
                Ok(DataType::Smallint)
            }
            Some(TokenKind::Integer_ | TokenKind::Int) => {
                self.discard(1);
                Ok(DataType::Integer)
            }
            Some(TokenKind::Bigint) => {
                self.discard(1);
                Ok(DataType::Bigint)
            }
            Some(TokenKind::Real) => {
                self.discard(1);
                Ok(DataType::Real)
            }
            Some(TokenKind::Text) => {
                self.discard(1);
                Ok(DataType::Text)
            }
            Some(TokenKind::Varchar) => {
                self.discard(1);
                let length = self.parse_parenthesized_integer()?;
                Ok(DataType::Varchar(length))
            }
            Some(TokenKind::Bytea) => {
                self.discard(1);
                Ok(DataType::Bytea)
            }
            Some(TokenKind::Serial) => {
                self.discard(1);
                Ok(DataType::Serial)
            }
            Some(TokenKind::Double) if self.peek(1) == Some(&TokenKind::Precision) => {
                self.discard(2);
                Ok(DataType::DoublePrecision)
            }
            _ => Err(self.unexpected_token_error("data type")),
        }
    }

    /// Parses an optional parenthesized integer.
    fn parse_parenthesized_integer(&mut self) -> Result<Option<u32>, SyntaxError> {
        if matches!(self.peek(0), Some(TokenKind::LParen)) {
            self.discard(1);
            let n = self.consume_integer()?;
            self.consume(TokenKind::RParen)?;
            Ok(Some(n as u32))
        } else {
            Ok(None)
        }
    }

    /// Parses column constraints.
    fn parse_column_constraints(&mut self) -> Result<Vec<ColumnConstraint>, SyntaxError> {
        let mut constraints = Vec::new();

        loop {
            if self.starts_with([TokenKind::Not, TokenKind::Null]) {
                self.discard(2);
                constraints.push(ColumnConstraint::NotNull);
            } else if self.starts_with([TokenKind::Null]) {
                self.discard(1);
                constraints.push(ColumnConstraint::Null);
            } else if self.starts_with([TokenKind::Primary, TokenKind::Key]) {
                self.discard(2);
                constraints.push(ColumnConstraint::PrimaryKey);
            } else if self.starts_with([TokenKind::Unique]) {
                self.discard(1);
                constraints.push(ColumnConstraint::Unique);
            } else if self.starts_with([TokenKind::Default]) {
                self.discard(1);
                let value = self.parse_expr()?;
                constraints.push(ColumnConstraint::Default(value));
            } else if self.starts_with([TokenKind::Check]) {
                self.discard(1);
                let expr = self.parse_parenthesized(Self::parse_expr)?;
                constraints.push(ColumnConstraint::Check(expr));
            } else if self.starts_with([TokenKind::References]) {
                self.discard(1);
                let table = self.consume_identifier()?;
                let column = self.parse_parenthesized_identifier()?;
                constraints.push(ColumnConstraint::References { table, column });
            } else {
                break;
            }
        }

        Ok(constraints)
    }

    /// Parses an optional parenthesized identifier.
    fn parse_parenthesized_identifier(&mut self) -> Result<Option<String>, SyntaxError> {
        if matches!(self.peek(0), Some(TokenKind::LParen)) {
            self.discard(1);
            let id = self.consume_identifier()?;
            self.consume(TokenKind::RParen)?;
            Ok(Some(id))
        } else {
            Ok(None)
        }
    }

    /// Parses a table-level constraint.
    fn parse_table_constraint(&mut self) -> Result<TableConstraint, SyntaxError> {
        let name = if self.starts_with([TokenKind::Constraint]) {
            self.discard(1);
            Some(self.consume_identifier()?)
        } else {
            None
        };

        let kind = if self.starts_with([TokenKind::Primary, TokenKind::Key]) {
            self.discard(2);
            let columns = self.parse_parenthesized(Self::parse_identifier_list)?;
            TableConstraintKind::PrimaryKey(columns)
        } else if self.starts_with([TokenKind::Unique]) {
            self.discard(1);
            let columns = self.parse_parenthesized(Self::parse_identifier_list)?;
            TableConstraintKind::Unique(columns)
        } else if self.starts_with([TokenKind::Check]) {
            self.discard(1);
            let expr = self.parse_parenthesized(Self::parse_expr)?;
            TableConstraintKind::Check(expr)
        } else if self.starts_with([TokenKind::Foreign, TokenKind::Key]) {
            self.discard(2);
            let columns = self.parse_parenthesized(Self::parse_identifier_list)?;
            self.consume(TokenKind::References)?;
            let ref_table = self.consume_identifier()?;
            let ref_columns = self.parse_parenthesized(Self::parse_identifier_list)?;
            TableConstraintKind::ForeignKey {
                columns,
                ref_table,
                ref_columns,
            }
        } else {
            return Err(self.unexpected_token_error("constraint type"));
        };

        Ok(TableConstraint { name, kind })
    }

    /// Parses a CREATE INDEX statement.
    fn parse_create_index(&mut self) -> Result<Statement, SyntaxError> {
        // CREATE [UNIQUE] INDEX [IF NOT EXISTS] name ON table (columns)
        self.consume(TokenKind::Create)?;

        let unique = self.starts_with([TokenKind::Unique]);
        if unique {
            self.discard(1);
        }

        self.consume(TokenKind::Index)?;

        let if_not_exists = self.parse_if_not_exists()?;
        let name = self.consume_identifier()?;
        self.consume(TokenKind::On)?;
        let table = self.consume_identifier()?;

        let columns = self.parse_parenthesized(Self::parse_index_column_list)?;

        Ok(Statement::CreateIndex(CreateIndexStmt {
            name,
            table,
            columns,
            if_not_exists,
            unique,
        }))
    }

    /// Parses a comma-separated list of index columns.
    fn parse_index_column_list(&mut self) -> Result<Vec<IndexColumn>, SyntaxError> {
        self.parse_comma_separated(|p| {
            let name = p.consume_identifier()?;
            let direction = p.parse_sort_direction();
            Ok(IndexColumn { name, direction })
        })
    }

    /// Parses a DROP statement (TABLE or INDEX).
    fn parse_drop_stmt(&mut self) -> Result<Statement, SyntaxError> {
        // DROP TABLE
        if self.starts_with([TokenKind::Drop, TokenKind::Table]) {
            return self.parse_drop_table();
        }

        // DROP INDEX
        if self.starts_with([TokenKind::Drop, TokenKind::Index]) {
            return self.parse_drop_index();
        }

        // Consume DROP to give a better error message
        self.consume(TokenKind::Drop)?;
        Err(self.unexpected_token_error("TABLE or INDEX"))
    }

    /// Parses a DROP TABLE statement.
    fn parse_drop_table(&mut self) -> Result<Statement, SyntaxError> {
        // DROP TABLE [IF EXISTS] name
        self.consume(TokenKind::Drop)?;
        self.consume(TokenKind::Table)?;

        let if_exists = self.parse_if_exists()?;
        let name = self.consume_identifier()?;

        Ok(Statement::DropTable(DropTableStmt { name, if_exists }))
    }

    /// Parses a DROP INDEX statement.
    fn parse_drop_index(&mut self) -> Result<Statement, SyntaxError> {
        // DROP INDEX [IF EXISTS] name
        self.consume(TokenKind::Drop)?;
        self.consume(TokenKind::Index)?;

        let if_exists = self.parse_if_exists()?;
        let name = self.consume_identifier()?;

        Ok(Statement::DropIndex(DropIndexStmt { name, if_exists }))
    }

    /// Parses a SELECT statement.
    pub(crate) fn parse_select_stmt(&mut self) -> Result<SelectStmt, SyntaxError> {
        self.consume(TokenKind::Select)?;

        // DISTINCT / ALL
        let distinct = if self.starts_with([TokenKind::Distinct]) {
            self.discard(1);
            true
        } else {
            if self.starts_with([TokenKind::All]) {
                self.discard(1);
            }
            false
        };

        // Select list
        let columns = self.parse_select_list()?;

        // FROM clause
        let from = self.parse_if_token(TokenKind::From, Self::parse_from_clause)?;

        // WHERE clause
        let where_clause = self.parse_if_token(TokenKind::Where, Self::parse_expr)?;

        // GROUP BY clause
        let group_by = if self.starts_with([TokenKind::Group, TokenKind::By]) {
            self.discard(2);
            self.parse_expr_list()?
        } else {
            vec![]
        };

        // HAVING clause
        let having = self.parse_if_token(TokenKind::Having, Self::parse_expr)?;

        // ORDER BY clause
        let order_by = if self.starts_with([TokenKind::Order, TokenKind::By]) {
            self.discard(2);
            self.parse_order_by_list()?
        } else {
            vec![]
        };

        // LIMIT clause
        let limit = self.parse_if_token(TokenKind::Limit, Self::parse_expr)?;

        // OFFSET clause
        let offset = self.parse_if_token(TokenKind::Offset, Self::parse_expr)?;

        // FOR UPDATE/SHARE
        let locking = self.parse_if_token(TokenKind::For, Self::parse_locking_clause)?;

        Ok(SelectStmt {
            distinct,
            columns,
            from,
            where_clause,
            group_by,
            having,
            order_by,
            limit,
            offset,
            locking,
        })
    }

    /// Parses the select list (columns/expressions).
    fn parse_select_list(&mut self) -> Result<Vec<SelectItem>, SyntaxError> {
        self.parse_comma_separated(Self::parse_select_item)
    }

    /// Parses a single select item.
    fn parse_select_item(&mut self) -> Result<SelectItem, SyntaxError> {
        // Check for *
        if matches!(self.peek(0), Some(TokenKind::Asterisk)) {
            self.discard(1);
            return Ok(SelectItem::Wildcard);
        }

        // Check for table.* (qualified wildcard)
        if let Some(TokenKind::Identifier(name) | TokenKind::QuotedIdentifier(name)) = self.peek(0)
            && self.peek(1) == Some(&TokenKind::Dot)
            && self.peek(2) == Some(&TokenKind::Asterisk)
        {
            let name = name.clone();
            self.discard(3);
            return Ok(SelectItem::QualifiedWildcard(name));
        }

        // Expression with optional alias
        let expr = self.parse_expr()?;
        let alias = self.parse_as()?;

        Ok(SelectItem::Expr { expr, alias })
    }

    /// Parses the FROM clause.
    fn parse_from_clause(&mut self) -> Result<FromClause, SyntaxError> {
        let tables = self.parse_comma_separated(Self::parse_table_ref)?;
        Ok(FromClause { tables })
    }

    /// Parses a table reference.
    fn parse_table_ref(&mut self) -> Result<TableRef, SyntaxError> {
        let mut table_ref = self.parse_primary_table_ref()?;

        // Handle JOINs
        loop {
            let join_type = if self.starts_with([TokenKind::Cross, TokenKind::Join]) {
                self.discard(2);
                Some(JoinType::Cross)
            } else if self.starts_with([TokenKind::Inner, TokenKind::Join]) {
                self.discard(2);
                Some(JoinType::Inner)
            } else if self.starts_with([TokenKind::Left, TokenKind::Outer, TokenKind::Join]) {
                self.discard(3);
                Some(JoinType::Left)
            } else if self.starts_with([TokenKind::Left, TokenKind::Join]) {
                self.discard(2);
                Some(JoinType::Left)
            } else if self.starts_with([TokenKind::Right, TokenKind::Outer, TokenKind::Join]) {
                self.discard(3);
                Some(JoinType::Right)
            } else if self.starts_with([TokenKind::Right, TokenKind::Join]) {
                self.discard(2);
                Some(JoinType::Right)
            } else if self.starts_with([TokenKind::Full, TokenKind::Outer, TokenKind::Join]) {
                self.discard(3);
                Some(JoinType::Full)
            } else if self.starts_with([TokenKind::Full, TokenKind::Join]) {
                self.discard(2);
                Some(JoinType::Full)
            } else if self.starts_with([TokenKind::Join]) {
                self.discard(1);
                Some(JoinType::Inner)
            } else {
                None
            };

            let Some(join_type) = join_type else {
                break;
            };

            let right = self.parse_primary_table_ref()?;

            let condition = if join_type == JoinType::Cross {
                None
            } else if self.starts_with([TokenKind::On]) {
                self.discard(1);
                Some(JoinCondition::On(self.parse_expr()?))
            } else if self.starts_with([TokenKind::Using]) {
                self.discard(1);
                let columns = self.parse_parenthesized(Self::parse_identifier_list)?;
                Some(JoinCondition::Using(columns))
            } else {
                None
            };

            table_ref = TableRef::Join {
                left: Box::new(table_ref),
                join_type,
                right: Box::new(right),
                condition,
            };
        }

        Ok(table_ref)
    }

    /// Parses a primary table reference (table name or subquery).
    fn parse_primary_table_ref(&mut self) -> Result<TableRef, SyntaxError> {
        // Subquery
        if matches!(self.peek(0), Some(TokenKind::LParen)) {
            self.discard(1);
            let query = self.parse_select_stmt()?;
            self.consume(TokenKind::RParen)?;

            // Subquery alias is required
            if self.starts_with([TokenKind::As]) {
                self.discard(1);
            }
            let alias = self.consume_identifier()?;

            return Ok(TableRef::Subquery {
                query: Box::new(query),
                alias,
            });
        }

        // Table name
        let name = self.consume_identifier()?;
        let alias = self.parse_as()?;

        Ok(TableRef::Table { name, alias })
    }

    /// Parses ORDER BY item list.
    fn parse_order_by_list(&mut self) -> Result<Vec<OrderByItem>, SyntaxError> {
        self.parse_comma_separated(|p| {
            let expr = p.parse_expr()?;
            let direction = p.parse_sort_direction();
            let nulls = p.parse_null_ordering()?;
            Ok(OrderByItem {
                expr,
                direction,
                nulls,
            })
        })
    }

    /// Parses FOR UPDATE/SHARE clause.
    fn parse_locking_clause(&mut self) -> Result<LockingClause, SyntaxError> {
        let mode = match self.peek(0) {
            Some(TokenKind::Update) => {
                self.discard(1);
                LockMode::Update
            }
            Some(TokenKind::Share) => {
                self.discard(1);
                LockMode::Share
            }
            _ => return Err(self.unexpected_token_error("UPDATE or SHARE")),
        };

        Ok(LockingClause { mode })
    }

    /// Parses an INSERT statement.
    fn parse_insert_stmt(&mut self) -> Result<Statement, SyntaxError> {
        self.consume(TokenKind::Insert)?;
        self.consume(TokenKind::Into)?;
        let table = self.consume_identifier()?;

        // Optional column list
        let columns = if matches!(self.peek(0), Some(TokenKind::LParen)) {
            self.parse_parenthesized(Self::parse_identifier_list)?
        } else {
            vec![]
        };

        // VALUES clause
        self.consume(TokenKind::Values)?;

        let values =
            self.parse_comma_separated(|p| p.parse_parenthesized(Self::parse_expr_list))?;

        Ok(Statement::Insert(Box::new(InsertStmt {
            table,
            columns,
            values,
        })))
    }

    /// Parses an UPDATE statement.
    fn parse_update_stmt(&mut self) -> Result<Statement, SyntaxError> {
        self.consume(TokenKind::Update)?;
        let table = self.consume_identifier()?;
        self.consume(TokenKind::Set)?;

        let assignments = self.parse_comma_separated(|p| {
            let column = p.consume_identifier()?;
            p.consume(TokenKind::Eq)?;
            let value = p.parse_expr()?;
            Ok(Assignment { column, value })
        })?;

        let where_clause = self.parse_if_token(TokenKind::Where, Self::parse_expr)?;

        Ok(Statement::Update(Box::new(UpdateStmt {
            table,
            assignments,
            where_clause,
        })))
    }

    /// Parses a DELETE statement.
    fn parse_delete_stmt(&mut self) -> Result<Statement, SyntaxError> {
        self.consume(TokenKind::Delete)?;
        self.consume(TokenKind::From)?;
        let table = self.consume_identifier()?;

        let where_clause = self.parse_if_token(TokenKind::Where, Self::parse_expr)?;

        Ok(Statement::Delete(Box::new(DeleteStmt {
            table,
            where_clause,
        })))
    }

    // ==================== Expression parsing ====================

    /// Parses an expression.
    pub fn parse_expr(&mut self) -> Result<Expr, SyntaxError> {
        self.parse_expr_with_precedence(Precedence::Lowest)
    }

    /// Parses an expression with minimum precedence.
    fn parse_expr_with_precedence(&mut self, min_prec: Precedence) -> Result<Expr, SyntaxError> {
        let mut left = self.parse_unary_expr()?;

        loop {
            let Some((op, prec)) = self.peek_binary_op() else {
                break;
            };
            if prec < min_prec {
                break;
            }
            self.discard(1);

            let next_prec = prec.next();
            let right = self.parse_expr_with_precedence(next_prec)?;

            left = Expr::BinaryOp {
                left: Box::new(left),
                op,
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    /// Parses a unary expression (NOT, -, +) or primary expression.
    fn parse_unary_expr(&mut self) -> Result<Expr, SyntaxError> {
        let (op, precedence) = match self.peek(0) {
            Some(TokenKind::Not) => (UnaryOperator::Not, Precedence::Not),
            Some(TokenKind::Minus) => (UnaryOperator::Minus, Precedence::UnaryPlusMinus),
            Some(TokenKind::Plus) => (UnaryOperator::Plus, Precedence::UnaryPlusMinus),
            _ => return self.parse_postfix_expr(),
        };
        self.discard(1);
        let operand = self.parse_expr_with_precedence(precedence)?;
        Ok(Expr::UnaryOp {
            op,
            operand: Box::new(operand),
        })
    }

    /// Parses postfix expressions (IS NULL, IN, BETWEEN, LIKE, ::, etc.).
    fn parse_postfix_expr(&mut self) -> Result<Expr, SyntaxError> {
        let mut expr = self.parse_primary_expr()?;

        loop {
            if self.starts_with([TokenKind::Is, TokenKind::Not, TokenKind::Null]) {
                self.discard(3);
                expr = Expr::IsNull {
                    expr: Box::new(expr),
                    negated: true,
                };
            } else if self.starts_with([TokenKind::Is, TokenKind::Null]) {
                self.discard(2);
                expr = Expr::IsNull {
                    expr: Box::new(expr),
                    negated: false,
                };
            } else if self.starts_with([TokenKind::Not, TokenKind::In]) {
                self.discard(2);
                expr = self.parse_in_expr(expr, true)?;
            } else if self.starts_with([TokenKind::Not, TokenKind::Between]) {
                self.discard(2);
                expr = self.parse_between_expr(expr, true)?;
            } else if self.starts_with([TokenKind::Not, TokenKind::Like])
                || self.starts_with([TokenKind::Not, TokenKind::Ilike])
            {
                self.discard(1); // NOT (LIKE/ILIKE consumed by parse_like_expr)
                expr = self.parse_like_expr(expr, true)?;
            } else if self.starts_with([TokenKind::In]) {
                self.discard(1);
                expr = self.parse_in_expr(expr, false)?;
            } else if self.starts_with([TokenKind::Between]) {
                self.discard(1);
                expr = self.parse_between_expr(expr, false)?;
            } else if self.starts_with([TokenKind::Like]) || self.starts_with([TokenKind::Ilike]) {
                expr = self.parse_like_expr(expr, false)?;
            } else if matches!(self.peek(0), Some(TokenKind::DoubleColon)) {
                self.discard(1);
                let data_type = self.parse_data_type()?;
                expr = Expr::Cast {
                    expr: Box::new(expr),
                    data_type,
                };
            } else {
                break;
            }
        }

        Ok(expr)
    }

    /// Parses IN expression (after IN keyword consumed).
    fn parse_in_expr(&mut self, expr: Expr, negated: bool) -> Result<Expr, SyntaxError> {
        self.consume(TokenKind::LParen)?;
        if self.starts_with([TokenKind::Select]) {
            let subquery = self.parse_select_stmt()?;
            self.consume(TokenKind::RParen)?;
            Ok(Expr::InSubquery {
                expr: Box::new(expr),
                subquery: Box::new(subquery),
                negated,
            })
        } else {
            let list = self.parse_expr_list()?;
            self.consume(TokenKind::RParen)?;
            Ok(Expr::InList {
                expr: Box::new(expr),
                list,
                negated,
            })
        }
    }

    /// Parses BETWEEN expression (after BETWEEN keyword consumed).
    fn parse_between_expr(&mut self, expr: Expr, negated: bool) -> Result<Expr, SyntaxError> {
        let low = self.parse_expr_with_precedence(Precedence::Comparison)?;
        self.consume(TokenKind::And)?;
        let high = self.parse_expr_with_precedence(Precedence::Comparison)?;
        Ok(Expr::Between {
            expr: Box::new(expr),
            low: Box::new(low),
            high: Box::new(high),
            negated,
        })
    }

    /// Parses LIKE/ILIKE expression (consumes keyword itself).
    fn parse_like_expr(&mut self, expr: Expr, negated: bool) -> Result<Expr, SyntaxError> {
        let case_insensitive = self.starts_with([TokenKind::Ilike]);
        self.discard(1); // consume LIKE or ILIKE
        let pattern = self.parse_expr_with_precedence(Precedence::Comparison)?;
        let escape = if self.starts_with([TokenKind::Escape]) {
            self.discard(1);
            Some(Box::new(
                self.parse_expr_with_precedence(Precedence::Comparison)?,
            ))
        } else {
            None
        };
        Ok(Expr::Like {
            expr: Box::new(expr),
            pattern: Box::new(pattern),
            escape,
            negated,
            case_insensitive,
        })
    }

    /// Parses a primary expression (literals, identifiers, function calls, etc.).
    fn parse_primary_expr(&mut self) -> Result<Expr, SyntaxError> {
        match self.peek(0) {
            Some(TokenKind::Null) => {
                self.discard(1);
                Ok(Expr::Null)
            }
            Some(TokenKind::True) => {
                self.discard(1);
                Ok(Expr::Boolean(true))
            }
            Some(TokenKind::False) => {
                self.discard(1);
                Ok(Expr::Boolean(false))
            }
            Some(TokenKind::Exists) => {
                self.discard(1);
                let subquery = self.parse_parenthesized(Self::parse_select_stmt)?;
                Ok(Expr::Exists {
                    subquery: Box::new(subquery),
                    negated: false,
                })
            }
            Some(TokenKind::Case) => {
                self.discard(1);
                self.parse_case_expr()
            }
            Some(TokenKind::Cast) => {
                self.discard(1);
                let (expr, data_type) = self.parse_parenthesized(|p| {
                    let expr = p.parse_expr()?;
                    p.consume(TokenKind::As)?;
                    let data_type = p.parse_data_type()?;
                    Ok((expr, data_type))
                })?;
                Ok(Expr::Cast {
                    expr: Box::new(expr),
                    data_type,
                })
            }
            Some(TokenKind::Integer(n)) => {
                let n = *n;
                self.discard(1);
                Ok(Expr::Integer(n))
            }
            Some(TokenKind::Float(n)) => {
                let n = *n;
                self.discard(1);
                Ok(Expr::Float(n))
            }
            Some(TokenKind::String(s)) => {
                let s = s.clone();
                self.discard(1);
                Ok(Expr::String(s))
            }
            Some(TokenKind::Parameter(n)) => {
                let n = *n;
                self.discard(1);
                Ok(Expr::Parameter(n))
            }
            Some(TokenKind::LParen) => {
                self.discard(1);
                if self.starts_with([TokenKind::Select]) {
                    let query = self.parse_select_stmt()?;
                    self.consume(TokenKind::RParen)?;
                    Ok(Expr::Subquery(Box::new(query)))
                } else {
                    let expr = self.parse_expr()?;
                    self.consume(TokenKind::RParen)?;
                    Ok(expr)
                }
            }
            Some(TokenKind::Identifier(name) | TokenKind::QuotedIdentifier(name)) => {
                let name = name.clone();
                self.discard(1);

                // Function call
                if matches!(self.peek(0), Some(TokenKind::LParen)) {
                    return self.parse_function_call(name);
                }

                // Qualified column reference (table.column)
                if matches!(self.peek(0), Some(TokenKind::Dot)) {
                    self.discard(1);
                    let column = self.consume_identifier()?;
                    return Ok(Expr::ColumnRef {
                        table: Some(name),
                        column,
                    });
                }

                Ok(Expr::ColumnRef {
                    table: None,
                    column: name,
                })
            }
            // Asterisk (for COUNT(*))
            Some(TokenKind::Asterisk) => {
                self.discard(1);
                Ok(Expr::ColumnRef {
                    table: None,
                    column: "*".to_string(),
                })
            }
            _ => Err(self.unexpected_token_error("expression")),
        }
    }

    /// Parses a function call with arguments.
    fn parse_function_call(&mut self, name: String) -> Result<Expr, SyntaxError> {
        self.consume(TokenKind::LParen)?;

        // Check for DISTINCT
        let distinct = self.starts_with([TokenKind::Distinct]);
        if distinct {
            self.discard(1);
        }

        // Check for empty argument list or wildcard
        if matches!(self.peek(0), Some(TokenKind::RParen)) {
            self.discard(1);
            return Ok(Expr::Function {
                name,
                args: vec![],
                distinct,
            });
        }

        // Check for COUNT(*)
        if matches!(self.peek(0), Some(TokenKind::Asterisk)) {
            self.discard(1);
            self.consume(TokenKind::RParen)?;
            return Ok(Expr::Function {
                name,
                args: vec![Expr::ColumnRef {
                    table: None,
                    column: "*".to_string(),
                }],
                distinct,
            });
        }

        // Parse argument list
        let args = self.parse_comma_separated(Self::parse_expr)?;

        self.consume(TokenKind::RParen)?;

        Ok(Expr::Function {
            name,
            args,
            distinct,
        })
    }

    /// Parses a CASE expression.
    ///
    /// Supports both simple CASE (CASE expr WHEN value THEN result)
    /// and searched CASE (CASE WHEN condition THEN result).
    fn parse_case_expr(&mut self) -> Result<Expr, SyntaxError> {
        // Check for simple CASE (has operand)
        let operand = if !self.starts_with([TokenKind::When]) {
            Some(Box::new(self.parse_expr()?))
        } else {
            None
        };

        // Parse WHEN clauses
        let mut when_clauses = Vec::new();
        while self.starts_with([TokenKind::When]) {
            self.discard(1);
            let condition = self.parse_expr()?;
            self.consume(TokenKind::Then)?;
            let result = self.parse_expr()?;
            when_clauses.push(WhenClause { condition, result });
        }

        if when_clauses.is_empty() {
            return Err(self.unexpected_token_error("WHEN in CASE expression"));
        }

        // Parse optional ELSE
        let else_result = self
            .parse_if_token(TokenKind::Else, Self::parse_expr)?
            .map(Box::new);

        self.consume(TokenKind::End)?;

        Ok(Expr::Case {
            operand,
            when_clauses,
            else_result,
        })
    }

    /// Peeks at the next token and returns the binary operator and its precedence.
    fn peek_binary_op(&self) -> Option<(BinaryOperator, Precedence)> {
        match self.peek(0)? {
            TokenKind::Or => Some((BinaryOperator::Or, Precedence::Or)),
            TokenKind::And => Some((BinaryOperator::And, Precedence::And)),
            TokenKind::Eq => Some((BinaryOperator::Eq, Precedence::Comparison)),
            TokenKind::Neq => Some((BinaryOperator::Neq, Precedence::Comparison)),
            TokenKind::Lt => Some((BinaryOperator::Lt, Precedence::Comparison)),
            TokenKind::LtEq => Some((BinaryOperator::LtEq, Precedence::Comparison)),
            TokenKind::Gt => Some((BinaryOperator::Gt, Precedence::Comparison)),
            TokenKind::GtEq => Some((BinaryOperator::GtEq, Precedence::Comparison)),
            TokenKind::Concat => Some((BinaryOperator::Concat, Precedence::Concat)),
            TokenKind::Plus => Some((BinaryOperator::Add, Precedence::AddSub)),
            TokenKind::Minus => Some((BinaryOperator::Sub, Precedence::AddSub)),
            TokenKind::Asterisk => Some((BinaryOperator::Mul, Precedence::MulDiv)),
            TokenKind::Slash => Some((BinaryOperator::Div, Precedence::MulDiv)),
            TokenKind::Percent => Some((BinaryOperator::Mod, Precedence::MulDiv)),
            _ => None,
        }
    }

    // ==================== Parsing utilities ====================

    /// Parses something only if the specified token is present.
    fn parse_if_token<T>(
        &mut self,
        kind: TokenKind,
        f: impl FnOnce(&mut Self) -> Result<T, SyntaxError>,
    ) -> Result<Option<T>, SyntaxError> {
        if self.peek(0) == Some(&kind) {
            self.discard(1);
            Ok(Some(f(self)?))
        } else {
            Ok(None)
        }
    }

    /// Parses content within parentheses.
    fn parse_parenthesized<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<T, SyntaxError>,
    ) -> Result<T, SyntaxError> {
        self.consume(TokenKind::LParen)?;
        let result = f(self)?;
        self.consume(TokenKind::RParen)?;
        Ok(result)
    }

    /// Parses a comma-separated list of items.
    fn parse_comma_separated<T>(
        &mut self,
        mut f: impl FnMut(&mut Self) -> Result<T, SyntaxError>,
    ) -> Result<Vec<T>, SyntaxError> {
        let mut items = vec![f(self)?];
        while matches!(self.peek(0), Some(TokenKind::Comma)) {
            self.discard(1);
            items.push(f(self)?);
        }
        Ok(items)
    }

    /// Parses an optional alias (with or without AS keyword).
    fn parse_as(&mut self) -> Result<Option<String>, SyntaxError> {
        if self.starts_with([TokenKind::As]) {
            self.discard(1);
            return Ok(Some(self.consume_identifier()?));
        }
        // Alias without AS: identifier that's not a reserved keyword
        if let Some(TokenKind::Identifier(name)) = self.peek(0) {
            let alias = name.clone();
            self.discard(1);
            return Ok(Some(alias));
        }
        Ok(None)
    }

    /// Parses optional IF NOT EXISTS clause.
    fn parse_if_not_exists(&mut self) -> Result<bool, SyntaxError> {
        if self.starts_with([TokenKind::If, TokenKind::Not, TokenKind::Exists]) {
            self.discard(3);
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Parses optional IF EXISTS clause.
    fn parse_if_exists(&mut self) -> Result<bool, SyntaxError> {
        if self.starts_with([TokenKind::If, TokenKind::Exists]) {
            self.discard(2);
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Parses sort direction (ASC/DESC).
    fn parse_sort_direction(&mut self) -> SortDirection {
        match self.peek(0) {
            Some(TokenKind::Asc) => {
                self.discard(1);
                SortDirection::Asc
            }
            Some(TokenKind::Desc) => {
                self.discard(1);
                SortDirection::Desc
            }
            _ => SortDirection::default(),
        }
    }

    /// Parses NULL ordering (NULLS FIRST/LAST).
    fn parse_null_ordering(&mut self) -> Result<NullOrdering, SyntaxError> {
        if self.starts_with([TokenKind::Nulls, TokenKind::First]) {
            self.discard(2);
            Ok(NullOrdering::First)
        } else if self.starts_with([TokenKind::Nulls, TokenKind::Last]) {
            self.discard(2);
            Ok(NullOrdering::Last)
        } else if self.starts_with([TokenKind::Nulls]) {
            self.discard(1);
            Err(self.unexpected_token_error("FIRST or LAST"))
        } else {
            Ok(NullOrdering::default())
        }
    }

    /// Parses a comma-separated list of identifiers.
    fn parse_identifier_list(&mut self) -> Result<Vec<String>, SyntaxError> {
        self.parse_comma_separated(Self::consume_identifier)
    }

    /// Parses a comma-separated list of expressions.
    fn parse_expr_list(&mut self) -> Result<Vec<Expr>, SyntaxError> {
        self.parse_comma_separated(Self::parse_expr)
    }

    // ==================== Token utilities ====================

    // --- Peek operations ---

    /// Peeks at the kind of a token at the given offset from current position.
    fn peek(&self, nth: usize) -> Option<&TokenKind> {
        self.tokens.get(self.pos + nth).map(|t| &t.kind)
    }

    /// Checks if the next tokens match the given token sequence.
    fn starts_with<const N: usize>(&self, tokens: [TokenKind; N]) -> bool {
        tokens
            .into_iter()
            .enumerate()
            .all(|(i, kind)| self.peek(i) == Some(&kind))
    }

    // --- Consume operations ---

    /// Advances by the given number of tokens.
    fn discard(&mut self, count: usize) {
        self.pos = (self.pos + count).min(self.tokens.len());
    }

    /// Expects a specific token, returning an error if not found.
    fn consume(&mut self, kind: TokenKind) -> Result<(), SyntaxError> {
        if self.peek(0) == Some(&kind) {
            self.discard(1);
            Ok(())
        } else {
            Err(self.unexpected_token_error(&kind.display_name()))
        }
    }

    /// Expects an identifier, returning its name.
    fn consume_identifier(&mut self) -> Result<String, SyntaxError> {
        match self.peek(0) {
            Some(TokenKind::Identifier(name) | TokenKind::QuotedIdentifier(name)) => {
                let name = name.clone();
                self.discard(1);
                Ok(name)
            }
            _ => Err(self.unexpected_token_error("identifier")),
        }
    }

    /// Expects an integer literal.
    fn consume_integer(&mut self) -> Result<i64, SyntaxError> {
        match self.peek(0) {
            Some(TokenKind::Integer(n)) => {
                let n = *n;
                self.discard(1);
                Ok(n)
            }
            _ => Err(self.unexpected_token_error("integer")),
        }
    }

    // --- Error helpers ---

    /// Creates an unexpected token error with the current position.
    fn unexpected_token_error(&self, expected: &str) -> SyntaxError {
        let current_span = self
            .tokens
            .get(self.pos)
            .map_or(Span::at(self.input.len()), |t| t.span);
        let current_token_name = self
            .peek(0)
            .map_or("end of input".to_string(), |k| k.display_name());
        SyntaxError::unexpected_token(expected, &current_token_name, current_span)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(sql: &str) -> Result<Statement, SyntaxError> {
        Parser::new(sql)
            .parse()
            .and_then(|opt| opt.ok_or_else(|| SyntaxError::new("empty query", Span::at(0))))
    }

    #[test]
    fn test_empty_query() {
        assert!(Parser::new("").parse().unwrap().is_none());
        assert!(Parser::new("   ").parse().unwrap().is_none());
        assert!(Parser::new("  \n\t  ").parse().unwrap().is_none());
        assert!(Parser::new("-- comment").parse().unwrap().is_none());
        assert!(Parser::new("/* block */").parse().unwrap().is_none());
    }

    #[test]
    fn test_begin_commit_rollback() {
        assert_eq!(parse("BEGIN").unwrap(), Statement::Begin);
        assert_eq!(parse("BEGIN TRANSACTION").unwrap(), Statement::Begin);
        assert_eq!(parse("COMMIT").unwrap(), Statement::Commit);
        assert_eq!(parse("ROLLBACK").unwrap(), Statement::Rollback);
    }

    #[test]
    fn test_set() {
        let Statement::Set(s) = parse("SET foo = 42").unwrap() else {
            panic!("expected SET");
        };
        assert_eq!(s.name, "foo");
        assert_eq!(s.value, Expr::Integer(42));
    }

    #[test]
    fn test_create_table_basic() {
        let Statement::CreateTable(ct) =
            parse("CREATE TABLE users (id INTEGER, name TEXT)").unwrap()
        else {
            panic!("expected CREATE TABLE");
        };
        assert_eq!(ct.name, "users");
        assert_eq!(ct.columns.len(), 2);
        assert_eq!(ct.columns[0].name, "id");
        assert_eq!(ct.columns[0].data_type, DataType::Integer);
        assert_eq!(ct.columns[1].name, "name");
        assert_eq!(ct.columns[1].data_type, DataType::Text);
        assert!(!ct.if_not_exists);

        // IF NOT EXISTS
        let Statement::CreateTable(ct) =
            parse("CREATE TABLE IF NOT EXISTS users (id INTEGER)").unwrap()
        else {
            panic!("expected CREATE TABLE");
        };
        assert_eq!(ct.name, "users");
        assert!(ct.if_not_exists);
    }

    #[test]
    fn test_create_table_with_constraints() {
        let Statement::CreateTable(ct) = parse(
            "CREATE TABLE users (
                id SERIAL PRIMARY KEY,
                email VARCHAR(255) NOT NULL UNIQUE,
                age INTEGER CHECK (age >= 0)
            )",
        )
        .unwrap() else {
            panic!("expected CREATE TABLE");
        };
        assert_eq!(ct.columns.len(), 3);
        assert!(
            ct.columns[0]
                .constraints
                .contains(&ColumnConstraint::PrimaryKey)
        );
        assert!(
            ct.columns[1]
                .constraints
                .contains(&ColumnConstraint::NotNull)
        );
        assert!(
            ct.columns[1]
                .constraints
                .contains(&ColumnConstraint::Unique)
        );
    }

    #[test]
    fn test_select_basic() {
        let Statement::Select(s) = parse("SELECT 1").unwrap() else {
            panic!("expected SELECT");
        };
        assert_eq!(s.columns.len(), 1);
        assert!(s.from.is_none());
    }

    #[test]
    fn test_select_columns() {
        let Statement::Select(s) = parse("SELECT id, name FROM users").unwrap() else {
            panic!("expected SELECT");
        };
        assert_eq!(s.columns.len(), 2);
        assert!(s.from.is_some());
    }

    #[test]
    fn test_select_wildcard() {
        let Statement::Select(s) = parse("SELECT * FROM users").unwrap() else {
            panic!("expected SELECT");
        };
        assert!(matches!(s.columns[0], SelectItem::Wildcard));
    }

    #[test]
    fn test_select_qualified_wildcard() {
        let Statement::Select(s) = parse("SELECT u.* FROM users u").unwrap() else {
            panic!("expected SELECT");
        };
        assert!(matches!(
            &s.columns[0],
            SelectItem::QualifiedWildcard(name) if name == "u"
        ));
    }

    #[test]
    fn test_select_with_alias() {
        let Statement::Select(s) = parse("SELECT id AS user_id FROM users").unwrap() else {
            panic!("expected SELECT");
        };
        let SelectItem::Expr { alias, .. } = &s.columns[0] else {
            panic!("expected Expr");
        };
        assert_eq!(alias.as_deref(), Some("user_id"));
    }

    #[test]
    fn test_select_where() {
        let Statement::Select(s) = parse("SELECT * FROM users WHERE active = TRUE").unwrap() else {
            panic!("expected SELECT");
        };
        assert!(s.where_clause.is_some());
    }

    #[test]
    fn test_select_group_by() {
        let Statement::Select(s) = parse("SELECT dept, COUNT(*) FROM emp GROUP BY dept").unwrap()
        else {
            panic!("expected SELECT");
        };
        assert_eq!(s.group_by.len(), 1);
    }

    #[test]
    fn test_select_order_by() {
        let Statement::Select(s) = parse("SELECT * FROM users ORDER BY name ASC, id DESC").unwrap()
        else {
            panic!("expected SELECT");
        };
        assert_eq!(s.order_by.len(), 2);
        assert_eq!(s.order_by[0].direction, SortDirection::Asc);
        assert_eq!(s.order_by[1].direction, SortDirection::Desc);
    }

    #[test]
    fn test_select_limit_offset() {
        let Statement::Select(s) = parse("SELECT * FROM users LIMIT 10 OFFSET 5").unwrap() else {
            panic!("expected SELECT");
        };
        assert!(s.limit.is_some());
        assert!(s.offset.is_some());
    }

    #[test]
    fn test_select_join() {
        let Statement::Select(s) =
            parse("SELECT * FROM users u INNER JOIN orders o ON u.id = o.user_id").unwrap()
        else {
            panic!("expected SELECT");
        };
        let from = s.from.unwrap();
        assert!(matches!(from.tables[0], TableRef::Join { .. }));
    }

    #[test]
    fn test_insert() {
        let Statement::Insert(i) =
            parse("INSERT INTO users (id, name) VALUES (1, 'Alice')").unwrap()
        else {
            panic!("expected INSERT");
        };
        assert_eq!(i.table, "users");
        assert_eq!(i.columns, vec!["id", "name"]);
        assert_eq!(i.values.len(), 1);
        assert_eq!(i.values[0].len(), 2);
    }

    #[test]
    fn test_insert_multi_row() {
        let Statement::Insert(i) =
            parse("INSERT INTO users VALUES (1, 'Alice'), (2, 'Bob')").unwrap()
        else {
            panic!("expected INSERT");
        };
        assert_eq!(i.values.len(), 2);
    }

    #[test]
    fn test_update() {
        let Statement::Update(u) = parse("UPDATE users SET name = 'Bob' WHERE id = 1").unwrap()
        else {
            panic!("expected UPDATE");
        };
        assert_eq!(u.table, "users");
        assert_eq!(u.assignments.len(), 1);
        assert_eq!(u.assignments[0].column, "name");
        assert!(u.where_clause.is_some());
    }

    #[test]
    fn test_delete() {
        let Statement::Delete(d) = parse("DELETE FROM users WHERE id = 1").unwrap() else {
            panic!("expected DELETE");
        };
        assert_eq!(d.table, "users");
        assert!(d.where_clause.is_some());
    }

    #[test]
    fn test_explain() {
        let stmt = parse("EXPLAIN SELECT * FROM users").unwrap();
        assert!(matches!(stmt, Statement::Explain(_)));
    }

    #[test]
    fn test_trailing_semicolon() {
        assert!(parse("SELECT 1;").is_ok());
        assert!(parse("BEGIN;").is_ok());
    }

    #[test]
    fn test_syntax_error() {
        let err = parse("SELECTT * FROM users").unwrap_err();
        assert!(err.message.contains("expected"));
    }

    #[test]
    fn test_for_update() {
        let Statement::Select(s) = parse("SELECT * FROM users FOR UPDATE").unwrap() else {
            panic!("expected SELECT");
        };
        assert!(matches!(
            s.locking,
            Some(LockingClause {
                mode: LockMode::Update
            })
        ));
    }

    #[test]
    fn test_drop_table() {
        let Statement::DropTable(dt) = parse("DROP TABLE users").unwrap() else {
            panic!("expected DROP TABLE");
        };
        assert_eq!(dt.name, "users");
        assert!(!dt.if_exists);
    }

    #[test]
    fn test_drop_table_if_exists() {
        let Statement::DropTable(dt) = parse("DROP TABLE IF EXISTS users").unwrap() else {
            panic!("expected DROP TABLE");
        };
        assert_eq!(dt.name, "users");
        assert!(dt.if_exists);
    }

    #[test]
    fn test_create_index() {
        let Statement::CreateIndex(ci) = parse("CREATE INDEX idx_name ON users (name)").unwrap()
        else {
            panic!("expected CREATE INDEX");
        };
        assert_eq!(ci.name, "idx_name");
        assert_eq!(ci.table, "users");
        assert_eq!(ci.columns.len(), 1);
        assert_eq!(ci.columns[0].name, "name");
        assert!(!ci.unique);
        assert!(!ci.if_not_exists);
    }

    #[test]
    fn test_create_unique_index() {
        let Statement::CreateIndex(ci) =
            parse("CREATE UNIQUE INDEX IF NOT EXISTS idx_email ON users (email DESC)").unwrap()
        else {
            panic!("expected CREATE INDEX");
        };
        assert_eq!(ci.name, "idx_email");
        assert_eq!(ci.table, "users");
        assert!(ci.unique);
        assert!(ci.if_not_exists);
        assert_eq!(ci.columns[0].direction, SortDirection::Desc);
    }

    #[test]
    fn test_create_index_multi_column() {
        let Statement::CreateIndex(ci) =
            parse("CREATE INDEX idx_multi ON orders (user_id ASC, created_at DESC)").unwrap()
        else {
            panic!("expected CREATE INDEX");
        };
        assert_eq!(ci.columns.len(), 2);
        assert_eq!(ci.columns[0].name, "user_id");
        assert_eq!(ci.columns[1].name, "created_at");
    }

    #[test]
    fn test_drop_index() {
        let Statement::DropIndex(di) = parse("DROP INDEX idx_name").unwrap() else {
            panic!("expected DROP INDEX");
        };
        assert_eq!(di.name, "idx_name");
        assert!(!di.if_exists);
    }

    #[test]
    fn test_drop_index_if_exists() {
        let Statement::DropIndex(di) = parse("DROP INDEX IF EXISTS idx_name").unwrap() else {
            panic!("expected DROP INDEX");
        };
        assert!(di.if_exists);
    }

    // ==================== Expression tests ====================

    fn parse_expr(input: &str) -> Result<Expr, SyntaxError> {
        Parser::new(input).parse_expr()
    }

    #[test]
    fn test_expr_literals() {
        assert_eq!(parse_expr("NULL").unwrap(), Expr::Null);
        assert_eq!(parse_expr("TRUE").unwrap(), Expr::Boolean(true));
        assert_eq!(parse_expr("FALSE").unwrap(), Expr::Boolean(false));
        assert_eq!(parse_expr("42").unwrap(), Expr::Integer(42));
        assert_eq!(parse_expr("3.14").unwrap(), Expr::Float(3.14));
        assert_eq!(
            parse_expr("'hello'").unwrap(),
            Expr::String("hello".to_string())
        );
    }

    #[test]
    fn test_expr_column_ref() {
        assert_eq!(
            parse_expr("foo").unwrap(),
            Expr::ColumnRef {
                table: None,
                column: "foo".to_string()
            }
        );
        assert_eq!(
            parse_expr("t.foo").unwrap(),
            Expr::ColumnRef {
                table: Some("t".to_string()),
                column: "foo".to_string()
            }
        );
    }

    #[test]
    fn test_expr_parameter() {
        assert_eq!(parse_expr("$1").unwrap(), Expr::Parameter(1));
        assert_eq!(parse_expr("$42").unwrap(), Expr::Parameter(42));
    }

    #[test]
    fn test_expr_binary_ops() {
        let expr = parse_expr("1 + 2").unwrap();
        assert!(matches!(
            expr,
            Expr::BinaryOp {
                op: BinaryOperator::Add,
                ..
            }
        ));

        let expr = parse_expr("a = b").unwrap();
        assert!(matches!(
            expr,
            Expr::BinaryOp {
                op: BinaryOperator::Eq,
                ..
            }
        ));
    }

    #[test]
    fn test_expr_precedence() {
        // 1 + 2 * 3 should be 1 + (2 * 3)
        let expr = parse_expr("1 + 2 * 3").unwrap();
        match expr {
            Expr::BinaryOp { op, left, right } => {
                assert_eq!(op, BinaryOperator::Add);
                assert!(matches!(*left, Expr::Integer(1)));
                assert!(matches!(
                    *right,
                    Expr::BinaryOp {
                        op: BinaryOperator::Mul,
                        ..
                    }
                ));
            }
            _ => panic!("expected BinaryOp"),
        }

        // a AND b OR c should be (a AND b) OR c
        let expr = parse_expr("a AND b OR c").unwrap();
        match expr {
            Expr::BinaryOp { op, .. } => {
                assert_eq!(op, BinaryOperator::Or);
            }
            _ => panic!("expected BinaryOp"),
        }
    }

    #[test]
    fn test_expr_unary_ops() {
        let expr = parse_expr("-5").unwrap();
        assert!(matches!(
            expr,
            Expr::UnaryOp {
                op: UnaryOperator::Minus,
                ..
            }
        ));

        let expr = parse_expr("NOT TRUE").unwrap();
        assert!(matches!(
            expr,
            Expr::UnaryOp {
                op: UnaryOperator::Not,
                ..
            }
        ));
    }

    #[test]
    fn test_expr_is_null() {
        let expr = parse_expr("x IS NULL").unwrap();
        assert!(matches!(expr, Expr::IsNull { negated: false, .. }));

        let expr = parse_expr("x IS NOT NULL").unwrap();
        assert!(matches!(expr, Expr::IsNull { negated: true, .. }));
    }

    #[test]
    fn test_expr_function_call() {
        let Expr::Function {
            name,
            args,
            distinct,
        } = parse_expr("COUNT(*)").unwrap()
        else {
            panic!("expected Function");
        };
        assert_eq!(name, "COUNT");
        assert_eq!(args.len(), 1);
        assert!(!distinct);

        let Expr::Function { name, distinct, .. } = parse_expr("SUM(DISTINCT x)").unwrap() else {
            panic!("expected Function");
        };
        assert_eq!(name, "SUM");
        assert!(distinct);
    }

    #[test]
    fn test_expr_parenthesized() {
        // Parentheses control precedence but don't create AST nodes
        let Expr::BinaryOp { op, left, .. } = parse_expr("(1 + 2) * 3").unwrap() else {
            panic!("expected BinaryOp");
        };
        assert_eq!(op, BinaryOperator::Mul);
        assert!(matches!(
            *left,
            Expr::BinaryOp {
                op: BinaryOperator::Add,
                ..
            }
        ));
    }

    #[test]
    fn test_expr_in_list() {
        let expr = parse_expr("x IN (1, 2, 3)").unwrap();
        assert!(matches!(expr, Expr::InList { negated: false, .. }));

        let expr = parse_expr("x NOT IN (1, 2, 3)").unwrap();
        assert!(matches!(expr, Expr::InList { negated: true, .. }));
    }

    #[test]
    fn test_expr_between() {
        let expr = parse_expr("x BETWEEN 1 AND 10").unwrap();
        assert!(matches!(expr, Expr::Between { negated: false, .. }));

        let expr = parse_expr("x NOT BETWEEN 1 AND 10").unwrap();
        assert!(matches!(expr, Expr::Between { negated: true, .. }));
    }

    #[test]
    fn test_expr_like() {
        let expr = parse_expr("name LIKE 'A%'").unwrap();
        assert!(matches!(
            expr,
            Expr::Like {
                negated: false,
                case_insensitive: false,
                ..
            }
        ));

        let expr = parse_expr("name NOT LIKE '%test%'").unwrap();
        assert!(matches!(expr, Expr::Like { negated: true, .. }));

        let expr = parse_expr("name ILIKE 'test'").unwrap();
        assert!(matches!(
            expr,
            Expr::Like {
                case_insensitive: true,
                ..
            }
        ));
    }

    #[test]
    fn test_expr_like_escape() {
        let Expr::Like { escape, .. } = parse_expr("name LIKE '%\\%%' ESCAPE '\\'").unwrap() else {
            panic!("expected Like");
        };
        assert!(escape.is_some());
    }

    #[test]
    fn test_expr_exists() {
        let expr = parse_expr("EXISTS (SELECT 1)").unwrap();
        assert!(matches!(expr, Expr::Exists { negated: false, .. }));
    }

    #[test]
    fn test_expr_case_searched() {
        let Expr::Case {
            operand,
            when_clauses,
            else_result,
        } = parse_expr("CASE WHEN x > 0 THEN 'positive' ELSE 'non-positive' END").unwrap()
        else {
            panic!("expected Case");
        };
        assert!(operand.is_none());
        assert_eq!(when_clauses.len(), 1);
        assert!(else_result.is_some());
    }

    #[test]
    fn test_expr_case_simple() {
        let Expr::Case {
            operand,
            when_clauses,
            else_result,
        } = parse_expr("CASE status WHEN 1 THEN 'active' WHEN 2 THEN 'inactive' END").unwrap()
        else {
            panic!("expected Case");
        };
        assert!(operand.is_some());
        assert_eq!(when_clauses.len(), 2);
        assert!(else_result.is_none());
    }

    #[test]
    fn test_expr_cast_function() {
        let Expr::Cast { data_type, .. } = parse_expr("CAST(123 AS TEXT)").unwrap() else {
            panic!("expected Cast");
        };
        assert_eq!(data_type, DataType::Text);
    }

    #[test]
    fn test_expr_cast_double_colon() {
        let Expr::Cast { data_type, .. } = parse_expr("123::TEXT").unwrap() else {
            panic!("expected Cast");
        };
        assert_eq!(data_type, DataType::Text);
    }

    #[test]
    fn test_expr_cast_chain() {
        // 123::TEXT::VARCHAR should be ((123::TEXT)::VARCHAR)
        let Expr::Cast {
            expr: inner,
            data_type,
        } = parse_expr("123::TEXT::VARCHAR").unwrap()
        else {
            panic!("expected Cast");
        };
        assert_eq!(data_type, DataType::Varchar(None));
        assert!(matches!(*inner, Expr::Cast { .. }));
    }
}
