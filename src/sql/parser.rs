//! SQL parser using recursive descent.
//!
//! The [`Parser`] converts a stream of tokens into an Abstract Syntax Tree (AST).
//! It uses recursive descent for most constructs and precedence climbing for
//! expression parsing.

use super::ast::*;
use super::error::{SyntaxError, Span};
use super::lexer::Lexer;
use super::token::{Keyword, Token, TokenKind};

/// SQL parser that converts tokens into an AST.
///
/// The parser implements recursive descent parsing for SQL statements.
/// Expression parsing uses precedence climbing (see `expr.rs`).
pub struct Parser<'a> {
    tokens: Vec<Token>,
    pos: usize,
    input: &'a str,
}

impl<'a> Parser<'a> {
    /// Creates a new parser for the given SQL input.
    pub fn new(input: &'a str) -> Self {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize();

        // NOTE: Lexer errors are accumulated and could be checked here.
        // For simplicity, we proceed with whatever tokens we got.

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
        if self.is_eof() {
            return Ok(None);
        }

        let stmt = self.parse_statement()?;

        // Optional trailing semicolon
        self.consume_token(TokenKind::Semicolon);

        // Check for unexpected trailing tokens
        if !self.is_eof() {
            let span = self.current_span();
            return Err(SyntaxError::unexpected_token(
                "end of input",
                &self.current_token_name(),
                span,
            ));
        }

        Ok(Some(stmt))
    }

    /// Parses a single statement.
    fn parse_statement(&mut self) -> Result<Statement, SyntaxError> {
        // Handle EXPLAIN prefix
        if self.consume_keyword(Keyword::Explain) {
            let inner = self.parse_statement()?;
            return Ok(Statement::Explain(Box::new(inner)));
        }

        // Transaction control
        if self.consume_keyword(Keyword::Begin) {
            // Optional: TRANSACTION
            self.consume_keyword(Keyword::Transaction);
            return Ok(Statement::Begin);
        }

        if self.check_keyword(Keyword::Start) {
            self.advance();
            self.expect_keyword(Keyword::Transaction)?;
            return Ok(Statement::Begin);
        }

        if self.consume_keyword(Keyword::Commit) {
            return Ok(Statement::Commit);
        }

        if self.consume_keyword(Keyword::Rollback) {
            return Ok(Statement::Rollback);
        }

        // SET statement
        if self.consume_keyword(Keyword::Set) {
            return self.parse_set_stmt();
        }

        // CREATE TABLE / CREATE INDEX
        if self.consume_keyword(Keyword::Create) {
            if self.consume_keyword(Keyword::Table) {
                return self.parse_create_table_stmt();
            }
            // CREATE [UNIQUE] INDEX
            let unique = self.consume_keyword(Keyword::Unique);
            if self.consume_keyword(Keyword::Index) {
                return self.parse_create_index_stmt(unique);
            }
            if unique {
                // Had UNIQUE but not INDEX
                let span = self.current_span();
                return Err(SyntaxError::unexpected_token(
                    "INDEX after UNIQUE",
                    &self.current_token_name(),
                    span,
                ));
            }
            let span = self.current_span();
            return Err(SyntaxError::unexpected_token(
                "TABLE or INDEX",
                &self.current_token_name(),
                span,
            ));
        }

        // DROP TABLE / DROP INDEX
        if self.consume_keyword(Keyword::Drop) {
            if self.consume_keyword(Keyword::Table) {
                return self.parse_drop_table_stmt();
            }
            if self.consume_keyword(Keyword::Index) {
                return self.parse_drop_index_stmt();
            }
            let span = self.current_span();
            return Err(SyntaxError::unexpected_token(
                "TABLE or INDEX",
                &self.current_token_name(),
                span,
            ));
        }

        // SELECT
        if self.check_keyword(Keyword::Select) {
            let select = self.parse_select_stmt()?;
            return Ok(Statement::Select(Box::new(select)));
        }

        // INSERT
        if self.consume_keyword(Keyword::Insert) {
            return self.parse_insert_stmt();
        }

        // UPDATE
        if self.consume_keyword(Keyword::Update) {
            return self.parse_update_stmt();
        }

        // DELETE
        if self.consume_keyword(Keyword::Delete) {
            return self.parse_delete_stmt();
        }

        let span = self.current_span();
        Err(SyntaxError::unexpected_token(
            "statement",
            &self.current_token_name(),
            span,
        ))
    }

    /// Parses a SET statement.
    fn parse_set_stmt(&mut self) -> Result<Statement, SyntaxError> {
        let name = self.expect_identifier()?;

        // SET name = value or SET name TO value
        if !self.consume_token(TokenKind::Eq) {
            // PostgreSQL also accepts "TO" instead of "="
            if let Some(TokenKind::Identifier(s)) = self.peek_kind() {
                if s.eq_ignore_ascii_case("to") {
                    self.advance();
                } else {
                    return Err(SyntaxError::unexpected_token(
                        "'=' or 'TO'",
                        &self.current_token_name(),
                        self.current_span(),
                    ));
                }
            }
        }

        let value = self.parse_expr()?;

        Ok(Statement::Set(SetStmt { name, value }))
    }

    /// Parses a CREATE TABLE statement.
    fn parse_create_table_stmt(&mut self) -> Result<Statement, SyntaxError> {
        let name = self.expect_identifier()?;

        self.expect_token(TokenKind::LParen)?;

        let mut columns = Vec::new();
        let mut constraints = Vec::new();

        loop {
            // Check for table-level constraint
            if self.check_keyword(Keyword::Primary)
                || self.check_keyword(Keyword::Unique)
                || self.check_keyword(Keyword::Foreign)
                || self.check_keyword(Keyword::Check)
                || self.check_keyword(Keyword::Constraint)
            {
                constraints.push(self.parse_table_constraint()?);
            } else {
                columns.push(self.parse_column_def()?);
            }

            if !self.consume_token(TokenKind::Comma) {
                break;
            }
        }

        self.expect_token(TokenKind::RParen)?;

        Ok(Statement::CreateTable(Box::new(CreateTableStmt {
            name,
            columns,
            constraints,
        })))
    }

    /// Parses a column definition.
    fn parse_column_def(&mut self) -> Result<ColumnDef, SyntaxError> {
        let name = self.expect_identifier()?;
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
        // BOOLEAN
        if self.consume_keyword(Keyword::Boolean) {
            return Ok(DataType::Boolean);
        }

        // SMALLINT
        if self.consume_keyword(Keyword::Smallint) {
            return Ok(DataType::Smallint);
        }

        // INTEGER or INT
        if self.consume_keyword(Keyword::Integer) || self.consume_keyword(Keyword::Int) {
            return Ok(DataType::Integer);
        }

        // BIGINT
        if self.consume_keyword(Keyword::Bigint) {
            return Ok(DataType::Bigint);
        }

        // REAL
        if self.consume_keyword(Keyword::Real) {
            return Ok(DataType::Real);
        }

        // DOUBLE PRECISION
        if self.consume_keyword(Keyword::Double) {
            self.expect_keyword(Keyword::Precision)?;
            return Ok(DataType::DoublePrecision);
        }

        // TEXT
        if self.consume_keyword(Keyword::Text) {
            return Ok(DataType::Text);
        }

        // VARCHAR(n)
        if self.consume_keyword(Keyword::Varchar) {
            let length = if self.consume_token(TokenKind::LParen) {
                let n = self.expect_integer()?;
                self.expect_token(TokenKind::RParen)?;
                Some(n as u32)
            } else {
                None
            };
            return Ok(DataType::Varchar(length));
        }

        // BYTEA
        if self.consume_keyword(Keyword::Bytea) {
            return Ok(DataType::Bytea);
        }

        // SERIAL
        if self.consume_keyword(Keyword::Serial) {
            return Ok(DataType::Serial);
        }

        let span = self.current_span();
        Err(SyntaxError::unexpected_token(
            "data type",
            &self.current_token_name(),
            span,
        ))
    }

    /// Parses column constraints.
    fn parse_column_constraints(&mut self) -> Result<Vec<ColumnConstraint>, SyntaxError> {
        let mut constraints = Vec::new();

        loop {
            if self.consume_keyword(Keyword::Not) {
                self.expect_keyword(Keyword::Null)?;
                constraints.push(ColumnConstraint::NotNull);
            } else if self.consume_keyword(Keyword::Null) {
                constraints.push(ColumnConstraint::Null);
            } else if self.consume_keyword(Keyword::Primary) {
                self.expect_keyword(Keyword::Key)?;
                constraints.push(ColumnConstraint::PrimaryKey);
            } else if self.consume_keyword(Keyword::Unique) {
                constraints.push(ColumnConstraint::Unique);
            } else if self.consume_keyword(Keyword::Default) {
                let value = self.parse_expr()?;
                constraints.push(ColumnConstraint::Default(value));
            } else if self.consume_keyword(Keyword::Check) {
                self.expect_token(TokenKind::LParen)?;
                let expr = self.parse_expr()?;
                self.expect_token(TokenKind::RParen)?;
                constraints.push(ColumnConstraint::Check(expr));
            } else if self.consume_keyword(Keyword::References) {
                let table = self.expect_identifier()?;
                let column = if self.consume_token(TokenKind::LParen) {
                    let col = self.expect_identifier()?;
                    self.expect_token(TokenKind::RParen)?;
                    Some(col)
                } else {
                    None
                };
                constraints.push(ColumnConstraint::References { table, column });
            } else {
                break;
            }
        }

        Ok(constraints)
    }

    /// Parses a table-level constraint.
    fn parse_table_constraint(&mut self) -> Result<TableConstraint, SyntaxError> {
        let name = if self.consume_keyword(Keyword::Constraint) {
            Some(self.expect_identifier()?)
        } else {
            None
        };

        let kind = if self.consume_keyword(Keyword::Primary) {
            self.expect_keyword(Keyword::Key)?;
            self.expect_token(TokenKind::LParen)?;
            let columns = self.parse_identifier_list()?;
            self.expect_token(TokenKind::RParen)?;
            TableConstraintKind::PrimaryKey(columns)
        } else if self.consume_keyword(Keyword::Unique) {
            self.expect_token(TokenKind::LParen)?;
            let columns = self.parse_identifier_list()?;
            self.expect_token(TokenKind::RParen)?;
            TableConstraintKind::Unique(columns)
        } else if self.consume_keyword(Keyword::Check) {
            self.expect_token(TokenKind::LParen)?;
            let expr = self.parse_expr()?;
            self.expect_token(TokenKind::RParen)?;
            TableConstraintKind::Check(expr)
        } else if self.consume_keyword(Keyword::Foreign) {
            self.expect_keyword(Keyword::Key)?;
            self.expect_token(TokenKind::LParen)?;
            let columns = self.parse_identifier_list()?;
            self.expect_token(TokenKind::RParen)?;
            self.expect_keyword(Keyword::References)?;
            let ref_table = self.expect_identifier()?;
            self.expect_token(TokenKind::LParen)?;
            let ref_columns = self.parse_identifier_list()?;
            self.expect_token(TokenKind::RParen)?;
            TableConstraintKind::ForeignKey {
                columns,
                ref_table,
                ref_columns,
            }
        } else {
            let span = self.current_span();
            return Err(SyntaxError::unexpected_token(
                "constraint type",
                &self.current_token_name(),
                span,
            ));
        };

        Ok(TableConstraint { name, kind })
    }

    /// Parses a SELECT statement.
    pub(crate) fn parse_select_stmt(&mut self) -> Result<SelectStmt, SyntaxError> {
        self.expect_keyword(Keyword::Select)?;

        // DISTINCT / ALL
        let distinct = if self.consume_keyword(Keyword::Distinct) {
            true
        } else {
            self.consume_keyword(Keyword::All);
            false
        };

        // Select list
        let columns = self.parse_select_list()?;

        // FROM clause
        let from = if self.consume_keyword(Keyword::From) {
            Some(self.parse_from_clause()?)
        } else {
            None
        };

        // WHERE clause
        let where_clause = if self.consume_keyword(Keyword::Where) {
            Some(self.parse_expr()?)
        } else {
            None
        };

        // GROUP BY clause
        let group_by = if self.consume_keyword(Keyword::Group) {
            self.expect_keyword(Keyword::By)?;
            self.parse_expr_list()?
        } else {
            vec![]
        };

        // HAVING clause
        let having = if self.consume_keyword(Keyword::Having) {
            Some(self.parse_expr()?)
        } else {
            None
        };

        // ORDER BY clause
        let order_by = if self.consume_keyword(Keyword::Order) {
            self.expect_keyword(Keyword::By)?;
            self.parse_order_by_list()?
        } else {
            vec![]
        };

        // LIMIT clause
        let limit = if self.consume_keyword(Keyword::Limit) {
            Some(self.parse_expr()?)
        } else {
            None
        };

        // OFFSET clause
        let offset = if self.consume_keyword(Keyword::Offset) {
            Some(self.parse_expr()?)
        } else {
            None
        };

        // FOR UPDATE/SHARE
        let locking = if self.consume_keyword(Keyword::For) {
            Some(self.parse_locking_clause()?)
        } else {
            None
        };

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
        let mut items = Vec::new();

        loop {
            items.push(self.parse_select_item()?);
            if !self.consume_token(TokenKind::Comma) {
                break;
            }
        }

        Ok(items)
    }

    /// Parses a single select item.
    fn parse_select_item(&mut self) -> Result<SelectItem, SyntaxError> {
        // Check for *
        if self.consume_token(TokenKind::Asterisk) {
            return Ok(SelectItem::Wildcard);
        }

        // Check for table.* or expression
        if let Some(TokenKind::Identifier(name) | TokenKind::QuotedIdentifier(name)) =
            self.peek_kind()
        {
            let name = name.clone();

            // Look ahead for table.*
            if self.peek_nth_kind(1) == Some(&TokenKind::Dot)
                && self.peek_nth_kind(2) == Some(&TokenKind::Asterisk)
            {
                self.advance(); // identifier
                self.advance(); // .
                self.advance(); // *
                return Ok(SelectItem::QualifiedWildcard(name));
            }
        }

        // Expression with optional alias
        let expr = self.parse_expr()?;
        let alias = if self.consume_keyword(Keyword::As) {
            Some(self.expect_identifier()?)
        } else if let Some(TokenKind::Identifier(name) | TokenKind::QuotedIdentifier(name)) =
            self.peek_kind()
        {
            // Alias without AS (if next token is an identifier and not a keyword)
            if !self.check_keyword_any() {
                let alias = name.clone();
                self.advance();
                Some(alias)
            } else {
                None
            }
        } else {
            None
        };

        Ok(SelectItem::Expr { expr, alias })
    }

    /// Parses the FROM clause.
    fn parse_from_clause(&mut self) -> Result<FromClause, SyntaxError> {
        let mut tables = Vec::new();

        loop {
            let table = self.parse_table_ref()?;
            tables.push(table);

            if !self.consume_token(TokenKind::Comma) {
                break;
            }
        }

        Ok(FromClause { tables })
    }

    /// Parses a table reference.
    fn parse_table_ref(&mut self) -> Result<TableRef, SyntaxError> {
        let mut table_ref = self.parse_primary_table_ref()?;

        // Handle JOINs
        loop {
            let join_type = if self.consume_keyword(Keyword::Cross) {
                self.expect_keyword(Keyword::Join)?;
                Some(JoinType::Cross)
            } else if self.consume_keyword(Keyword::Inner) {
                self.expect_keyword(Keyword::Join)?;
                Some(JoinType::Inner)
            } else if self.consume_keyword(Keyword::Left) {
                self.consume_keyword(Keyword::Outer);
                self.expect_keyword(Keyword::Join)?;
                Some(JoinType::Left)
            } else if self.consume_keyword(Keyword::Right) {
                self.consume_keyword(Keyword::Outer);
                self.expect_keyword(Keyword::Join)?;
                Some(JoinType::Right)
            } else if self.consume_keyword(Keyword::Full) {
                self.consume_keyword(Keyword::Outer);
                self.expect_keyword(Keyword::Join)?;
                Some(JoinType::Full)
            } else if self.consume_keyword(Keyword::Join) {
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
            } else if self.consume_keyword(Keyword::On) {
                Some(JoinCondition::On(self.parse_expr()?))
            } else if self.consume_keyword(Keyword::Using) {
                self.expect_token(TokenKind::LParen)?;
                let columns = self.parse_identifier_list()?;
                self.expect_token(TokenKind::RParen)?;
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
        if self.consume_token(TokenKind::LParen) {
            let query = self.parse_select_stmt()?;
            self.expect_token(TokenKind::RParen)?;

            // Subquery alias is required
            self.consume_keyword(Keyword::As);
            let alias = self.expect_identifier()?;

            return Ok(TableRef::Subquery {
                query: Box::new(query),
                alias,
            });
        }

        // Table name
        let name = self.expect_identifier()?;
        let alias = if self.consume_keyword(Keyword::As) {
            Some(self.expect_identifier()?)
        } else if let Some(TokenKind::Identifier(alias) | TokenKind::QuotedIdentifier(alias)) =
            self.peek_kind()
        {
            // Alias without AS
            if !self.check_keyword_any() {
                let alias = alias.clone();
                self.advance();
                Some(alias)
            } else {
                None
            }
        } else {
            None
        };

        Ok(TableRef::Table { name, alias })
    }

    /// Parses ORDER BY item list.
    fn parse_order_by_list(&mut self) -> Result<Vec<OrderByItem>, SyntaxError> {
        let mut items = Vec::new();

        loop {
            let expr = self.parse_expr()?;

            let direction = if self.consume_keyword(Keyword::Asc) {
                SortDirection::Asc
            } else if self.consume_keyword(Keyword::Desc) {
                SortDirection::Desc
            } else {
                SortDirection::default()
            };

            let nulls = if self.consume_keyword(Keyword::Nulls) {
                if self.consume_keyword(Keyword::First) {
                    NullOrdering::First
                } else if self.consume_keyword(Keyword::Last) {
                    NullOrdering::Last
                } else {
                    let span = self.current_span();
                    return Err(SyntaxError::unexpected_token(
                        "FIRST or LAST",
                        &self.current_token_name(),
                        span,
                    ));
                }
            } else {
                NullOrdering::default()
            };

            items.push(OrderByItem {
                expr,
                direction,
                nulls,
            });

            if !self.consume_token(TokenKind::Comma) {
                break;
            }
        }

        Ok(items)
    }

    /// Parses FOR UPDATE/SHARE clause.
    fn parse_locking_clause(&mut self) -> Result<LockingClause, SyntaxError> {
        let mode = if self.consume_keyword(Keyword::Update) {
            LockMode::Update
        } else if self.consume_keyword(Keyword::Share) {
            LockMode::Share
        } else {
            let span = self.current_span();
            return Err(SyntaxError::unexpected_token(
                "UPDATE or SHARE",
                &self.current_token_name(),
                span,
            ));
        };

        Ok(LockingClause { mode })
    }

    /// Parses an INSERT statement.
    fn parse_insert_stmt(&mut self) -> Result<Statement, SyntaxError> {
        self.expect_keyword(Keyword::Into)?;
        let table = self.expect_identifier()?;

        // Optional column list
        let columns = if self.consume_token(TokenKind::LParen) {
            let cols = self.parse_identifier_list()?;
            self.expect_token(TokenKind::RParen)?;
            cols
        } else {
            vec![]
        };

        // VALUES clause
        self.expect_keyword(Keyword::Values)?;

        let mut values = Vec::new();
        loop {
            self.expect_token(TokenKind::LParen)?;
            let row = self.parse_expr_list()?;
            self.expect_token(TokenKind::RParen)?;
            values.push(row);

            if !self.consume_token(TokenKind::Comma) {
                break;
            }
        }

        Ok(Statement::Insert(Box::new(InsertStmt {
            table,
            columns,
            values,
        })))
    }

    /// Parses an UPDATE statement.
    fn parse_update_stmt(&mut self) -> Result<Statement, SyntaxError> {
        let table = self.expect_identifier()?;
        self.expect_keyword(Keyword::Set)?;

        let mut assignments = Vec::new();
        loop {
            let column = self.expect_identifier()?;
            self.expect_token(TokenKind::Eq)?;
            let value = self.parse_expr()?;
            assignments.push(Assignment { column, value });

            if !self.consume_token(TokenKind::Comma) {
                break;
            }
        }

        let where_clause = if self.consume_keyword(Keyword::Where) {
            Some(self.parse_expr()?)
        } else {
            None
        };

        Ok(Statement::Update(Box::new(UpdateStmt {
            table,
            assignments,
            where_clause,
        })))
    }

    /// Parses a DELETE statement.
    fn parse_delete_stmt(&mut self) -> Result<Statement, SyntaxError> {
        self.expect_keyword(Keyword::From)?;
        let table = self.expect_identifier()?;

        let where_clause = if self.consume_keyword(Keyword::Where) {
            Some(self.parse_expr()?)
        } else {
            None
        };

        Ok(Statement::Delete(Box::new(DeleteStmt {
            table,
            where_clause,
        })))
    }

    /// Parses a DROP TABLE statement.
    fn parse_drop_table_stmt(&mut self) -> Result<Statement, SyntaxError> {
        // DROP TABLE [IF EXISTS] name
        let if_exists = if self.consume_keyword(Keyword::If) {
            self.expect_keyword(Keyword::Exists)?;
            true
        } else {
            false
        };

        let name = self.expect_identifier()?;

        Ok(Statement::DropTable(DropTableStmt { name, if_exists }))
    }

    /// Parses a CREATE INDEX statement.
    fn parse_create_index_stmt(&mut self, unique: bool) -> Result<Statement, SyntaxError> {
        // CREATE [UNIQUE] INDEX [IF NOT EXISTS] name ON table (columns)
        let if_not_exists = if self.consume_keyword(Keyword::If) {
            self.expect_keyword(Keyword::Not)?;
            self.expect_keyword(Keyword::Exists)?;
            true
        } else {
            false
        };

        let name = self.expect_identifier()?;
        self.expect_keyword(Keyword::On)?;
        let table = self.expect_identifier()?;

        self.expect_token(TokenKind::LParen)?;
        let columns = self.parse_index_column_list()?;
        self.expect_token(TokenKind::RParen)?;

        Ok(Statement::CreateIndex(CreateIndexStmt {
            name,
            table,
            columns,
            if_not_exists,
            unique,
        }))
    }

    /// Parses a DROP INDEX statement.
    fn parse_drop_index_stmt(&mut self) -> Result<Statement, SyntaxError> {
        // DROP INDEX [IF EXISTS] name
        let if_exists = if self.consume_keyword(Keyword::If) {
            self.expect_keyword(Keyword::Exists)?;
            true
        } else {
            false
        };

        let name = self.expect_identifier()?;

        Ok(Statement::DropIndex(DropIndexStmt { name, if_exists }))
    }

    /// Parses a comma-separated list of index columns.
    fn parse_index_column_list(&mut self) -> Result<Vec<IndexColumn>, SyntaxError> {
        let mut columns = Vec::new();

        loop {
            let name = self.expect_identifier()?;
            let direction = if self.consume_keyword(Keyword::Asc) {
                SortDirection::Asc
            } else if self.consume_keyword(Keyword::Desc) {
                SortDirection::Desc
            } else {
                SortDirection::default()
            };
            columns.push(IndexColumn { name, direction });

            if !self.consume_token(TokenKind::Comma) {
                break;
            }
        }

        Ok(columns)
    }

    // ==================== Helper methods ====================

    /// Returns true if at end of tokens.
    pub(crate) fn is_eof(&self) -> bool {
        self.peek().is_none_or(|t| t.is_eof())
    }

    /// Peeks at the current token.
    pub(crate) fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    /// Peeks at the kind of the current token.
    pub(crate) fn peek_kind(&self) -> Option<&TokenKind> {
        self.peek().map(|t| &t.kind)
    }

    /// Peeks at the nth token ahead.
    fn peek_nth_kind(&self, n: usize) -> Option<&TokenKind> {
        self.tokens.get(self.pos + n).map(|t| &t.kind)
    }

    /// Advances to the next token.
    pub(crate) fn advance(&mut self) {
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
    }

    /// Returns the span of the current token.
    pub(crate) fn current_span(&self) -> Span {
        self.peek().map_or(Span::at(self.input.len()), |t| t.span)
    }

    /// Returns a display name for the current token.
    pub(crate) fn current_token_name(&self) -> String {
        self.peek()
            .map_or("end of input".to_string(), |t| t.kind.display_name())
    }

    /// Checks if the current token is a specific keyword.
    pub(crate) fn check_keyword(&self, kw: Keyword) -> bool {
        matches!(self.peek_kind(), Some(TokenKind::Keyword(k)) if *k == kw)
    }

    /// Checks if the current token is any keyword.
    fn check_keyword_any(&self) -> bool {
        matches!(self.peek_kind(), Some(TokenKind::Keyword(_)))
    }

    /// Consumes the current token if it's a specific keyword.
    pub(crate) fn consume_keyword(&mut self, kw: Keyword) -> bool {
        if self.check_keyword(kw) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Expects a specific keyword, returning an error if not found.
    pub(crate) fn expect_keyword(&mut self, kw: Keyword) -> Result<(), SyntaxError> {
        if self.consume_keyword(kw) {
            Ok(())
        } else {
            let span = self.current_span();
            Err(SyntaxError::unexpected_token(
                &format!("keyword '{}'", kw.as_str()),
                &self.current_token_name(),
                span,
            ))
        }
    }

    /// Checks if the current token matches.
    pub(crate) fn check_token(&self, kind: TokenKind) -> bool {
        self.peek_kind() == Some(&kind)
    }

    /// Consumes the current token if it matches.
    pub(crate) fn consume_token(&mut self, kind: TokenKind) -> bool {
        if self.check_token(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Expects a specific token, returning an error if not found.
    pub(crate) fn expect_token(&mut self, kind: TokenKind) -> Result<(), SyntaxError> {
        if self.consume_token(kind.clone()) {
            Ok(())
        } else {
            let span = self.current_span();
            Err(SyntaxError::unexpected_token(
                &kind.display_name(),
                &self.current_token_name(),
                span,
            ))
        }
    }

    /// Expects an identifier, returning its name.
    pub(crate) fn expect_identifier(&mut self) -> Result<String, SyntaxError> {
        match self.peek_kind() {
            Some(TokenKind::Identifier(name) | TokenKind::QuotedIdentifier(name)) => {
                let name = name.clone();
                self.advance();
                Ok(name)
            }
            _ => {
                let span = self.current_span();
                Err(SyntaxError::unexpected_token(
                    "identifier",
                    &self.current_token_name(),
                    span,
                ))
            }
        }
    }

    /// Expects an integer literal.
    fn expect_integer(&mut self) -> Result<i64, SyntaxError> {
        match self.peek_kind() {
            Some(TokenKind::Integer(n)) => {
                let n = *n;
                self.advance();
                Ok(n)
            }
            _ => {
                let span = self.current_span();
                Err(SyntaxError::unexpected_token(
                    "integer",
                    &self.current_token_name(),
                    span,
                ))
            }
        }
    }

    /// Parses a comma-separated list of identifiers.
    fn parse_identifier_list(&mut self) -> Result<Vec<String>, SyntaxError> {
        let mut list = vec![self.expect_identifier()?];
        while self.consume_token(TokenKind::Comma) {
            list.push(self.expect_identifier()?);
        }
        Ok(list)
    }

    /// Parses a comma-separated list of expressions.
    fn parse_expr_list(&mut self) -> Result<Vec<Expr>, SyntaxError> {
        let mut list = vec![self.parse_expr()?];
        while self.consume_token(TokenKind::Comma) {
            list.push(self.parse_expr()?);
        }
        Ok(list)
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
        assert_eq!(parse("START TRANSACTION").unwrap(), Statement::Begin);
        assert_eq!(parse("COMMIT").unwrap(), Statement::Commit);
        assert_eq!(parse("ROLLBACK").unwrap(), Statement::Rollback);
    }

    #[test]
    fn test_set() {
        let stmt = parse("SET foo = 42").unwrap();
        match stmt {
            Statement::Set(s) => {
                assert_eq!(s.name, "foo");
                assert_eq!(s.value, Expr::Integer(42));
            }
            _ => panic!("expected SET"),
        }
    }

    #[test]
    fn test_create_table_basic() {
        let stmt = parse("CREATE TABLE users (id INTEGER, name TEXT)").unwrap();
        match stmt {
            Statement::CreateTable(ct) => {
                assert_eq!(ct.name, "users");
                assert_eq!(ct.columns.len(), 2);
                assert_eq!(ct.columns[0].name, "id");
                assert_eq!(ct.columns[0].data_type, DataType::Integer);
                assert_eq!(ct.columns[1].name, "name");
                assert_eq!(ct.columns[1].data_type, DataType::Text);
            }
            _ => panic!("expected CREATE TABLE"),
        }
    }

    #[test]
    fn test_create_table_with_constraints() {
        let stmt = parse(
            "CREATE TABLE users (
                id SERIAL PRIMARY KEY,
                email VARCHAR(255) NOT NULL UNIQUE,
                age INTEGER CHECK (age >= 0)
            )",
        )
        .unwrap();

        match stmt {
            Statement::CreateTable(ct) => {
                assert_eq!(ct.columns.len(), 3);
                assert!(ct.columns[0]
                    .constraints
                    .contains(&ColumnConstraint::PrimaryKey));
                assert!(ct.columns[1]
                    .constraints
                    .contains(&ColumnConstraint::NotNull));
                assert!(ct.columns[1]
                    .constraints
                    .contains(&ColumnConstraint::Unique));
            }
            _ => panic!("expected CREATE TABLE"),
        }
    }

    #[test]
    fn test_select_basic() {
        let stmt = parse("SELECT 1").unwrap();
        match stmt {
            Statement::Select(s) => {
                assert_eq!(s.columns.len(), 1);
                assert!(s.from.is_none());
            }
            _ => panic!("expected SELECT"),
        }
    }

    #[test]
    fn test_select_columns() {
        let stmt = parse("SELECT id, name FROM users").unwrap();
        match stmt {
            Statement::Select(s) => {
                assert_eq!(s.columns.len(), 2);
                assert!(s.from.is_some());
            }
            _ => panic!("expected SELECT"),
        }
    }

    #[test]
    fn test_select_wildcard() {
        let stmt = parse("SELECT * FROM users").unwrap();
        match stmt {
            Statement::Select(s) => {
                assert!(matches!(s.columns[0], SelectItem::Wildcard));
            }
            _ => panic!("expected SELECT"),
        }
    }

    #[test]
    fn test_select_qualified_wildcard() {
        let stmt = parse("SELECT u.* FROM users u").unwrap();
        match stmt {
            Statement::Select(s) => {
                assert!(matches!(
                    &s.columns[0],
                    SelectItem::QualifiedWildcard(name) if name == "u"
                ));
            }
            _ => panic!("expected SELECT"),
        }
    }

    #[test]
    fn test_select_with_alias() {
        let stmt = parse("SELECT id AS user_id FROM users").unwrap();
        match stmt {
            Statement::Select(s) => {
                match &s.columns[0] {
                    SelectItem::Expr { alias, .. } => {
                        assert_eq!(alias.as_deref(), Some("user_id"));
                    }
                    _ => panic!("expected Expr"),
                }
            }
            _ => panic!("expected SELECT"),
        }
    }

    #[test]
    fn test_select_where() {
        let stmt = parse("SELECT * FROM users WHERE active = TRUE").unwrap();
        match stmt {
            Statement::Select(s) => {
                assert!(s.where_clause.is_some());
            }
            _ => panic!("expected SELECT"),
        }
    }

    #[test]
    fn test_select_group_by() {
        let stmt = parse("SELECT dept, COUNT(*) FROM emp GROUP BY dept").unwrap();
        match stmt {
            Statement::Select(s) => {
                assert_eq!(s.group_by.len(), 1);
            }
            _ => panic!("expected SELECT"),
        }
    }

    #[test]
    fn test_select_order_by() {
        let stmt = parse("SELECT * FROM users ORDER BY name ASC, id DESC").unwrap();
        match stmt {
            Statement::Select(s) => {
                assert_eq!(s.order_by.len(), 2);
                assert_eq!(s.order_by[0].direction, SortDirection::Asc);
                assert_eq!(s.order_by[1].direction, SortDirection::Desc);
            }
            _ => panic!("expected SELECT"),
        }
    }

    #[test]
    fn test_select_limit_offset() {
        let stmt = parse("SELECT * FROM users LIMIT 10 OFFSET 5").unwrap();
        match stmt {
            Statement::Select(s) => {
                assert!(s.limit.is_some());
                assert!(s.offset.is_some());
            }
            _ => panic!("expected SELECT"),
        }
    }

    #[test]
    fn test_select_join() {
        let stmt =
            parse("SELECT * FROM users u INNER JOIN orders o ON u.id = o.user_id").unwrap();
        match stmt {
            Statement::Select(s) => {
                let from = s.from.unwrap();
                assert!(matches!(from.tables[0], TableRef::Join { .. }));
            }
            _ => panic!("expected SELECT"),
        }
    }

    #[test]
    fn test_insert() {
        let stmt = parse("INSERT INTO users (id, name) VALUES (1, 'Alice')").unwrap();
        match stmt {
            Statement::Insert(i) => {
                assert_eq!(i.table, "users");
                assert_eq!(i.columns, vec!["id", "name"]);
                assert_eq!(i.values.len(), 1);
                assert_eq!(i.values[0].len(), 2);
            }
            _ => panic!("expected INSERT"),
        }
    }

    #[test]
    fn test_insert_multi_row() {
        let stmt = parse("INSERT INTO users VALUES (1, 'Alice'), (2, 'Bob')").unwrap();
        match stmt {
            Statement::Insert(i) => {
                assert_eq!(i.values.len(), 2);
            }
            _ => panic!("expected INSERT"),
        }
    }

    #[test]
    fn test_update() {
        let stmt = parse("UPDATE users SET name = 'Bob' WHERE id = 1").unwrap();
        match stmt {
            Statement::Update(u) => {
                assert_eq!(u.table, "users");
                assert_eq!(u.assignments.len(), 1);
                assert_eq!(u.assignments[0].column, "name");
                assert!(u.where_clause.is_some());
            }
            _ => panic!("expected UPDATE"),
        }
    }

    #[test]
    fn test_delete() {
        let stmt = parse("DELETE FROM users WHERE id = 1").unwrap();
        match stmt {
            Statement::Delete(d) => {
                assert_eq!(d.table, "users");
                assert!(d.where_clause.is_some());
            }
            _ => panic!("expected DELETE"),
        }
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
        let stmt = parse("SELECT * FROM users FOR UPDATE").unwrap();
        match stmt {
            Statement::Select(s) => {
                assert!(matches!(
                    s.locking,
                    Some(LockingClause {
                        mode: LockMode::Update
                    })
                ));
            }
            _ => panic!("expected SELECT"),
        }
    }

    #[test]
    fn test_drop_table() {
        let stmt = parse("DROP TABLE users").unwrap();
        match stmt {
            Statement::DropTable(dt) => {
                assert_eq!(dt.name, "users");
                assert!(!dt.if_exists);
            }
            _ => panic!("expected DROP TABLE"),
        }
    }

    #[test]
    fn test_drop_table_if_exists() {
        let stmt = parse("DROP TABLE IF EXISTS users").unwrap();
        match stmt {
            Statement::DropTable(dt) => {
                assert_eq!(dt.name, "users");
                assert!(dt.if_exists);
            }
            _ => panic!("expected DROP TABLE"),
        }
    }

    #[test]
    fn test_create_index() {
        let stmt = parse("CREATE INDEX idx_name ON users (name)").unwrap();
        match stmt {
            Statement::CreateIndex(ci) => {
                assert_eq!(ci.name, "idx_name");
                assert_eq!(ci.table, "users");
                assert_eq!(ci.columns.len(), 1);
                assert_eq!(ci.columns[0].name, "name");
                assert!(!ci.unique);
                assert!(!ci.if_not_exists);
            }
            _ => panic!("expected CREATE INDEX"),
        }
    }

    #[test]
    fn test_create_unique_index() {
        let stmt = parse("CREATE UNIQUE INDEX IF NOT EXISTS idx_email ON users (email DESC)")
            .unwrap();
        match stmt {
            Statement::CreateIndex(ci) => {
                assert_eq!(ci.name, "idx_email");
                assert_eq!(ci.table, "users");
                assert!(ci.unique);
                assert!(ci.if_not_exists);
                assert_eq!(ci.columns[0].direction, SortDirection::Desc);
            }
            _ => panic!("expected CREATE INDEX"),
        }
    }

    #[test]
    fn test_create_index_multi_column() {
        let stmt = parse("CREATE INDEX idx_multi ON orders (user_id ASC, created_at DESC)")
            .unwrap();
        match stmt {
            Statement::CreateIndex(ci) => {
                assert_eq!(ci.columns.len(), 2);
                assert_eq!(ci.columns[0].name, "user_id");
                assert_eq!(ci.columns[1].name, "created_at");
            }
            _ => panic!("expected CREATE INDEX"),
        }
    }

    #[test]
    fn test_drop_index() {
        let stmt = parse("DROP INDEX idx_name").unwrap();
        match stmt {
            Statement::DropIndex(di) => {
                assert_eq!(di.name, "idx_name");
                assert!(!di.if_exists);
            }
            _ => panic!("expected DROP INDEX"),
        }
    }

    #[test]
    fn test_drop_index_if_exists() {
        let stmt = parse("DROP INDEX IF EXISTS idx_name").unwrap();
        match stmt {
            Statement::DropIndex(di) => {
                assert!(di.if_exists);
            }
            _ => panic!("expected DROP INDEX"),
        }
    }
}
