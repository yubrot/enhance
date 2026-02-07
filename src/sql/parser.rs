//! SQL parser using recursive descent.
//!
//! The [`Parser`] converts a stream of tokens into an Abstract Syntax Tree (AST).
//! It uses recursive descent for most constructs and precedence climbing for
//! expression parsing.

use super::ast::*;
use super::error::{Span, SyntaxError};
use super::lexer::Lexer;
use super::token::TokenKind::*;
use super::token::{Token, TokenKind};

/// Matches token sequences with optional consumption using match patterns.
///
/// Use `[Token1, Token2]!` to match and consume tokens.
/// Use `[Token1, Token2]` to match without consuming tokens.
macro_rules! match_tokens {
    // Entry point: with consumption
    ($self:expr, { [$($pat:pat),+]! => $body:expr $(, $($rest:tt)*)? }) => {
        if let [$(Some($pat)),+] = $self.peek::<{match_tokens!(@count $($pat),+)}>() {
            $self.discard(match_tokens!(@count $($pat),+));
            $body
        } else {
            match_tokens!($self, { $($($rest)*)? })
        }
    };

    // Entry point: without consumption
    ($self:expr, { [$($pat:pat),+] => $body:expr $(, $($rest:tt)*)? }) => {
        if let [$(Some($pat)),+] = $self.peek::<{match_tokens!(@count $($pat),+)}>() {
            $body
        } else {
            match_tokens!($self, { $($($rest)*)? })
        }
    };

    // Default case
    ($self:expr, { _ => $default:expr $(,)? }) => {
        $default
    };

    // Helper: count patterns
    (@count) => { 0 };
    (@count $head:pat $(, $tail:pat)*) => { 1 + match_tokens!(@count $($tail),*) };
}

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
    /// Creates a new parser for the given SQL input.
    pub fn new(input: &'a str) -> Self {
        // NOTE: Lexer errors are returned as Error tokens.
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
        if matches!(self.peek(), [None | Some(Eof)]) {
            return Ok(None);
        }

        let stmt = self.parse_statement()?;

        match_tokens!(self, { [Semicolon]! => {}, _ => {} });

        // Check for unexpected trailing tokens
        if !matches!(self.peek(), [None | Some(Eof)]) {
            return Err(self.unexpected_token_error("end of input"));
        }

        Ok(Some(stmt))
    }

    // ==================== Statement parsing ====================

    /// Parses a single statement.
    fn parse_statement(&mut self) -> Result<Statement, SyntaxError> {
        match_tokens!(self, {
            [Explain]! => Ok(Statement::Explain(Box::new(self.parse_statement()?))),
            [Begin] => self.parse_begin_stmt(),
            [Commit]! => Ok(Statement::Commit),
            [Rollback]! => Ok(Statement::Rollback),
            [Set] => self.parse_set_stmt(),
            [Create] => self.parse_create_stmt(),
            [Drop] => self.parse_drop_stmt(),
            [Select] => Ok(Statement::Select(Box::new(self.parse_select_stmt()?))),
            [Insert] => self.parse_insert_stmt(),
            [Update] => self.parse_update_stmt(),
            [Delete] => self.parse_delete_stmt(),
            _ => Err(self.unexpected_token_error("statement")),
        })
    }

    /// Parses a BEGIN statement.
    fn parse_begin_stmt(&mut self) -> Result<Statement, SyntaxError> {
        self.consume([Begin])?;

        match_tokens!(self, { [Transaction]! => {}, _ => {} });

        Ok(Statement::Begin)
    }

    /// Parses a SET statement.
    fn parse_set_stmt(&mut self) -> Result<Statement, SyntaxError> {
        self.consume([Set])?;
        let name = self.consume_identifier()?;
        self.consume([Eq])?;
        let value = self.parse_expr()?;

        Ok(Statement::Set(SetStmt { name, value }))
    }

    /// Parses a CREATE statement (TABLE or INDEX).
    fn parse_create_stmt(&mut self) -> Result<Statement, SyntaxError> {
        match_tokens!(self, {
            [Create, Table] => self.parse_create_table(),
            [Create, Unique, Index] => self.parse_create_index(),
            [Create, Index] => self.parse_create_index(),
            _ => {
                // Consume CREATE to give a better error message
                self.consume([Create])?;
                Err(self.unexpected_token_error("TABLE or INDEX"))
            }
        })
    }

    /// Parses a CREATE TABLE statement.
    fn parse_create_table(&mut self) -> Result<Statement, SyntaxError> {
        self.consume([Create, Table])?;
        let if_not_exists = match_tokens!(self, { [If, Not, Exists]! => true, _ => false });
        let name = self.consume_identifier()?;

        self.consume([LParen])?;
        let mut columns = Vec::new();
        let mut constraints = Vec::new();

        loop {
            match_tokens!(self, {
                [Primary | Unique | Foreign | Check | Constraint] => constraints.push(self.parse_table_constraint()?),
                _ => columns.push(self.parse_column_def()?),
            });
            match_tokens!(self, {
                [Comma]! => continue,
                [RParen]! => break,
                _ => return Err(self.unexpected_token_error("',' or ')'")),
            });
        }

        Ok(Statement::CreateTable(Box::new(CreateTableStmt {
            name,
            columns,
            constraints,
            if_not_exists,
        })))
    }

    /// Parses a table-level constraint.
    fn parse_table_constraint(&mut self) -> Result<TableConstraint, SyntaxError> {
        let name = match_tokens!(self, {
            [Constraint]! => Some(self.consume_identifier()?),
            _ => None
        });

        let kind = match_tokens!(self, {
            [Primary, Key]! => {
                let columns = self.parse_parenthesized(|p| p.parse_comma_separated(Self::consume_identifier))?;
                TableConstraintKind::PrimaryKey(columns)
            },
            [Unique]! => {
                let columns = self.parse_parenthesized(|p| p.parse_comma_separated(Self::consume_identifier))?;
                TableConstraintKind::Unique(columns)
            },
            [Check]! => TableConstraintKind::Check(self.parse_parenthesized(Self::parse_expr)?),
            [Foreign, Key]! => {
                let columns = self.parse_parenthesized(|p| p.parse_comma_separated(Self::consume_identifier))?;
                self.consume([References])?;
                let ref_table = self.consume_identifier()?;
                let ref_columns = self.parse_parenthesized(|p| p.parse_comma_separated(Self::consume_identifier))?;
                TableConstraintKind::ForeignKey {
                    columns,
                    ref_table,
                    ref_columns,
                }
            },
            _ => return Err(self.unexpected_token_error("constraint type"))
        });

        Ok(TableConstraint { name, kind })
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

    /// Parses column constraints.
    fn parse_column_constraints(&mut self) -> Result<Vec<ColumnConstraint>, SyntaxError> {
        let mut constraints = Vec::new();
        loop {
            let constraint = match_tokens!(self, {
                [Not, Null]! => ColumnConstraint::NotNull,
                [Primary, Key]! => ColumnConstraint::PrimaryKey,
                [Null]! => ColumnConstraint::Null,
                [Unique]! => ColumnConstraint::Unique,
                [Default]! => ColumnConstraint::Default(self.parse_expr()?),
                [Check]! => ColumnConstraint::Check(self.parse_parenthesized(Self::parse_expr)?),
                [References]! => {
                    let table = self.consume_identifier()?;
                    let column = self.parse_if_parenthesized(Self::consume_identifier)?;
                    ColumnConstraint::References { table, column }
                },
                _ => break
            });
            constraints.push(constraint);
        }
        Ok(constraints)
    }

    /// Parses a data type.
    pub(crate) fn parse_data_type(&mut self) -> Result<DataType, SyntaxError> {
        match_tokens!(self, {
            [Boolean]! => Ok(DataType::Boolean),
            [Smallint]! => Ok(DataType::Smallint),
            [Integer]! => Ok(DataType::Integer),
            [Int]! => Ok(DataType::Integer),
            [Bigint]! => Ok(DataType::Bigint),
            [Double, Precision]! => Ok(DataType::DoublePrecision),
            [Real]! => Ok(DataType::Real),
            [Text]! => Ok(DataType::Text),
            [Bytea]! => Ok(DataType::Bytea),
            [Serial]! => Ok(DataType::Serial),
            [Varchar]! => Ok(DataType::Varchar(self.parse_if_parenthesized(Self::consume_integer)?.map(|i| i as u32))),
            _ => Err(self.unexpected_token_error("data type"))
        })
    }

    /// Parses a CREATE INDEX statement.
    fn parse_create_index(&mut self) -> Result<Statement, SyntaxError> {
        // CREATE [UNIQUE] INDEX [IF NOT EXISTS] name ON table (columns)
        self.consume([Create])?;

        let unique = match_tokens!(self, { [Unique]! => true, _ => false });

        self.consume([Index])?;

        let if_not_exists = match_tokens!(self, { [If, Not, Exists]! => true, _ => false });

        let name = self.consume_identifier()?;
        self.consume([On])?;
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
        match_tokens!(self, {
            [Drop, Table] => self.parse_drop_table(),
            [Drop, Index] => self.parse_drop_index(),
            _ => {
                // Consume DROP to give a better error message
                self.consume([Drop])?;
                Err(self.unexpected_token_error("TABLE or INDEX"))
            }
        })
    }

    /// Parses a DROP TABLE statement.
    fn parse_drop_table(&mut self) -> Result<Statement, SyntaxError> {
        // DROP TABLE [IF EXISTS] name
        self.consume([Drop, Table])?;

        let if_exists = match_tokens!(self, { [If, Exists]! => true, _ => false });
        let name = self.consume_identifier()?;

        Ok(Statement::DropTable(DropTableStmt { name, if_exists }))
    }

    /// Parses a DROP INDEX statement.
    fn parse_drop_index(&mut self) -> Result<Statement, SyntaxError> {
        // DROP INDEX [IF EXISTS] name
        self.consume([Drop, Index])?;

        let if_exists = match_tokens!(self, { [If, Exists]! => true, _ => false });
        let name = self.consume_identifier()?;

        Ok(Statement::DropIndex(DropIndexStmt { name, if_exists }))
    }

    /// Parses a SELECT statement.
    pub(crate) fn parse_select_stmt(&mut self) -> Result<SelectStmt, SyntaxError> {
        self.consume([Select])?;

        // DISTINCT / ALL
        let distinct = match_tokens!(self, { [Distinct]! => true, [All]! => false, _ => false });

        // Select list
        let columns = self.parse_comma_separated(Self::parse_select_item)?;

        // FROM clause
        let from = match_tokens!(self, { [From]! => Some(self.parse_from_clause()?), _ => None });

        // WHERE clause
        let where_clause = match_tokens!(self, { [Where]! => Some(self.parse_expr()?), _ => None });

        // GROUP BY clause
        let group_by = match_tokens!(self, { [Group, By]! => self.parse_comma_separated(Self::parse_expr)?, _ => Vec::new() });

        // HAVING clause
        let having = match_tokens!(self, { [Having]! => Some(self.parse_expr()?), _ => None });

        // ORDER BY clause
        let order_by =
            match_tokens!(self, { [Order, By]! => self.parse_order_by_list()?, _ => vec![] });

        // LIMIT clause
        let limit = match_tokens!(self, { [Limit]! => Some(self.parse_expr()?), _ => None });

        // OFFSET clause
        let offset = match_tokens!(self, { [Offset]! => Some(self.parse_expr()?), _ => None });

        // FOR UPDATE/SHARE
        let locking =
            match_tokens!(self, { [For]! => Some(self.parse_locking_clause()?), _ => None });

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

    /// Parses a single select item.
    fn parse_select_item(&mut self) -> Result<SelectItem, SyntaxError> {
        // Check for *
        match_tokens!(self, {
            [Asterisk]! => return Ok(SelectItem::Wildcard),
            _ => {},
        });

        // Check for table.* (qualified wildcard)
        if let [Some(Identifier(name)), Some(Dot), Some(Asterisk)] = self.peek() {
            let name = std::mem::take(name);
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
            let join_type = match_tokens!(self, {
                [Cross, Join]! => JoinType::Cross,
                [Inner, Join]! => JoinType::Inner,
                [Left, Outer, Join]! => JoinType::Left,
                [Left, Join]! => JoinType::Left,
                [Right, Outer, Join]! => JoinType::Right,
                [Right, Join]! => JoinType::Right,
                [Full, Outer, Join]! => JoinType::Full,
                [Full, Join]! => JoinType::Full,
                [Join]! => JoinType::Inner,
                _ => break,
            });

            let right = self.parse_primary_table_ref()?;

            let condition = match join_type {
                JoinType::Cross => None,
                _ => match_tokens!(self, {
                    [On]! => Some(JoinCondition::On(self.parse_expr()?)),
                    [Using]! => {
                        let columns = self.parse_parenthesized(|p| p.parse_comma_separated(Self::consume_identifier))?;
                        Some(JoinCondition::Using(columns))
                    },
                    _ => None,
                }),
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
        match_tokens!(self, {
            [LParen]! => {
                let query = self.parse_select_stmt()?;
                self.consume([RParen])?;

                // Subquery alias is required
                match_tokens!(self, { [As]! => {}, _ => {} });
                let alias = self.consume_identifier()?;

                Ok(TableRef::Subquery {
                    query: Box::new(query),
                    alias,
                })
            },
            _ => {
                // Table name
                let name = self.consume_identifier()?;
                let alias = self.parse_as()?;

                Ok(TableRef::Table { name, alias })
            }
        })
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
        let mode = match_tokens!(self, {
            [Update]! => LockMode::Update,
            [Share]! => LockMode::Share,
            _ => return Err(self.unexpected_token_error("UPDATE or SHARE"))
        });

        Ok(LockingClause { mode })
    }

    /// Parses an INSERT statement.
    fn parse_insert_stmt(&mut self) -> Result<Statement, SyntaxError> {
        self.consume([Insert, Into])?;
        let table = self.consume_identifier()?;

        // Optional column list
        let columns = self
            .parse_if_parenthesized(|p| p.parse_comma_separated(Self::consume_identifier))?
            .unwrap_or(Vec::new());

        // VALUES clause
        self.consume([Values])?;

        let values = self.parse_comma_separated(|p| {
            p.parse_parenthesized(|p| p.parse_comma_separated(Self::parse_expr))
        })?;

        Ok(Statement::Insert(Box::new(InsertStmt {
            table,
            columns,
            values,
        })))
    }

    /// Parses an UPDATE statement.
    fn parse_update_stmt(&mut self) -> Result<Statement, SyntaxError> {
        self.consume([Update])?;
        let table = self.consume_identifier()?;
        self.consume([Set])?;

        let assignments = self.parse_comma_separated(|p| {
            let column = p.consume_identifier()?;
            p.consume([Eq])?;
            let value = p.parse_expr()?;
            Ok(Assignment { column, value })
        })?;

        let where_clause = match_tokens!(self, { [Where]! => Some(self.parse_expr()?), _ => None });

        Ok(Statement::Update(Box::new(UpdateStmt {
            table,
            assignments,
            where_clause,
        })))
    }

    /// Parses a DELETE statement.
    fn parse_delete_stmt(&mut self) -> Result<Statement, SyntaxError> {
        self.consume([Delete, From])?;
        let table = self.consume_identifier()?;

        let where_clause = match_tokens!(self, { [Where]! => Some(self.parse_expr()?), _ => None });

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
        if let Some((op, precedence)) = match_tokens!(self, {
            [Not]! => Some((UnaryOperator::Not, Precedence::Not)),
            [Minus]! => Some((UnaryOperator::Minus, Precedence::UnaryPlusMinus)),
            [Plus]! => Some((UnaryOperator::Plus, Precedence::UnaryPlusMinus)),
            _ => None
        }) {
            let operand = self.parse_expr_with_precedence(precedence)?;
            Ok(Expr::UnaryOp {
                op,
                operand: Box::new(operand),
            })
        } else {
            self.parse_postfix_expr()
        }
    }

    /// Parses postfix expressions (IS NULL, IN, BETWEEN, LIKE, ::, etc.).
    fn parse_postfix_expr(&mut self) -> Result<Expr, SyntaxError> {
        let mut expr = self.parse_primary_expr()?;

        loop {
            expr = match_tokens!(self, {
                [Is, Not, Null]! => Expr::IsNull {
                    expr: Box::new(expr),
                    negated: true,
                },
                [Is, Null]! => Expr::IsNull {
                    expr: Box::new(expr),
                    negated: false,
                },
                [In]! => self.parse_in_expr(expr, false)?,
                [Between]! => self.parse_between_expr(expr, false)?,
                [Like]! => self.parse_like_expr(expr, false, false)?,
                [Ilike]! => self.parse_like_expr(expr, true, false)?,
                [Not, In]! => self.parse_in_expr(expr, true)?,
                [Not, Between]! => self.parse_between_expr(expr, true)?,
                [Not, Like]! => self.parse_like_expr(expr, false, true)?,
                [Not, Ilike]! => self.parse_like_expr(expr, true, true)?,
                [DoubleColon]! => {
                    let data_type = self.parse_data_type()?;
                    Expr::Cast {
                        expr: Box::new(expr),
                        data_type,
                    }
                },
                _ => break,
            });
        }

        Ok(expr)
    }

    /// Parses IN expression (after IN keyword consumed).
    fn parse_in_expr(&mut self, expr: Expr, negated: bool) -> Result<Expr, SyntaxError> {
        self.consume([LParen])?;
        match_tokens!(self, {
            [Select] => {
                let subquery = self.parse_select_stmt()?;
                self.consume([RParen])?;
                Ok(Expr::InSubquery {
                    expr: Box::new(expr),
                    subquery: Box::new(subquery),
                    negated,
                })
            },
            _ => {
                let list = self.parse_comma_separated(Self::parse_expr)?;
                self.consume([RParen])?;
                Ok(Expr::InList {
                    expr: Box::new(expr),
                    list,
                    negated,
                })
            }
        })
    }

    /// Parses BETWEEN expression (after BETWEEN keyword consumed).
    fn parse_between_expr(&mut self, expr: Expr, negated: bool) -> Result<Expr, SyntaxError> {
        let low = self.parse_expr_with_precedence(Precedence::Comparison)?;
        self.consume([And])?;
        let high = self.parse_expr_with_precedence(Precedence::Comparison)?;
        Ok(Expr::Between {
            expr: Box::new(expr),
            low: Box::new(low),
            high: Box::new(high),
            negated,
        })
    }

    /// Parses LIKE/ILIKE expression (after LIKE/ILIKE keyword consumed).
    fn parse_like_expr(
        &mut self,
        expr: Expr,
        case_insensitive: bool,
        negated: bool,
    ) -> Result<Expr, SyntaxError> {
        let pattern = self.parse_expr_with_precedence(Precedence::Comparison)?;
        let escape = match_tokens!(self, {
            [Escape]! => Some(Box::new(self.parse_expr_with_precedence(Precedence::Comparison)?)),
            _ => None
        });
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
        match_tokens!(self, {
            [Null]! => Ok(Expr::Null),
            [True]! => Ok(Expr::Boolean(true)),
            [False]! => Ok(Expr::Boolean(false)),
            [Exists]! => {
                let subquery = self.parse_parenthesized(Self::parse_select_stmt)?;
                Ok(Expr::Exists {
                    subquery: Box::new(subquery),
                    negated: false,
                })
            },
            [Case]! => self.parse_case_expr(),
            [Cast]! => {
                let (expr, data_type) = self.parse_parenthesized(|p| {
                    let expr = p.parse_expr()?;
                    p.consume([As])?;
                    let data_type = p.parse_data_type()?;
                    Ok((expr, data_type))
                })?;
                Ok(Expr::Cast {
                    expr: Box::new(expr),
                    data_type,
                })
            },
            [LParen]! => {
                Ok(match_tokens!(self, {
                    [Select] => {
                        let query = self.parse_select_stmt()?;
                        self.consume([RParen])?;
                        Expr::Subquery(Box::new(query))
                    },
                    _ => {
                        let expr = self.parse_expr()?;
                        self.consume([RParen])?;
                        expr
                    }
                }))
            },
            [Asterisk]! => {
                Ok(Expr::ColumnRef {
                    table: None,
                    column: "*".to_string(),
                })
            },
            [IntegerLit(n)] => {
                let n = std::mem::take(n);
                self.discard(1);
                Ok(Expr::Integer(n))
            },
            [FloatLit(n)] => {
                let n = std::mem::take(n);
                self.discard(1);
                Ok(Expr::Float(n))
            },
            [StringLit(s)] => {
                let s = std::mem::take(s);
                self.discard(1);
                Ok(Expr::String(s))
            },
            [Parameter(n)] => {
                let n = std::mem::take(n);
                self.discard(1);
                Ok(Expr::Parameter(n))
            },
            [Identifier(name)] => {
                let name = std::mem::take(name);
                self.discard(1);

                match_tokens!(self, {
                    // Function call
                    [LParen] => self.parse_function_call(name),
                    // Qualified column reference (table.column)
                    [Dot]! => {
                        let column = self.consume_identifier()?;
                        Ok(Expr::ColumnRef {
                            table: Some(name),
                            column,
                        })
                    },
                    _ => Ok(Expr::ColumnRef {
                        table: None,
                        column: name,
                    }),
                })
            },
            _ => Err(self.unexpected_token_error("expression")),
        })
    }

    /// Parses a function call with arguments.
    fn parse_function_call(&mut self, name: String) -> Result<Expr, SyntaxError> {
        self.consume([LParen])?;

        // Check for DISTINCT
        let distinct = match_tokens!(self, { [Distinct]! => true, _ => false });

        let args = match_tokens!(self, {
            // Check for empty argument list first
            [RParen] => Vec::new(),
            // Check for COUNT(*)
            [Asterisk]! => vec![Expr::ColumnRef { table: None, column: "*".to_string() }],
            _ => self.parse_comma_separated(Self::parse_expr)?,
        });

        self.consume([RParen])?;

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
        let operand = match_tokens!(self, {
            [When] => None,
            _ => Some(Box::new(self.parse_expr()?)),
        });

        // Parse WHEN clauses
        let mut when_clauses = Vec::new();
        while match_tokens!(self, { [When]! => true, _ => false }) {
            let condition = self.parse_expr()?;
            self.consume([Then])?;
            let result = self.parse_expr()?;
            when_clauses.push(WhenClause { condition, result });
        }

        if when_clauses.is_empty() {
            return Err(self.unexpected_token_error("WHEN in CASE expression"));
        }

        // Parse optional ELSE
        let else_result = match_tokens!(self, {
            [Else]! => Some(Box::new(self.parse_expr()?)),
            _ => None
        });

        self.consume([End])?;

        Ok(Expr::Case {
            operand,
            when_clauses,
            else_result,
        })
    }

    /// Peeks at the next token and returns the binary operator and its precedence.
    fn peek_binary_op(&mut self) -> Option<(BinaryOperator, Precedence)> {
        Some(match_tokens!(self, {
            [Or] => (BinaryOperator::Or, Precedence::Or),
            [And] => (BinaryOperator::And, Precedence::And),
            [Eq] => (BinaryOperator::Eq, Precedence::Comparison),
            [Neq] => (BinaryOperator::Neq, Precedence::Comparison),
            [Lt] => (BinaryOperator::Lt, Precedence::Comparison),
            [LtEq] => (BinaryOperator::LtEq, Precedence::Comparison),
            [Gt] => (BinaryOperator::Gt, Precedence::Comparison),
            [GtEq] => (BinaryOperator::GtEq, Precedence::Comparison),
            [Concat] => (BinaryOperator::Concat, Precedence::Concat),
            [Plus] => (BinaryOperator::Add, Precedence::AddSub),
            [Minus] => (BinaryOperator::Sub, Precedence::AddSub),
            [Asterisk] => (BinaryOperator::Mul, Precedence::MulDiv),
            [Slash] => (BinaryOperator::Div, Precedence::MulDiv),
            [Percent] => (BinaryOperator::Mod, Precedence::MulDiv),
            _ => return None
        }))
    }

    // ==================== Parsing utilities ====================

    /// Parses content within parentheses.
    fn parse_parenthesized<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<T, SyntaxError>,
    ) -> Result<T, SyntaxError> {
        self.consume([LParen])?;
        let result = f(self)?;
        self.consume([RParen])?;
        Ok(result)
    }

    fn parse_if_parenthesized<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<T, SyntaxError>,
    ) -> Result<Option<T>, SyntaxError> {
        match_tokens!(self, {
            [LParen]! => {
                let result = f(self)?;
                self.consume([RParen])?;
                Ok(Some(result))
            },
            _ => Ok(None),
        })
    }

    /// Parses a comma-separated list of items.
    fn parse_comma_separated<T>(
        &mut self,
        mut f: impl FnMut(&mut Self) -> Result<T, SyntaxError>,
    ) -> Result<Vec<T>, SyntaxError> {
        let mut items = vec![f(self)?];
        while match_tokens!(self, { [Comma]! => true, _ => false }) {
            items.push(f(self)?);
        }
        Ok(items)
    }

    /// Parses an optional alias (with or without AS keyword).
    fn parse_as(&mut self) -> Result<Option<String>, SyntaxError> {
        match_tokens!(self, {
            [As]! => Ok(Some(self.consume_identifier()?)),
            // Alias without AS: identifier that's not a reserved keyword
            [Identifier(_)] => Ok(Some(self.consume_identifier()?)),
            _ => Ok(None),
        })
    }

    /// Parses sort direction (ASC/DESC).
    fn parse_sort_direction(&mut self) -> SortDirection {
        match_tokens!(self, {
            [Asc]! => SortDirection::Asc,
            [Desc]! => SortDirection::Desc,
            _ => SortDirection::default()
        })
    }

    /// Parses NULL ordering (NULLS FIRST/LAST).
    fn parse_null_ordering(&mut self) -> Result<NullOrdering, SyntaxError> {
        match_tokens!(self, {
            [Nulls, First]! => Ok(NullOrdering::First),
            [Nulls, Last]! => Ok(NullOrdering::Last),
            [Nulls]! => Err(self.unexpected_token_error("FIRST or LAST")),
            _ => Ok(NullOrdering::default())
        })
    }

    // ==================== Token utilities ====================

    /// Returns a fixed-size array of mutable references to upcoming tokens.
    fn peek<const N: usize>(&mut self) -> [Option<&mut TokenKind>; N] {
        let mut result = [const { None }; N];
        for (i, t) in self.tokens.iter_mut().skip(self.pos).take(N).enumerate() {
            result[i] = Some(&mut t.kind);
        }
        result
    }

    /// Expects a specific token, returning an error if not found.
    fn consume<const N: usize>(&mut self, tokens: [TokenKind; N]) -> Result<(), SyntaxError> {
        for token in tokens {
            if matches!(self.peek(), [Some(t)] if t == &token) {
                self.discard(1);
            } else {
                return Err(self.unexpected_token_error(&token.display_name()));
            }
        }
        Ok(())
    }

    /// Advances by the given number of tokens.
    fn discard(&mut self, count: usize) {
        self.pos = (self.pos + count).min(self.tokens.len());
    }

    /// Expects an identifier, returning its name.
    fn consume_identifier(&mut self) -> Result<String, SyntaxError> {
        match_tokens!(self, {
            [Identifier(name)] => {
                let name = std::mem::take(name);
                self.discard(1);
                Ok(name)
            },
            _ => Err(self.unexpected_token_error("identifier")),
        })
    }

    /// Expects an integer literal.
    fn consume_integer(&mut self) -> Result<i64, SyntaxError> {
        match_tokens!(self, {
            [IntegerLit(n)] => {
                let n = std::mem::take(n);
                self.discard(1);
                Ok(n)
            },
            _ => Err(self.unexpected_token_error("integer")),
        })
    }

    /// Creates an unexpected token error with the current position.
    fn unexpected_token_error(&self, expected: &str) -> SyntaxError {
        let current_span = self
            .tokens
            .get(self.pos)
            .map_or(Span::at(self.input.len()), |t| t.span);
        let current_token_name = self
            .tokens
            .get(self.pos)
            .map(|t| &t.kind)
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
        assert_eq!(parse_expr("3.5").unwrap(), Expr::Float(3.5));
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
