//! Expression parsing with precedence climbing.
//!
//! This module implements expression parsing using the precedence climbing algorithm,
//! which handles operator precedence and associativity correctly.

use super::ast::{BinaryOperator, Expr, UnaryOperator, WhenClause};
use super::error::ParseError;
use super::parser::Parser;
use super::token::{Keyword, TokenKind};

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
pub enum Precedence {
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
    pub fn next(self) -> Self {
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

impl<'a> Parser<'a> {
    /// Parses an expression.
    pub fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        self.parse_expr_with_precedence(Precedence::Lowest)
    }

    /// Parses an expression with minimum precedence.
    pub fn parse_expr_with_precedence(&mut self, min_prec: Precedence) -> Result<Expr, ParseError> {
        let mut left = self.parse_unary_expr()?;

        loop {
            let Some((op, prec)) = self.peek_binary_op() else {
                break;
            };

            if prec < min_prec {
                break;
            }

            self.advance(); // consume operator

            // Handle IS NULL / IS NOT NULL specially
            if matches!(op, BinaryOperator::Eq) && self.check_keyword(Keyword::Null) {
                // This was actually IS NULL
                self.advance();
                left = Expr::IsNull {
                    expr: Box::new(left),
                    negated: false,
                };
                continue;
            }

            // Right-associative for comparison operators
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
    fn parse_unary_expr(&mut self) -> Result<Expr, ParseError> {
        // NOT
        if self.consume_keyword(Keyword::Not) {
            let operand = self.parse_expr_with_precedence(Precedence::Not)?;
            return Ok(Expr::UnaryOp {
                op: UnaryOperator::Not,
                operand: Box::new(operand),
            });
        }

        // Unary minus
        if self.consume_token(TokenKind::Minus) {
            let operand = self.parse_expr_with_precedence(Precedence::UnaryPlusMinus)?;
            return Ok(Expr::UnaryOp {
                op: UnaryOperator::Minus,
                operand: Box::new(operand),
            });
        }

        // Unary plus
        if self.consume_token(TokenKind::Plus) {
            let operand = self.parse_expr_with_precedence(Precedence::UnaryPlusMinus)?;
            return Ok(Expr::UnaryOp {
                op: UnaryOperator::Plus,
                operand: Box::new(operand),
            });
        }

        self.parse_postfix_expr()
    }

    /// Parses postfix expressions (IS NULL, IN, BETWEEN, LIKE, ::, etc.).
    fn parse_postfix_expr(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary_expr()?;

        loop {
            // IS [NOT] NULL
            if self.consume_keyword(Keyword::Is) {
                let negated = self.consume_keyword(Keyword::Not);
                self.expect_keyword(Keyword::Null)?;
                expr = Expr::IsNull {
                    expr: Box::new(expr),
                    negated,
                };
                continue;
            }

            // [NOT] IN (...)
            let not_before_in = self.consume_keyword(Keyword::Not);
            if self.consume_keyword(Keyword::In) {
                self.expect_token(TokenKind::LParen)?;

                // Check for subquery
                if self.check_keyword(Keyword::Select) {
                    let subquery = self.parse_select_stmt()?;
                    self.expect_token(TokenKind::RParen)?;
                    expr = Expr::InSubquery {
                        expr: Box::new(expr),
                        subquery: Box::new(subquery),
                        negated: not_before_in,
                    };
                } else {
                    // Value list
                    let list = self.parse_expr_list_inner()?;
                    self.expect_token(TokenKind::RParen)?;
                    expr = Expr::InList {
                        expr: Box::new(expr),
                        list,
                        negated: not_before_in,
                    };
                }
                continue;
            }

            // [NOT] BETWEEN low AND high
            if not_before_in && self.consume_keyword(Keyword::Between) {
                let low = self.parse_expr_with_precedence(Precedence::Comparison)?;
                self.expect_keyword(Keyword::And)?;
                let high = self.parse_expr_with_precedence(Precedence::Comparison)?;
                expr = Expr::Between {
                    expr: Box::new(expr),
                    low: Box::new(low),
                    high: Box::new(high),
                    negated: true,
                };
                continue;
            }
            if self.consume_keyword(Keyword::Between) {
                let low = self.parse_expr_with_precedence(Precedence::Comparison)?;
                self.expect_keyword(Keyword::And)?;
                let high = self.parse_expr_with_precedence(Precedence::Comparison)?;
                expr = Expr::Between {
                    expr: Box::new(expr),
                    low: Box::new(low),
                    high: Box::new(high),
                    negated: false,
                };
                continue;
            }

            // [NOT] LIKE / ILIKE pattern [ESCAPE escape]
            if not_before_in && (self.consume_keyword(Keyword::Like) || self.consume_keyword(Keyword::Ilike)) {
                let case_insensitive = self.check_keyword(Keyword::Ilike);
                let pattern = self.parse_expr_with_precedence(Precedence::Comparison)?;
                let escape = if self.consume_keyword(Keyword::Escape) {
                    Some(Box::new(self.parse_expr_with_precedence(Precedence::Comparison)?))
                } else {
                    None
                };
                expr = Expr::Like {
                    expr: Box::new(expr),
                    pattern: Box::new(pattern),
                    escape,
                    negated: true,
                    case_insensitive,
                };
                continue;
            }
            let case_insensitive = self.consume_keyword(Keyword::Ilike);
            if case_insensitive || self.consume_keyword(Keyword::Like) {
                let pattern = self.parse_expr_with_precedence(Precedence::Comparison)?;
                let escape = if self.consume_keyword(Keyword::Escape) {
                    Some(Box::new(self.parse_expr_with_precedence(Precedence::Comparison)?))
                } else {
                    None
                };
                expr = Expr::Like {
                    expr: Box::new(expr),
                    pattern: Box::new(pattern),
                    escape,
                    negated: false,
                    case_insensitive,
                };
                continue;
            }

            // Restore NOT if it wasn't used
            if not_before_in {
                // NOT was consumed but not used - this is actually a unary NOT for next expr
                // We need to push it back, but since we can't, treat this as end of postfix
                // and let caller handle it. Actually, this is a parse error in most cases.
                let span = self.current_span();
                return Err(ParseError::unexpected_token(
                    "IN, BETWEEN, or LIKE after NOT",
                    &self.current_token_name(),
                    span,
                ));
            }

            // :: type cast (PostgreSQL style)
            if self.consume_token(TokenKind::DoubleColon) {
                let data_type = self.parse_data_type()?;
                expr = Expr::Cast {
                    expr: Box::new(expr),
                    data_type,
                };
                continue;
            }

            break;
        }

        Ok(expr)
    }

    /// Parses a comma-separated list of expressions (internal, for IN list).
    fn parse_expr_list_inner(&mut self) -> Result<Vec<Expr>, ParseError> {
        let mut list = vec![self.parse_expr()?];
        while self.consume_token(TokenKind::Comma) {
            list.push(self.parse_expr()?);
        }
        Ok(list)
    }

    /// Parses a primary expression (literals, identifiers, function calls, etc.).
    fn parse_primary_expr(&mut self) -> Result<Expr, ParseError> {
        // NULL
        if self.consume_keyword(Keyword::Null) {
            return Ok(Expr::Null);
        }

        // TRUE
        if self.consume_keyword(Keyword::True) {
            return Ok(Expr::Boolean(true));
        }

        // FALSE
        if self.consume_keyword(Keyword::False) {
            return Ok(Expr::Boolean(false));
        }

        // EXISTS (subquery)
        if self.consume_keyword(Keyword::Exists) {
            self.expect_token(TokenKind::LParen)?;
            let subquery = self.parse_select_stmt()?;
            self.expect_token(TokenKind::RParen)?;
            return Ok(Expr::Exists {
                subquery: Box::new(subquery),
                negated: false,
            });
        }

        // NOT EXISTS (subquery) - handled specially
        // Note: This is also handled in parse_unary_expr, but NOT EXISTS can appear in primary context

        // CASE expression
        if self.consume_keyword(Keyword::Case) {
            return self.parse_case_expr();
        }

        // CAST(expr AS type)
        if self.consume_keyword(Keyword::Cast) {
            self.expect_token(TokenKind::LParen)?;
            let expr = self.parse_expr()?;
            self.expect_keyword(Keyword::As)?;
            let data_type = self.parse_data_type()?;
            self.expect_token(TokenKind::RParen)?;
            return Ok(Expr::Cast {
                expr: Box::new(expr),
                data_type,
            });
        }

        // Integer literal
        if let Some(TokenKind::Integer(n)) = self.peek_kind() {
            let n = *n;
            self.advance();
            return Ok(Expr::Integer(n));
        }

        // Float literal
        if let Some(TokenKind::Float(n)) = self.peek_kind() {
            let n = *n;
            self.advance();
            return Ok(Expr::Float(n));
        }

        // String literal
        if let Some(TokenKind::String(s)) = self.peek_kind() {
            let s = s.clone();
            self.advance();
            return Ok(Expr::String(s));
        }

        // Parameter ($1, $2, etc.)
        if let Some(TokenKind::Parameter(n)) = self.peek_kind() {
            let n = *n;
            self.advance();
            return Ok(Expr::Parameter(n));
        }

        // Parenthesized expression or subquery
        if self.consume_token(TokenKind::LParen) {
            // Check for subquery
            if self.check_keyword(Keyword::Select) {
                let query = self.parse_select_stmt()?;
                self.expect_token(TokenKind::RParen)?;
                return Ok(Expr::Subquery(Box::new(query)));
            }

            let expr = self.parse_expr()?;
            self.expect_token(TokenKind::RParen)?;
            return Ok(Expr::Nested(Box::new(expr)));
        }

        // Identifier (column reference or function call)
        if let Some(TokenKind::Identifier(name) | TokenKind::QuotedIdentifier(name)) =
            self.peek_kind()
        {
            let name = name.clone();
            self.advance();

            // Check for function call
            if self.check_token(TokenKind::LParen) {
                return self.parse_function_call(name);
            }

            // Check for qualified column reference (table.column)
            if self.consume_token(TokenKind::Dot) {
                let column = self.expect_identifier()?;
                return Ok(Expr::ColumnRef {
                    table: Some(name),
                    column,
                });
            }

            return Ok(Expr::ColumnRef {
                table: None,
                column: name,
            });
        }

        // Asterisk (for COUNT(*))
        if self.consume_token(TokenKind::Asterisk) {
            return Ok(Expr::ColumnRef {
                table: None,
                column: "*".to_string(),
            });
        }

        let span = self.current_span();
        Err(ParseError::unexpected_token(
            "expression",
            &self.current_token_name(),
            span,
        ))
    }

    /// Parses a function call with arguments.
    fn parse_function_call(&mut self, name: String) -> Result<Expr, ParseError> {
        self.expect_token(TokenKind::LParen)?;

        // Check for DISTINCT
        let distinct = self.consume_keyword(Keyword::Distinct);

        // Check for empty argument list or wildcard
        if self.consume_token(TokenKind::RParen) {
            return Ok(Expr::Function {
                name,
                args: vec![],
                distinct,
            });
        }

        // Check for COUNT(*)
        if self.consume_token(TokenKind::Asterisk) {
            self.expect_token(TokenKind::RParen)?;
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
        let mut args = vec![self.parse_expr()?];
        while self.consume_token(TokenKind::Comma) {
            args.push(self.parse_expr()?);
        }

        self.expect_token(TokenKind::RParen)?;

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
    fn parse_case_expr(&mut self) -> Result<Expr, ParseError> {
        // Check for simple CASE (has operand)
        let operand = if !self.check_keyword(Keyword::When) {
            Some(Box::new(self.parse_expr()?))
        } else {
            None
        };

        // Parse WHEN clauses
        let mut when_clauses = Vec::new();
        while self.consume_keyword(Keyword::When) {
            let condition = self.parse_expr()?;
            self.expect_keyword(Keyword::Then)?;
            let result = self.parse_expr()?;
            when_clauses.push(WhenClause { condition, result });
        }

        if when_clauses.is_empty() {
            let span = self.current_span();
            return Err(ParseError::unexpected_token(
                "WHEN in CASE expression",
                &self.current_token_name(),
                span,
            ));
        }

        // Parse optional ELSE
        let else_result = if self.consume_keyword(Keyword::Else) {
            Some(Box::new(self.parse_expr()?))
        } else {
            None
        };

        self.expect_keyword(Keyword::End)?;

        Ok(Expr::Case {
            operand,
            when_clauses,
            else_result,
        })
    }

    /// Peeks at the next token and returns the binary operator and its precedence.
    fn peek_binary_op(&self) -> Option<(BinaryOperator, Precedence)> {
        match self.peek_kind()? {
            TokenKind::Keyword(Keyword::Or) => Some((BinaryOperator::Or, Precedence::Or)),
            TokenKind::Keyword(Keyword::And) => Some((BinaryOperator::And, Precedence::And)),
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
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_expr(input: &str) -> Result<Expr, ParseError> {
        let mut parser = Parser::new(input);
        parser.parse_expr()
    }

    #[test]
    fn test_literals() {
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
    fn test_column_ref() {
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
    fn test_parameter() {
        assert_eq!(parse_expr("$1").unwrap(), Expr::Parameter(1));
        assert_eq!(parse_expr("$42").unwrap(), Expr::Parameter(42));
    }

    #[test]
    fn test_binary_ops() {
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
    fn test_precedence() {
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
    fn test_unary_ops() {
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
    fn test_is_null() {
        let expr = parse_expr("x IS NULL").unwrap();
        assert!(matches!(
            expr,
            Expr::IsNull {
                negated: false,
                ..
            }
        ));

        let expr = parse_expr("x IS NOT NULL").unwrap();
        assert!(matches!(
            expr,
            Expr::IsNull { negated: true, .. }
        ));
    }

    #[test]
    fn test_function_call() {
        let expr = parse_expr("COUNT(*)").unwrap();
        match expr {
            Expr::Function { name, args, distinct } => {
                assert_eq!(name, "COUNT");
                assert_eq!(args.len(), 1);
                assert!(!distinct);
            }
            _ => panic!("expected Function"),
        }

        let expr = parse_expr("SUM(DISTINCT x)").unwrap();
        match expr {
            Expr::Function { name, distinct, .. } => {
                assert_eq!(name, "SUM");
                assert!(distinct);
            }
            _ => panic!("expected Function"),
        }
    }

    #[test]
    fn test_nested_expr() {
        let expr = parse_expr("(1 + 2) * 3").unwrap();
        match expr {
            Expr::BinaryOp { op, left, .. } => {
                assert_eq!(op, BinaryOperator::Mul);
                assert!(matches!(*left, Expr::Nested(_)));
            }
            _ => panic!("expected BinaryOp"),
        }
    }

    #[test]
    fn test_complex_expr() {
        let expr = parse_expr("a + b * c - d / e").unwrap();
        assert!(expr != Expr::Null); // Just check it parses

        let expr = parse_expr("a > 0 AND b < 10 OR c = 5").unwrap();
        assert!(expr != Expr::Null);

        let expr = parse_expr("NOT (a = 1 OR b = 2)").unwrap();
        assert!(expr != Expr::Null);
    }

    #[test]
    fn test_in_list() {
        let expr = parse_expr("x IN (1, 2, 3)").unwrap();
        assert!(matches!(
            expr,
            Expr::InList {
                negated: false,
                ..
            }
        ));

        let expr = parse_expr("x NOT IN (1, 2, 3)").unwrap();
        assert!(matches!(
            expr,
            Expr::InList {
                negated: true,
                ..
            }
        ));
    }

    #[test]
    fn test_between() {
        let expr = parse_expr("x BETWEEN 1 AND 10").unwrap();
        assert!(matches!(
            expr,
            Expr::Between {
                negated: false,
                ..
            }
        ));

        let expr = parse_expr("x NOT BETWEEN 1 AND 10").unwrap();
        assert!(matches!(
            expr,
            Expr::Between {
                negated: true,
                ..
            }
        ));
    }

    #[test]
    fn test_like() {
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
        assert!(matches!(
            expr,
            Expr::Like {
                negated: true,
                ..
            }
        ));

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
    fn test_like_escape() {
        let expr = parse_expr("name LIKE '%\\%%' ESCAPE '\\'").unwrap();
        match expr {
            Expr::Like { escape, .. } => {
                assert!(escape.is_some());
            }
            _ => panic!("expected Like"),
        }
    }

    #[test]
    fn test_exists() {
        let expr = parse_expr("EXISTS (SELECT 1)").unwrap();
        assert!(matches!(
            expr,
            Expr::Exists {
                negated: false,
                ..
            }
        ));
    }

    #[test]
    fn test_case_searched() {
        let expr = parse_expr("CASE WHEN x > 0 THEN 'positive' ELSE 'non-positive' END").unwrap();
        match expr {
            Expr::Case {
                operand,
                when_clauses,
                else_result,
            } => {
                assert!(operand.is_none());
                assert_eq!(when_clauses.len(), 1);
                assert!(else_result.is_some());
            }
            _ => panic!("expected Case"),
        }
    }

    #[test]
    fn test_case_simple() {
        let expr = parse_expr("CASE status WHEN 1 THEN 'active' WHEN 2 THEN 'inactive' END").unwrap();
        match expr {
            Expr::Case {
                operand,
                when_clauses,
                else_result,
            } => {
                assert!(operand.is_some());
                assert_eq!(when_clauses.len(), 2);
                assert!(else_result.is_none());
            }
            _ => panic!("expected Case"),
        }
    }

    #[test]
    fn test_cast_function() {
        let expr = parse_expr("CAST(123 AS TEXT)").unwrap();
        match expr {
            Expr::Cast { data_type, .. } => {
                assert_eq!(data_type, super::super::ast::DataType::Text);
            }
            _ => panic!("expected Cast"),
        }
    }

    #[test]
    fn test_cast_double_colon() {
        let expr = parse_expr("123::TEXT").unwrap();
        match expr {
            Expr::Cast { data_type, .. } => {
                assert_eq!(data_type, super::super::ast::DataType::Text);
            }
            _ => panic!("expected Cast"),
        }
    }

    #[test]
    fn test_cast_chain() {
        // 123::TEXT::VARCHAR should be ((123::TEXT)::VARCHAR)
        let expr = parse_expr("123::TEXT::VARCHAR").unwrap();
        match expr {
            Expr::Cast { expr: inner, data_type } => {
                assert_eq!(data_type, super::super::ast::DataType::Varchar(None));
                assert!(matches!(*inner, Expr::Cast { .. }));
            }
            _ => panic!("expected Cast"),
        }
    }
}
