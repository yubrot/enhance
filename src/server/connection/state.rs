use std::collections::HashMap;

use crate::protocol::{ErrorInfo, FormatCode, sql_state};
use crate::sql::Statement;

/// Per-connection state for Extended Query Protocol.
///
/// This struct manages protocol-level state (prepared statements and portals).
/// Transaction state is managed by [`crate::db::Session`].
#[derive(Debug, Default)]
pub struct ConnectionState {
    /// Named prepared statements. Key "" is the unnamed statement.
    statements: HashMap<String, PreparedStatement>,
    /// Named portals. Key "" is the unnamed portal.
    portals: HashMap<String, Portal>,
    /// Error state flag. When true, extended query messages are skipped until Sync.
    pub in_error: bool,
}

impl ConnectionState {
    /// Create a new connection state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Store a prepared statement. Replaces any existing statement with same name.
    /// If name is empty (""), this is the unnamed statement.
    pub fn put_statement(&mut self, name: String, stmt: PreparedStatement) {
        self.close_statement(&name);
        self.statements.insert(name, stmt);
    }

    /// Resolves a prepared statement by name.
    pub fn resolve_statement(&self, name: &str) -> Result<&PreparedStatement, ErrorInfo> {
        self.statements.get(name).ok_or_else(|| {
            ErrorInfo::new(
                sql_state::INVALID_SQL_STATEMENT_NAME,
                format!("prepared statement \"{}\" does not exist", name),
            )
        })
    }

    /// Close a prepared statement. Also closes all portals referencing it.
    pub fn close_statement(&mut self, name: &str) {
        if self.statements.remove(name).is_some() {
            // Close all portals that reference this statement
            self.portals.retain(|_, p| p.statement_name != name);
        }
    }

    /// Store a portal. Replaces any existing portal with same name.
    pub fn put_portal(&mut self, name: String, portal: Portal) {
        self.portals.insert(name, portal);
    }

    /// Resolves a portal by name.
    fn resolve_portal(&self, name: &str) -> Result<&Portal, ErrorInfo> {
        self.portals.get(name).ok_or_else(|| {
            ErrorInfo::new(
                sql_state::INVALID_CURSOR_NAME,
                format!("portal \"{}\" does not exist", name),
            )
        })
    }

    /// Close a portal by name.
    pub fn close_portal(&mut self, name: &str) {
        self.portals.remove(name);
    }

    /// Resolves a portal name to its backing prepared statement.
    pub fn resolve_portal_statement(
        &self,
        portal_name: &str,
    ) -> Result<&PreparedStatement, ErrorInfo> {
        let portal = self.resolve_portal(portal_name)?;
        self.resolve_statement(&portal.statement_name)
    }

    /// Clear all unnamed statement/portal (called at end of extended query).
    /// Named ones persist across queries.
    pub fn clear_unnamed(&mut self) {
        // Unnamed statement is closed at Sync (matching PostgreSQL protocol semantics)
        // Named statements persist until explicitly closed
        self.close_statement("");
        self.close_portal("");
    }
}

/// A prepared statement stored on the connection.
#[derive(Debug, Clone)]
pub struct PreparedStatement {
    /// Parsed AST.
    pub ast: Statement,
    /// Parameter type OIDs (may be inferred later).
    pub param_types: Vec<i32>,
}

/// A portal (bound prepared statement) stored on the connection.
#[derive(Debug, Clone)]
pub struct Portal {
    /// Name of the source prepared statement
    pub statement_name: String,
    /// Bound parameter values (None = NULL)
    pub _param_values: Vec<Option<Vec<u8>>>,
    /// Parameter format codes
    pub _param_format_codes: Vec<FormatCode>,
    /// Result column format codes
    pub _result_format_codes: Vec<FormatCode>,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dummy_stmt() -> PreparedStatement {
        use crate::sql::Parser;
        PreparedStatement {
            ast: Parser::new("SELECT *").parse().unwrap().unwrap(),
            param_types: vec![],
        }
    }

    #[test]
    fn test_resolve_statement() {
        let mut state = ConnectionState::new();

        // Non-existent statement → error
        let err = state.resolve_statement("test").unwrap_err();
        assert_eq!(err.code, sql_state::INVALID_SQL_STATEMENT_NAME);

        // Create and resolve
        state.put_statement("test".to_string(), dummy_stmt());
        assert!(state.resolve_statement("test").is_ok());

        // Close statement → error again
        state.close_statement("test");
        assert!(state.resolve_statement("test").is_err());
    }

    #[test]
    fn test_resolve_portal() {
        let mut state = ConnectionState::new();

        // Non-existent portal → error
        let err = state.resolve_portal("p").unwrap_err();
        assert_eq!(err.code, sql_state::INVALID_CURSOR_NAME);

        // Create and resolve
        state.put_portal("p".to_string(), dummy_portal("s"));
        assert!(state.resolve_portal("p").is_ok());

        // Close portal → error again
        state.close_portal("p");
        assert!(state.resolve_portal("p").is_err());
    }

    #[test]
    fn test_statement_replacement() {
        let mut state = ConnectionState::new();

        // Create named statement
        state.put_statement("stmt".to_string(), dummy_stmt());

        // Create portal from named statement
        state.put_portal("portal1".to_string(), dummy_portal("stmt"));

        assert!(state.resolve_portal("portal1").is_ok());

        // Replace named statement - should also close dependent portals
        state.put_statement("stmt".to_string(), dummy_stmt());

        assert!(state.resolve_portal("portal1").is_err());
    }

    fn dummy_portal(statement_name: &str) -> Portal {
        Portal {
            statement_name: statement_name.to_string(),
            _param_values: vec![],
            _param_format_codes: vec![],
            _result_format_codes: vec![],
        }
    }

    #[test]
    fn test_resolve_portal_statement() {
        let mut state = ConnectionState::new();

        // Portal without statement → error
        state.put_portal("p".to_string(), dummy_portal("s"));
        let err = state.resolve_portal_statement("p").unwrap_err();
        assert_eq!(err.code, sql_state::INVALID_SQL_STATEMENT_NAME);

        // Non-existent portal → error
        let err = state.resolve_portal_statement("no_such").unwrap_err();
        assert_eq!(err.code, sql_state::INVALID_CURSOR_NAME);

        // Valid portal → returns the prepared statement
        state.put_statement("s".to_string(), dummy_stmt());
        let resolved = state.resolve_portal_statement("p").unwrap();
        assert!(matches!(resolved.ast, Statement::Select(_)));
    }

    #[test]
    fn test_clear_unnamed() {
        let mut state = ConnectionState::new();

        // Create both named and unnamed statements
        state.put_statement("".to_string(), dummy_stmt());
        state.put_statement("named".to_string(), dummy_stmt());

        // Create both named and unnamed portals
        state.put_portal("".to_string(), dummy_portal(""));
        state.put_portal("named_portal".to_string(), dummy_portal("named"));

        // Clear unnamed
        state.clear_unnamed();

        // Unnamed should be gone, named should remain
        assert!(state.resolve_statement("").is_err());
        assert!(state.resolve_statement("named").is_ok());
        assert!(state.resolve_portal("").is_err());
        assert!(state.resolve_portal("named_portal").is_ok());
    }
}
