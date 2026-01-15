use std::collections::HashMap;

/// A prepared statement stored on the connection.
#[derive(Debug, Clone)]
pub struct PreparedStatement {
    /// The original SQL query
    pub query: String,
    /// Parameter type OIDs (may be inferred later)
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
    pub _param_format_codes: Vec<i16>,
    /// Result column format codes
    pub _result_format_codes: Vec<i16>,
}

/// Per-connection state for Extended Query Protocol.
///
/// NOTE: No synchronization needed - this state is owned by a single connection.
#[derive(Debug, Default)]
pub struct ConnectionState {
    /// Named prepared statements. Key "" is the unnamed statement.
    statements: HashMap<String, PreparedStatement>,
    /// Named portals. Key "" is the unnamed portal.
    portals: HashMap<String, Portal>,
}

impl ConnectionState {
    /// Create a new connection state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Store a prepared statement. Replaces any existing statement with same name.
    /// If name is empty (""), this is the unnamed statement.
    pub fn put_statement(&mut self, name: String, stmt: PreparedStatement) {
        // Unnamed statement replaces any existing one and closes unnamed portal
        if name.is_empty() {
            self.portals.remove("");
        }
        self.statements.insert(name, stmt);
    }

    /// Get a prepared statement by name.
    pub fn get_statement(&self, name: &str) -> Option<&PreparedStatement> {
        self.statements.get(name)
    }

    /// Close a prepared statement. Also closes all portals referencing it.
    pub fn close_statement(&mut self, name: &str) {
        self.statements.remove(name);
        // Close all portals that reference this statement
        self.portals.retain(|_, p| p.statement_name != name);
    }

    /// Store a portal. Replaces any existing portal with same name.
    pub fn put_portal(&mut self, name: String, portal: Portal) {
        self.portals.insert(name, portal);
    }

    /// Get a portal by name.
    pub fn get_portal(&self, name: &str) -> Option<&Portal> {
        self.portals.get(name)
    }

    /// Close a portal by name.
    pub fn close_portal(&mut self, name: &str) {
        self.portals.remove(name);
    }

    /// Clear all unnamed statement/portal (called at end of extended query).
    /// Named ones persist across queries.
    pub fn clear_unnamed(&mut self) {
        // Per PostgreSQL: unnamed statement is closed at Sync
        // Named statements persist until explicitly closed
        self.statements.remove("");
        self.portals.remove("");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_statement_lifecycle() {
        let mut state = ConnectionState::new();

        // Create statement
        state.put_statement(
            "test".to_string(),
            PreparedStatement {
                query: "SELECT 1".to_string(),
                param_types: vec![],
            },
        );

        assert!(state.get_statement("test").is_some());
        assert!(state.get_statement("nonexistent").is_none());

        // Close statement
        state.close_statement("test");
        assert!(state.get_statement("test").is_none());
    }

    #[test]
    fn test_unnamed_statement_replacement() {
        let mut state = ConnectionState::new();

        // Create unnamed statement
        state.put_statement(
            "".to_string(),
            PreparedStatement {
                query: "SELECT 1".to_string(),
                param_types: vec![],
            },
        );

        // Create portal from unnamed statement
        state.put_portal(
            "".to_string(),
            Portal {
                statement_name: "".to_string(),
                _param_values: vec![],
                _param_format_codes: vec![],
                _result_format_codes: vec![],
            },
        );

        assert!(state.get_portal("").is_some());

        // Replace unnamed statement - should also close unnamed portal
        state.put_statement(
            "".to_string(),
            PreparedStatement {
                query: "SELECT 2".to_string(),
                param_types: vec![],
            },
        );

        assert!(state.get_portal("").is_none());
    }

    #[test]
    fn test_portal_cascade_close() {
        let mut state = ConnectionState::new();

        state.put_statement(
            "stmt".to_string(),
            PreparedStatement {
                query: "SELECT 1".to_string(),
                param_types: vec![],
            },
        );

        state.put_portal(
            "portal1".to_string(),
            Portal {
                statement_name: "stmt".to_string(),
                _param_values: vec![],
                _param_format_codes: vec![],
                _result_format_codes: vec![],
            },
        );

        // Closing statement should close dependent portals
        state.close_statement("stmt");
        assert!(state.get_portal("portal1").is_none());
    }

    #[test]
    fn test_clear_unnamed() {
        let mut state = ConnectionState::new();

        // Create both named and unnamed statements
        state.put_statement(
            "".to_string(),
            PreparedStatement {
                query: "SELECT 1".to_string(),
                param_types: vec![],
            },
        );
        state.put_statement(
            "named".to_string(),
            PreparedStatement {
                query: "SELECT 2".to_string(),
                param_types: vec![],
            },
        );

        // Create both named and unnamed portals
        state.put_portal(
            "".to_string(),
            Portal {
                statement_name: "".to_string(),
                _param_values: vec![],
                _param_format_codes: vec![],
                _result_format_codes: vec![],
            },
        );
        state.put_portal(
            "named_portal".to_string(),
            Portal {
                statement_name: "named".to_string(),
                _param_values: vec![],
                _param_format_codes: vec![],
                _result_format_codes: vec![],
            },
        );

        // Clear unnamed
        state.clear_unnamed();

        // Unnamed should be gone, named should remain
        assert!(state.get_statement("").is_none());
        assert!(state.get_statement("named").is_some());
        assert!(state.get_portal("").is_none());
        assert!(state.get_portal("named_portal").is_some());
    }
}
