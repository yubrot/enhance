//! Query execution plans.
//!
//! A [`Plan`] represents a logical execution plan for a query. Plans are
//! created by the planner from AST and then converted to executors for
//! actual execution.

use super::expr::BoundExpr;
use crate::storage::PageId;

/// Metadata about an output column.
#[derive(Debug, Clone, PartialEq)]
pub struct ColumnDesc {
    /// Column name (for display in result headers).
    pub name: String,
    /// PostgreSQL type OID.
    pub type_oid: i32,
}

impl ColumnDesc {
    /// Creates a new column descriptor.
    pub fn new(name: impl Into<String>, type_oid: i32) -> Self {
        Self {
            name: name.into(),
            type_oid,
        }
    }
}

/// A query execution plan.
///
/// Plans form a tree structure where leaf nodes access data (SeqScan)
/// and internal nodes transform or filter the data flow.
#[derive(Debug, Clone, PartialEq)]
pub enum Plan {
    /// Sequential scan of a heap table.
    SeqScan {
        /// Table name (for display).
        table_name: String,
        /// Table ID in the catalog.
        table_id: u32,
        /// First page of the heap.
        first_page: PageId,
        /// Column type OIDs for deserialization.
        schema: Vec<i32>,
        /// Output column descriptors.
        output_columns: Vec<ColumnDesc>,
    },

    /// Filter operator (WHERE clause).
    Filter {
        /// Input plan.
        input: Box<Plan>,
        /// Predicate expression.
        predicate: BoundExpr,
    },

    /// Projection operator (SELECT list).
    Projection {
        /// Input plan.
        input: Box<Plan>,
        /// Projection expressions.
        exprs: Vec<BoundExpr>,
        /// Output column descriptors.
        output_columns: Vec<ColumnDesc>,
    },
}

impl Plan {
    /// Returns the output column descriptors for this plan.
    pub fn output_columns(&self) -> &[ColumnDesc] {
        match self {
            Plan::SeqScan { output_columns, .. } => output_columns,
            Plan::Filter { input, .. } => input.output_columns(),
            Plan::Projection { output_columns, .. } => output_columns,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protocol::type_oid;

    #[test]
    fn test_column_desc() {
        let col = ColumnDesc::new("id", type_oid::INT4);
        assert_eq!(col.name, "id");
        assert_eq!(col.type_oid, type_oid::INT4);
    }

    #[test]
    fn test_plan_output_columns() {
        let scan = Plan::SeqScan {
            table_name: "test".to_string(),
            table_id: 100,
            first_page: PageId::new(1),
            schema: vec![type_oid::INT4, type_oid::TEXT],
            output_columns: vec![
                ColumnDesc::new("id", type_oid::INT4),
                ColumnDesc::new("name", type_oid::TEXT),
            ],
        };

        assert_eq!(scan.output_columns().len(), 2);
        assert_eq!(scan.output_columns()[0].name, "id");

        // Filter preserves input columns
        let filter = Plan::Filter {
            input: Box::new(scan.clone()),
            predicate: BoundExpr::Boolean(true),
        };
        assert_eq!(filter.output_columns().len(), 2);

        // Projection can change columns
        let projection = Plan::Projection {
            input: Box::new(scan),
            exprs: vec![BoundExpr::Column(0)],
            output_columns: vec![ColumnDesc::new("id", type_oid::INT4)],
        };
        assert_eq!(projection.output_columns().len(), 1);
    }
}
