//! Abstract Syntax Tree (AST) for SQL statements.
//!
//! This module defines the data structures that represent parsed SQL statements.
//! The AST is produced by the parser and consumed by the query planner/executor.

/// A SQL statement.
#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    /// SELECT statement.
    Select(Box<SelectStmt>),
    /// INSERT statement.
    Insert(Box<InsertStmt>),
    /// UPDATE statement.
    Update(Box<UpdateStmt>),
    /// DELETE statement.
    Delete(Box<DeleteStmt>),
    /// CREATE TABLE statement.
    CreateTable(Box<CreateTableStmt>),
    /// DROP TABLE statement.
    DropTable(DropTableStmt),
    /// CREATE INDEX statement.
    CreateIndex(CreateIndexStmt),
    /// DROP INDEX statement.
    DropIndex(DropIndexStmt),
    /// BEGIN or START TRANSACTION.
    Begin,
    /// COMMIT.
    Commit,
    /// ROLLBACK.
    Rollback,
    /// SET statement (session variable).
    Set(SetStmt),
    /// EXPLAIN statement.
    Explain(Box<Statement>),
}

/// SELECT statement.
#[derive(Debug, Clone, PartialEq)]
pub struct SelectStmt {
    /// Whether to select distinct rows only.
    pub distinct: bool,
    /// Selected columns/expressions.
    pub columns: Vec<SelectItem>,
    /// FROM clause.
    pub from: Option<FromClause>,
    /// WHERE clause.
    pub where_clause: Option<Expr>,
    /// GROUP BY expressions.
    pub group_by: Vec<Expr>,
    /// HAVING clause.
    pub having: Option<Expr>,
    /// ORDER BY clause.
    pub order_by: Vec<OrderByItem>,
    /// LIMIT clause.
    pub limit: Option<Expr>,
    /// OFFSET clause.
    pub offset: Option<Expr>,
    /// FOR UPDATE/SHARE locking.
    pub locking: Option<LockingClause>,
}

/// An item in the SELECT list.
#[derive(Debug, Clone, PartialEq)]
pub enum SelectItem {
    /// SELECT * - all columns.
    Wildcard,
    /// SELECT table.* - all columns from a table.
    QualifiedWildcard(String),
    /// An expression with optional alias.
    Expr { expr: Expr, alias: Option<String> },
}

/// FROM clause.
#[derive(Debug, Clone, PartialEq)]
pub struct FromClause {
    /// The table references.
    pub tables: Vec<TableRef>,
}

/// A table reference in FROM clause.
#[derive(Debug, Clone, PartialEq)]
pub enum TableRef {
    /// Simple table reference.
    Table { name: String, alias: Option<String> },
    /// Join between tables.
    Join {
        left: Box<TableRef>,
        join_type: JoinType,
        right: Box<TableRef>,
        condition: Option<JoinCondition>,
    },
    /// Subquery.
    Subquery {
        query: Box<SelectStmt>,
        alias: String,
    },
}

/// Type of JOIN.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JoinType {
    /// INNER JOIN.
    Inner,
    /// LEFT [OUTER] JOIN.
    Left,
    /// RIGHT [OUTER] JOIN.
    Right,
    /// FULL [OUTER] JOIN.
    Full,
    /// CROSS JOIN.
    Cross,
}

/// JOIN condition.
#[derive(Debug, Clone, PartialEq)]
pub enum JoinCondition {
    /// ON condition.
    On(Expr),
    /// USING (column_list).
    Using(Vec<String>),
}

/// ORDER BY item.
#[derive(Debug, Clone, PartialEq)]
pub struct OrderByItem {
    /// Expression to order by.
    pub expr: Expr,
    /// Sort direction.
    pub direction: SortDirection,
    /// NULL ordering.
    pub nulls: NullOrdering,
}

/// Sort direction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SortDirection {
    /// Ascending order.
    #[default]
    Asc,
    /// Descending order.
    Desc,
}

/// NULL value ordering in ORDER BY.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum NullOrdering {
    /// Use default NULL ordering (NULLS LAST for ASC, NULLS FIRST for DESC).
    #[default]
    Default,
    /// NULLS FIRST.
    First,
    /// NULLS LAST.
    Last,
}

/// Locking clause (FOR UPDATE/SHARE).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockingClause {
    /// Locking mode.
    pub mode: LockMode,
}

/// Lock mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LockMode {
    /// FOR UPDATE.
    Update,
    /// FOR SHARE.
    Share,
}

/// INSERT statement.
#[derive(Debug, Clone, PartialEq)]
pub struct InsertStmt {
    /// Target table name.
    pub table: String,
    /// Column names (empty means all columns).
    pub columns: Vec<String>,
    /// VALUES to insert.
    pub values: Vec<Vec<Expr>>,
}

/// UPDATE statement.
#[derive(Debug, Clone, PartialEq)]
pub struct UpdateStmt {
    /// Target table name.
    pub table: String,
    /// SET assignments.
    pub assignments: Vec<Assignment>,
    /// WHERE clause.
    pub where_clause: Option<Expr>,
}

/// SET assignment (column = value).
#[derive(Debug, Clone, PartialEq)]
pub struct Assignment {
    /// Column name.
    pub column: String,
    /// Value expression.
    pub value: Expr,
}

/// DELETE statement.
#[derive(Debug, Clone, PartialEq)]
pub struct DeleteStmt {
    /// Target table name.
    pub table: String,
    /// WHERE clause.
    pub where_clause: Option<Expr>,
}

/// CREATE TABLE statement.
#[derive(Debug, Clone, PartialEq)]
pub struct CreateTableStmt {
    /// Table name.
    pub name: String,
    /// Column definitions.
    pub columns: Vec<ColumnDef>,
    /// Table-level constraints.
    pub constraints: Vec<TableConstraint>,
}

/// Column definition.
#[derive(Debug, Clone, PartialEq)]
pub struct ColumnDef {
    /// Column name.
    pub name: String,
    /// Data type.
    pub data_type: DataType,
    /// Column constraints.
    pub constraints: Vec<ColumnConstraint>,
}

/// SQL data type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DataType {
    /// BOOLEAN.
    Boolean,
    /// SMALLINT.
    Smallint,
    /// INTEGER or INT.
    Integer,
    /// BIGINT.
    Bigint,
    /// REAL.
    Real,
    /// DOUBLE PRECISION.
    DoublePrecision,
    /// TEXT.
    Text,
    /// VARCHAR(n) - None means no length limit.
    Varchar(Option<u32>),
    /// BYTEA.
    Bytea,
    /// SERIAL (auto-increment INTEGER).
    Serial,
}

impl DataType {
    /// Returns the display name for this data type.
    pub fn display_name(&self) -> String {
        match self {
            DataType::Boolean => "BOOLEAN".to_string(),
            DataType::Smallint => "SMALLINT".to_string(),
            DataType::Integer => "INTEGER".to_string(),
            DataType::Bigint => "BIGINT".to_string(),
            DataType::Real => "REAL".to_string(),
            DataType::DoublePrecision => "DOUBLE PRECISION".to_string(),
            DataType::Text => "TEXT".to_string(),
            DataType::Varchar(None) => "VARCHAR".to_string(),
            DataType::Varchar(Some(n)) => format!("VARCHAR({n})"),
            DataType::Bytea => "BYTEA".to_string(),
            DataType::Serial => "SERIAL".to_string(),
        }
    }
}

/// Column constraint.
#[derive(Debug, Clone, PartialEq)]
pub enum ColumnConstraint {
    /// NOT NULL.
    NotNull,
    /// NULL (explicit nullable).
    Null,
    /// PRIMARY KEY.
    PrimaryKey,
    /// UNIQUE.
    Unique,
    /// DEFAULT value.
    Default(Expr),
    /// CHECK constraint.
    Check(Expr),
    /// REFERENCES (foreign key).
    References {
        table: String,
        column: Option<String>,
    },
}

/// Table-level constraint.
#[derive(Debug, Clone, PartialEq)]
pub struct TableConstraint {
    /// Optional constraint name.
    pub name: Option<String>,
    /// Constraint kind.
    pub kind: TableConstraintKind,
}

/// Kind of table constraint.
#[derive(Debug, Clone, PartialEq)]
pub enum TableConstraintKind {
    /// PRIMARY KEY (columns).
    PrimaryKey(Vec<String>),
    /// UNIQUE (columns).
    Unique(Vec<String>),
    /// CHECK (expression).
    Check(Expr),
    /// FOREIGN KEY (columns) REFERENCES table (columns).
    ForeignKey {
        columns: Vec<String>,
        ref_table: String,
        ref_columns: Vec<String>,
    },
}

/// SET statement.
#[derive(Debug, Clone, PartialEq)]
pub struct SetStmt {
    /// Variable name.
    pub name: String,
    /// Value expression.
    pub value: Expr,
}

/// DROP TABLE statement.
#[derive(Debug, Clone, PartialEq)]
pub struct DropTableStmt {
    /// Table name to drop.
    pub name: String,
    /// If true, don't error if table doesn't exist.
    pub if_exists: bool,
}

/// CREATE INDEX statement.
#[derive(Debug, Clone, PartialEq)]
pub struct CreateIndexStmt {
    /// Index name.
    pub name: String,
    /// Table to create index on.
    pub table: String,
    /// Columns to index.
    pub columns: Vec<IndexColumn>,
    /// If true, don't error if index already exists.
    pub if_not_exists: bool,
    /// If true, create a unique index.
    pub unique: bool,
}

/// A column in an index definition.
#[derive(Debug, Clone, PartialEq)]
pub struct IndexColumn {
    /// Column name.
    pub name: String,
    /// Sort direction (for B+tree indexes).
    pub direction: SortDirection,
}

/// DROP INDEX statement.
#[derive(Debug, Clone, PartialEq)]
pub struct DropIndexStmt {
    /// Index name to drop.
    pub name: String,
    /// If true, don't error if index doesn't exist.
    pub if_exists: bool,
}

/// Expression in SQL.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// NULL literal.
    Null,
    /// Boolean literal.
    Boolean(bool),
    /// Integer literal.
    Integer(i64),
    /// Float literal.
    Float(f64),
    /// String literal.
    String(String),
    /// Column reference (optionally qualified with table name).
    ColumnRef {
        table: Option<String>,
        column: String,
    },
    /// Positional parameter ($1, $2, etc.).
    Parameter(u32),
    /// Binary operation.
    BinaryOp {
        left: Box<Expr>,
        op: BinaryOperator,
        right: Box<Expr>,
    },
    /// Unary operation.
    UnaryOp {
        op: UnaryOperator,
        operand: Box<Expr>,
    },
    /// IS NULL / IS NOT NULL.
    IsNull { expr: Box<Expr>, negated: bool },
    /// IN list: expr [NOT] IN (value1, value2, ...).
    InList {
        expr: Box<Expr>,
        list: Vec<Expr>,
        negated: bool,
    },
    /// IN subquery: expr [NOT] IN (SELECT ...).
    InSubquery {
        expr: Box<Expr>,
        subquery: Box<SelectStmt>,
        negated: bool,
    },
    /// BETWEEN: expr [NOT] BETWEEN low AND high.
    Between {
        expr: Box<Expr>,
        low: Box<Expr>,
        high: Box<Expr>,
        negated: bool,
    },
    /// LIKE: expr [NOT] LIKE pattern [ESCAPE escape].
    Like {
        expr: Box<Expr>,
        pattern: Box<Expr>,
        escape: Option<Box<Expr>>,
        negated: bool,
        case_insensitive: bool,
    },
    /// EXISTS (subquery).
    Exists {
        subquery: Box<SelectStmt>,
        negated: bool,
    },
    /// CASE expression.
    Case {
        operand: Option<Box<Expr>>,
        when_clauses: Vec<WhenClause>,
        else_result: Option<Box<Expr>>,
    },
    /// Type cast: CAST(expr AS type) or expr::type.
    Cast {
        expr: Box<Expr>,
        data_type: DataType,
    },
    /// Function call.
    Function {
        name: String,
        args: Vec<Expr>,
        distinct: bool,
    },
    /// Subquery expression (scalar subquery).
    Subquery(Box<SelectStmt>),
}

/// A WHEN clause in a CASE expression.
#[derive(Debug, Clone, PartialEq)]
pub struct WhenClause {
    /// The condition (or value to match in simple CASE).
    pub condition: Expr,
    /// The result if condition is true.
    pub result: Expr,
}

/// Binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOperator {
    // Arithmetic
    /// +
    Add,
    /// -
    Sub,
    /// *
    Mul,
    /// /
    Div,
    /// %
    Mod,

    // Comparison
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

    // Logical
    /// AND
    And,
    /// OR
    Or,

    // String
    /// || (concatenation)
    Concat,
}

impl BinaryOperator {
    /// Returns the display string for this operator.
    pub fn as_str(&self) -> &'static str {
        match self {
            BinaryOperator::Add => "+",
            BinaryOperator::Sub => "-",
            BinaryOperator::Mul => "*",
            BinaryOperator::Div => "/",
            BinaryOperator::Mod => "%",
            BinaryOperator::Eq => "=",
            BinaryOperator::Neq => "<>",
            BinaryOperator::Lt => "<",
            BinaryOperator::LtEq => "<=",
            BinaryOperator::Gt => ">",
            BinaryOperator::GtEq => ">=",
            BinaryOperator::And => "AND",
            BinaryOperator::Or => "OR",
            BinaryOperator::Concat => "||",
        }
    }
}

/// Unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOperator {
    /// NOT
    Not,
    /// - (negation)
    Minus,
    /// + (positive, no-op)
    Plus,
}

impl UnaryOperator {
    /// Returns the display string for this operator.
    pub fn as_str(&self) -> &'static str {
        match self {
            UnaryOperator::Not => "NOT",
            UnaryOperator::Minus => "-",
            UnaryOperator::Plus => "+",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_data_type_display() {
        assert_eq!(DataType::Integer.display_name(), "INTEGER");
        assert_eq!(DataType::Varchar(None).display_name(), "VARCHAR");
        assert_eq!(DataType::Varchar(Some(255)).display_name(), "VARCHAR(255)");
        assert_eq!(DataType::DoublePrecision.display_name(), "DOUBLE PRECISION");
    }

    #[test]
    fn test_binary_operator_str() {
        assert_eq!(BinaryOperator::Add.as_str(), "+");
        assert_eq!(BinaryOperator::And.as_str(), "AND");
        assert_eq!(BinaryOperator::Neq.as_str(), "<>");
    }
}
