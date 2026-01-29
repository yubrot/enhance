//! Query planner for converting AST to execution plan.
//!
//! This is a simple direct translation planner without optimization.
//! Rule-based optimization for index selection comes in Step 17.

use std::sync::Arc;

use crate::catalog::{Catalog, ColumnInfo};
use crate::executor::plan::{
    Aggregate, AggregateExpr, AggregateFunction, Executor, Filter, OutputColumn, Projection,
    SeqScan, Sort, SortKey,
};
use crate::executor::ExecutorError;
use crate::protocol::type_oid;
use crate::sql::{Expr, SelectItem, SelectStmt, TableRef};
use crate::storage::{BufferPool, Replacer, Storage};
use crate::tx::{Snapshot, TransactionManager};

/// Result type for projection building: (expressions with aliases, output column metadata).
type ProjectionResult = Result<(Vec<(Expr, String)>, Vec<OutputColumn>), ExecutorError>;

/// Result type for aggregate analysis.
#[derive(Debug)]
struct AggregateAnalysis {
    /// Aggregate expressions found in SELECT list.
    aggregates: Vec<AggregateExpr>,
    /// Non-aggregate expressions in SELECT list.
    non_agg_exprs: Vec<(Expr, String)>,
    /// Output columns for the aggregate.
    output_columns: Vec<OutputColumn>,
    /// Whether any aggregates were found.
    has_aggregates: bool,
}

/// Plans a SELECT statement into an executor tree.
///
/// The pipeline order is:
/// SeqScan → Filter (WHERE) → Aggregate (GROUP BY + HAVING) → Sort (ORDER BY) → Projection
///
/// # Arguments
///
/// * `stmt` - The SELECT statement to plan.
/// * `snapshot` - MVCC snapshot for visibility.
/// * `catalog` - Catalog for table/column lookups.
/// * `pool` - Buffer pool for page access.
/// * `tx_manager` - Transaction manager.
///
/// # Errors
///
/// Returns an error if the table is not found or the query is unsupported.
pub async fn plan_select<S: Storage + 'static, R: Replacer + 'static>(
    stmt: &SelectStmt,
    snapshot: Snapshot,
    catalog: &Catalog<S, R>,
    pool: Arc<BufferPool<S, R>>,
    tx_manager: Arc<TransactionManager>,
) -> Result<Box<dyn Executor>, ExecutorError> {
    // Validate unsupported features
    if stmt.distinct {
        return Err(ExecutorError::Unsupported {
            feature: "DISTINCT".to_string(),
        });
    }
    if stmt.limit.is_some() {
        return Err(ExecutorError::Unsupported {
            feature: "LIMIT".to_string(),
        });
    }
    if stmt.offset.is_some() {
        return Err(ExecutorError::Unsupported {
            feature: "OFFSET".to_string(),
        });
    }
    if stmt.locking.is_some() {
        return Err(ExecutorError::Unsupported {
            feature: "FOR UPDATE/SHARE".to_string(),
        });
    }

    // Get the source table
    let from = stmt.from.as_ref().ok_or_else(|| ExecutorError::Unsupported {
        feature: "SELECT without FROM".to_string(),
    })?;

    if from.tables.len() != 1 {
        return Err(ExecutorError::Unsupported {
            feature: "multiple tables (JOINs)".to_string(),
        });
    }

    let table_ref = &from.tables[0];
    let (table_name, _alias) = match table_ref {
        TableRef::Table { name, alias } => (name.clone(), alias.clone()),
        TableRef::Join { .. } => {
            return Err(ExecutorError::Unsupported {
                feature: "JOINs".to_string(),
            });
        }
        TableRef::Subquery { .. } => {
            return Err(ExecutorError::Unsupported {
                feature: "subqueries in FROM".to_string(),
            });
        }
    };

    // Look up table in catalog
    let table_info = catalog
        .get_table(&snapshot, &table_name)
        .await?
        .ok_or_else(|| ExecutorError::TableNotFound {
            name: table_name.clone(),
        })?;

    let columns = catalog.get_columns(&snapshot, table_info.table_id).await?;

    // Analyze SELECT list for aggregates
    let agg_analysis = analyze_aggregates(&stmt.columns, &columns, &table_name)?;
    let has_group_by = !stmt.group_by.is_empty();
    let has_aggregates = agg_analysis.has_aggregates;

    // HAVING requires GROUP BY or aggregates
    if stmt.having.is_some() && !has_group_by && !has_aggregates {
        return Err(ExecutorError::InvalidOperation {
            message: "HAVING clause requires GROUP BY or aggregate functions".to_string(),
        });
    }

    // Create SeqScan
    let scan = SeqScan::new(
        table_name.clone(),
        columns.clone(),
        table_info.first_page,
        snapshot,
        pool,
        tx_manager,
    );

    // Build pipeline: SeqScan → Filter → Aggregate → Sort → Projection
    // We need to handle the generic types carefully here

    // Apply WHERE filter if present
    let filtered: Box<dyn Executor> = if let Some(where_clause) = &stmt.where_clause {
        Box::new(Filter::new(scan, columns.clone(), where_clause.clone()))
    } else {
        Box::new(scan)
    };

    // Apply aggregation if needed
    let aggregated: Box<dyn Executor> = if has_group_by || has_aggregates {
        let agg = Aggregate::new(
            filtered,
            columns.clone(),
            stmt.group_by.clone(),
            agg_analysis.aggregates.clone(),
            agg_analysis.non_agg_exprs.clone(),
            stmt.having.clone(),
            agg_analysis.output_columns.clone(),
        );
        Box::new(agg)
    } else {
        filtered
    };

    // Apply ORDER BY if present
    let sorted: Box<dyn Executor> = if !stmt.order_by.is_empty() {
        // Build sort keys
        let sort_keys: Vec<SortKey> = stmt
            .order_by
            .iter()
            .map(|item| SortKey::new(item.expr.clone(), item.direction, item.nulls))
            .collect();

        // For sorting, we need to use the right column info:
        // - If aggregated, use the aggregation output columns
        // - Otherwise, use the source columns
        let sort_columns = if has_group_by || has_aggregates {
            // Build column info from aggregate output
            build_aggregate_output_columns(&stmt.group_by, &agg_analysis, &columns)
        } else {
            columns.clone()
        };

        Box::new(Sort::new(aggregated, sort_columns, sort_keys))
    } else {
        aggregated
    };

    // Apply projection
    let (output_exprs, output_columns) = if has_group_by || has_aggregates {
        // For aggregate queries, the output is already in the right shape
        // We need to build expressions that reference the aggregate output
        build_aggregate_projection(&stmt.group_by, &agg_analysis)
    } else {
        build_projection(&stmt.columns, &columns, &table_name)?
    };

    // Build final column info for projection
    let projection_columns = if has_group_by || has_aggregates {
        build_aggregate_output_columns(&stmt.group_by, &agg_analysis, &columns)
    } else {
        columns
    };

    let projection = Projection::new(sorted, projection_columns, output_exprs, output_columns);
    Ok(Box::new(projection))
}

/// Analyzes SELECT items for aggregate functions.
fn analyze_aggregates(
    select_items: &[SelectItem],
    columns: &[ColumnInfo],
    table_name: &str,
) -> Result<AggregateAnalysis, ExecutorError> {
    let mut aggregates = Vec::new();
    let mut non_agg_exprs = Vec::new();
    let mut output_columns = Vec::new();
    let mut has_aggregates = false;

    for item in select_items {
        match item {
            SelectItem::Wildcard => {
                // SELECT * - include all columns as non-aggregate
                for col in columns {
                    let expr = Expr::ColumnRef {
                        table: None,
                        column: col.column_name.clone(),
                    };
                    non_agg_exprs.push((expr, col.column_name.clone()));
                    output_columns.push(OutputColumn::new(col.column_name.clone(), col.type_oid));
                }
            }
            SelectItem::QualifiedWildcard(qual_table) => {
                if qual_table != table_name {
                    return Err(ExecutorError::TableNotFound {
                        name: qual_table.clone(),
                    });
                }
                for col in columns {
                    let expr = Expr::ColumnRef {
                        table: Some(qual_table.clone()),
                        column: col.column_name.clone(),
                    };
                    non_agg_exprs.push((expr, col.column_name.clone()));
                    output_columns.push(OutputColumn::new(col.column_name.clone(), col.type_oid));
                }
            }
            SelectItem::Expr { expr, alias } => {
                if let Some(agg_expr) = extract_aggregate(expr, alias, columns)? {
                    has_aggregates = true;
                    output_columns.push(OutputColumn::new(
                        agg_expr.alias.clone(),
                        infer_aggregate_type(&agg_expr),
                    ));
                    aggregates.push(agg_expr);
                } else {
                    let name = alias.clone().unwrap_or_else(|| expr_to_name(expr));
                    let type_oid = infer_type(expr, columns);
                    non_agg_exprs.push((expr.clone(), name.clone()));
                    output_columns.push(OutputColumn::new(name, type_oid));
                }
            }
        }
    }

    Ok(AggregateAnalysis {
        aggregates,
        non_agg_exprs,
        output_columns,
        has_aggregates,
    })
}

/// Checks if an expression is the special `*` wildcard used in COUNT(*).
fn is_count_star_arg(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::ColumnRef {
            table: None,
            column,
        } if column == "*"
    )
}

/// Extracts an aggregate expression from an expression if it's an aggregate function.
fn extract_aggregate(
    expr: &Expr,
    alias: &Option<String>,
    _columns: &[ColumnInfo],
) -> Result<Option<AggregateExpr>, ExecutorError> {
    match expr {
        Expr::Function { name, args, distinct } => {
            if let Some(func) = AggregateFunction::from_name(name) {
                // Determine the argument expression
                // COUNT(*) is special - it's parsed as ColumnRef { column: "*" }
                let arg = if args.is_empty() {
                    None
                } else if args.len() == 1 {
                    if is_count_star_arg(&args[0]) {
                        // COUNT(*) case
                        None
                    } else {
                        Some(args[0].clone())
                    }
                } else {
                    return Err(ExecutorError::InvalidOperation {
                        message: format!(
                            "aggregate function {} takes at most 1 argument, got {}",
                            name,
                            args.len()
                        ),
                    });
                };

                // Determine alias
                let output_alias = alias.clone().unwrap_or_else(|| {
                    let arg_str = match &arg {
                        Some(e) => expr_to_name(e),
                        None => "*".to_string(),
                    };
                    format!("{}({})", func.name(), arg_str)
                });

                // NOTE: COUNT(DISTINCT) requires tracking distinct values (not implemented)
                if *distinct && func != AggregateFunction::Count {
                    return Err(ExecutorError::Unsupported {
                        feature: format!("{} DISTINCT", func.name().to_uppercase()),
                    });
                }

                Ok(Some(AggregateExpr::new(func, arg, *distinct, output_alias)))
            } else {
                // Not an aggregate function - unsupported regular function
                Err(ExecutorError::Unsupported {
                    feature: format!("function {}", name),
                })
            }
        }
        _ => Ok(None),
    }
}

/// Infers the type OID for an aggregate function result.
fn infer_aggregate_type(agg: &AggregateExpr) -> i32 {
    match agg.function {
        AggregateFunction::Count => type_oid::INT8,
        AggregateFunction::Sum => type_oid::INT8, // May be FLOAT8 at runtime
        AggregateFunction::Avg => type_oid::FLOAT8,
        AggregateFunction::Min | AggregateFunction::Max => {
            // Type depends on the argument, use UNKNOWN for now
            type_oid::UNKNOWN
        }
    }
}

/// Builds column info for aggregate output.
fn build_aggregate_output_columns(
    group_by: &[Expr],
    analysis: &AggregateAnalysis,
    source_columns: &[ColumnInfo],
) -> Vec<ColumnInfo> {
    let mut result = Vec::new();
    let mut idx = 0u32;

    // First, GROUP BY columns
    for expr in group_by {
        let name = match expr {
            Expr::ColumnRef { column, .. } => column.clone(),
            _ => format!("group_{}", idx),
        };
        let type_oid = infer_type(expr, source_columns);
        result.push(ColumnInfo::new(0, idx, name, type_oid, 0));
        idx += 1;
    }

    // Then, aggregate results
    for agg in &analysis.aggregates {
        let type_oid = infer_aggregate_type(agg);
        result.push(ColumnInfo::new(0, idx, agg.alias.clone(), type_oid, 0));
        idx += 1;
    }

    result
}

/// Builds projection expressions for aggregate output.
fn build_aggregate_projection(
    group_by: &[Expr],
    analysis: &AggregateAnalysis,
) -> (Vec<(Expr, String)>, Vec<OutputColumn>) {
    let mut output_exprs = Vec::new();
    let mut output_columns = Vec::new();

    // GROUP BY columns come first in the aggregate output
    for (i, expr) in group_by.iter().enumerate() {
        let name = match expr {
            Expr::ColumnRef { column, .. } => column.clone(),
            _ => format!("group_{}", i),
        };
        // Reference by column name in the aggregate output
        let col_ref = Expr::ColumnRef {
            table: None,
            column: name.clone(),
        };
        output_exprs.push((col_ref, name.clone()));
        output_columns.push(OutputColumn::new(name, type_oid::UNKNOWN));
    }

    // Then aggregate results
    for agg in &analysis.aggregates {
        let col_ref = Expr::ColumnRef {
            table: None,
            column: agg.alias.clone(),
        };
        output_exprs.push((col_ref, agg.alias.clone()));
        output_columns.push(OutputColumn::new(
            agg.alias.clone(),
            infer_aggregate_type(agg),
        ));
    }

    (output_exprs, output_columns)
}

/// Checks if an expression contains an aggregate function.
#[allow(dead_code)]
fn contains_aggregate(expr: &Expr) -> bool {
    match expr {
        Expr::Function { name, .. } => AggregateFunction::from_name(name).is_some(),
        Expr::BinaryOp { left, right, .. } => contains_aggregate(left) || contains_aggregate(right),
        Expr::UnaryOp { operand, .. } => contains_aggregate(operand),
        Expr::IsNull { expr, .. } => contains_aggregate(expr),
        Expr::Between { expr, low, high, .. } => {
            contains_aggregate(expr) || contains_aggregate(low) || contains_aggregate(high)
        }
        Expr::InList { expr, list, .. } => {
            contains_aggregate(expr) || list.iter().any(contains_aggregate)
        }
        Expr::Case { operand, when_clauses, else_result } => {
            operand.as_ref().is_some_and(|e| contains_aggregate(e))
                || when_clauses.iter().any(|w| {
                    contains_aggregate(&w.condition) || contains_aggregate(&w.result)
                })
                || else_result.as_ref().is_some_and(|e| contains_aggregate(e))
        }
        Expr::Cast { expr, .. } => contains_aggregate(expr),
        _ => false,
    }
}

/// Builds the projection expressions and output column metadata.
fn build_projection(
    select_items: &[SelectItem],
    columns: &[ColumnInfo],
    table_name: &str,
) -> ProjectionResult {
    let mut output_exprs = Vec::new();
    let mut output_columns = Vec::new();

    for item in select_items {
        match item {
            SelectItem::Wildcard => {
                // SELECT * - include all columns
                for col in columns {
                    let expr = Expr::ColumnRef {
                        table: None,
                        column: col.column_name.clone(),
                    };
                    output_exprs.push((expr, col.column_name.clone()));
                    output_columns.push(OutputColumn::new(
                        col.column_name.clone(),
                        col.type_oid,
                    ));
                }
            }
            SelectItem::QualifiedWildcard(qual_table) => {
                // SELECT table.* - include all columns from that table
                if qual_table != table_name {
                    return Err(ExecutorError::TableNotFound {
                        name: qual_table.clone(),
                    });
                }
                for col in columns {
                    let expr = Expr::ColumnRef {
                        table: Some(qual_table.clone()),
                        column: col.column_name.clone(),
                    };
                    output_exprs.push((expr, col.column_name.clone()));
                    output_columns.push(OutputColumn::new(
                        col.column_name.clone(),
                        col.type_oid,
                    ));
                }
            }
            SelectItem::Expr { expr, alias } => {
                // Determine output name: alias if provided, else derive from expression
                let name = alias.clone().unwrap_or_else(|| expr_to_name(expr));
                let type_oid = infer_type(expr, columns);
                output_exprs.push((expr.clone(), name.clone()));
                output_columns.push(OutputColumn::new(name, type_oid));
            }
        }
    }

    Ok((output_exprs, output_columns))
}

/// Derives a column name from an expression.
fn expr_to_name(expr: &Expr) -> String {
    match expr {
        Expr::ColumnRef { column, .. } => column.clone(),
        Expr::Integer(_) => "int4".to_string(),
        Expr::Float(_) => "float8".to_string(),
        Expr::String(_) => "text".to_string(),
        Expr::Boolean(_) => "bool".to_string(),
        Expr::Null => "null".to_string(),
        _ => "?column?".to_string(),
    }
}

/// Infers the type OID of an expression.
fn infer_type(expr: &Expr, columns: &[ColumnInfo]) -> i32 {
    match expr {
        Expr::ColumnRef { column, .. } => {
            // Find the column and return its type
            columns
                .iter()
                .find(|c| &c.column_name == column)
                .map(|c| c.type_oid)
                .unwrap_or(type_oid::UNKNOWN)
        }
        Expr::Null => type_oid::UNKNOWN,
        Expr::Boolean(_) => type_oid::BOOL,
        Expr::Integer(n) => {
            if *n >= i32::MIN as i64 && *n <= i32::MAX as i64 {
                type_oid::INT4
            } else {
                type_oid::INT8
            }
        }
        Expr::Float(_) => type_oid::FLOAT8,
        Expr::String(_) => type_oid::TEXT,
        Expr::BinaryOp { left, op, .. } => {
            use crate::sql::BinaryOperator::*;
            match op {
                // Comparison operators return boolean
                Eq | Neq | Lt | LtEq | Gt | GtEq | And | Or => type_oid::BOOL,
                // Arithmetic operators: use left operand's type (simplified)
                Add | Sub | Mul | Div | Mod => infer_type(left, columns),
                // Concatenation returns text
                Concat => type_oid::TEXT,
            }
        }
        Expr::UnaryOp { op, operand } => {
            use crate::sql::UnaryOperator::*;
            match op {
                Not => type_oid::BOOL,
                Minus | Plus => infer_type(operand, columns),
            }
        }
        Expr::IsNull { .. } => type_oid::BOOL,
        Expr::Between { .. } => type_oid::BOOL,
        Expr::InList { .. } => type_oid::BOOL,
        _ => type_oid::UNKNOWN,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protocol::type_oid;

    #[test]
    fn test_expr_to_name() {
        assert_eq!(
            expr_to_name(&Expr::ColumnRef {
                table: None,
                column: "id".to_string()
            }),
            "id"
        );
        assert_eq!(expr_to_name(&Expr::Integer(42)), "int4");
        assert_eq!(expr_to_name(&Expr::Float(3.14)), "float8");
        assert_eq!(
            expr_to_name(&Expr::String("hello".to_string())),
            "text"
        );
    }

    #[test]
    fn test_infer_type() {
        let columns = vec![
            ColumnInfo::new(1, 0, "id".to_string(), type_oid::INT4, 0),
            ColumnInfo::new(1, 1, "name".to_string(), type_oid::TEXT, 0),
        ];

        // Column reference
        assert_eq!(
            infer_type(
                &Expr::ColumnRef {
                    table: None,
                    column: "id".to_string()
                },
                &columns
            ),
            type_oid::INT4
        );

        // Literals
        assert_eq!(infer_type(&Expr::Integer(42), &columns), type_oid::INT4);
        assert_eq!(infer_type(&Expr::Float(3.14), &columns), type_oid::FLOAT8);
        assert_eq!(
            infer_type(&Expr::String("hi".to_string()), &columns),
            type_oid::TEXT
        );
        assert_eq!(infer_type(&Expr::Boolean(true), &columns), type_oid::BOOL);

        // Comparison returns bool
        assert_eq!(
            infer_type(
                &Expr::BinaryOp {
                    left: Box::new(Expr::Integer(1)),
                    op: crate::sql::BinaryOperator::Eq,
                    right: Box::new(Expr::Integer(2)),
                },
                &columns
            ),
            type_oid::BOOL
        );
    }

    #[test]
    fn test_build_projection_wildcard() {
        let columns = vec![
            ColumnInfo::new(1, 0, "id".to_string(), type_oid::INT4, 0),
            ColumnInfo::new(1, 1, "name".to_string(), type_oid::TEXT, 0),
        ];

        let (exprs, output_cols) =
            build_projection(&[SelectItem::Wildcard], &columns, "users").unwrap();

        assert_eq!(exprs.len(), 2);
        assert_eq!(output_cols.len(), 2);
        assert_eq!(output_cols[0].name, "id");
        assert_eq!(output_cols[0].type_oid, type_oid::INT4);
        assert_eq!(output_cols[1].name, "name");
        assert_eq!(output_cols[1].type_oid, type_oid::TEXT);
    }

    #[test]
    fn test_build_projection_expr_with_alias() {
        let columns = vec![ColumnInfo::new(
            1,
            0,
            "id".to_string(),
            type_oid::INT4,
            0,
        )];

        let (exprs, output_cols) = build_projection(
            &[SelectItem::Expr {
                expr: Expr::ColumnRef {
                    table: None,
                    column: "id".to_string(),
                },
                alias: Some("user_id".to_string()),
            }],
            &columns,
            "users",
        )
        .unwrap();

        assert_eq!(exprs.len(), 1);
        assert_eq!(output_cols[0].name, "user_id");
    }
}
