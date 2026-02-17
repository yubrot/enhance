//! Query planner.

use std::collections::HashSet;

use crate::catalog::{Catalog, ColumnInfo};
use crate::datum::Type;
use crate::sql::{
    DeleteStmt, Expr, FromClause, InsertStmt, SelectItem, SelectStmt, TableRef, UpdateStmt,
};

use super::aggregate::{AggregateFunction, AggregateOp};
use super::error::ExecutorError;
use super::expr::{BoundExpr, BoundWhenClause};
use super::plan::{DmlPlan, QueryPlan, SortItem};
use super::{ColumnDesc, ColumnSource};

/// Plans a SELECT statement into a logical [`QueryPlan`] tree.
///
/// The planner resolves table references, binds column names to positional
/// indices, and constructs Filter/Projection plan nodes. No data is loaded
/// at this stage.
///
/// # Arguments
///
/// * `select` - The parsed SELECT statement
/// * `catalog` - Catalog for table/column metadata lookups
///
/// # Errors
///
/// Returns [`ExecutorError`] for unresolvable tables/columns, unsupported
/// features (JOINs, subqueries), or catalog lookup errors.
pub fn plan_select(select: &SelectStmt, catalog: &Catalog) -> Result<QueryPlan, ExecutorError> {
    // Check for unsupported features
    if select.distinct {
        return Err(ExecutorError::Unsupported("DISTINCT".to_string()));
    }
    if select.locking.is_some() {
        return Err(ExecutorError::Unsupported("FOR UPDATE/SHARE".to_string()));
    }

    // Step 1: FROM clause -> base plan
    let mut plan = match &select.from {
        Some(from) => build_from_plan(from, catalog)?,
        None => QueryPlan::ValuesScan,
    };
    let scan_columns = plan.columns().to_vec();

    // Step 2: WHERE clause -> Filter
    // Validate: no aggregates in WHERE
    if let Some(ref where_clause) = select.where_clause
        && contains_aggregate(where_clause)
    {
        return Err(ExecutorError::AggregateNotAllowed {
            context: "WHERE clause".to_string(),
        });
    }
    plan = apply_filter(plan, select.where_clause.as_ref())?;

    // Step 3: Detect aggregation context
    // ORDER BY expressions must also be checked — `SELECT x FROM t ORDER BY COUNT(*)`
    // triggers aggregation context, leading to NonAggregatedColumn for x.
    let has_aggregation = !select.group_by.is_empty()
        || select.columns.iter().any(|item| match item {
            SelectItem::Expr { expr, .. } => contains_aggregate(expr),
            _ => false,
        })
        || select.having.as_ref().is_some_and(contains_aggregate)
        || select
            .order_by
            .iter()
            .any(|ob| contains_aggregate(&ob.expr));

    if has_aggregation {
        plan = plan_aggregation(plan, select, &scan_columns)?;
    } else {
        // No aggregation — HAVING without aggregate context is an error
        if select.having.is_some() {
            return Err(ExecutorError::Unsupported(
                "HAVING without GROUP BY or aggregates".to_string(),
            ));
        }

        // Step 4a: ORDER BY without aggregation
        plan = plan_order_by_simple(plan, select)?;

        // Step 5a: Projection
        plan = build_projection_plan(plan, &select.columns)?;
    }

    // Step 6: LIMIT/OFFSET
    plan = plan_limit_offset(plan, select)?;

    Ok(plan)
}

/// Plans the aggregation portion of a SELECT: GROUP BY binding, aggregate
/// extraction, HAVING rewrite, ORDER BY rewrite, and final Projection.
///
/// Called only when the SELECT is in an aggregation context (GROUP BY is
/// present, or SELECT/HAVING/ORDER BY contain aggregate function calls).
fn plan_aggregation(
    plan: QueryPlan,
    select: &SelectStmt,
    scan_columns: &[ColumnDesc],
) -> Result<QueryPlan, ExecutorError> {
    // 1. Bind GROUP BY expressions against scan_columns
    let mut bound_group_by = Vec::new();
    for expr in &select.group_by {
        // Validate: no aggregates in GROUP BY
        if contains_aggregate(expr) {
            return Err(ExecutorError::AggregateNotAllowed {
                context: "GROUP BY expression".to_string(),
            });
        }
        bound_group_by.push(expr.bind(scan_columns)?);
    }

    // 2. Resolve SELECT items against scan_columns
    let mut select_bound_exprs = Vec::new();
    let mut select_descs = Vec::new();
    for item in &select.columns {
        for (expr, desc) in resolve_select_item(item, scan_columns)? {
            select_bound_exprs.push(expr);
            select_descs.push(desc);
        }
    }

    // 3. Validate aggregate argument types (SUM/AVG must be numeric)
    // and no nested aggregates (aggregate within aggregate)
    for expr in &select_bound_exprs {
        validate_bound_aggregates(expr)?;
    }

    // 4. Rewrite SELECT expressions for aggregate output.
    // All aggregate extraction (SELECT, HAVING, ORDER BY) shares a single
    // aggregates Vec so duplicate aggregates reuse the same output position.
    let mut aggregates: Vec<AggregateOp> = Vec::new();
    let mut rewritten_select = Vec::new();
    for expr in select_bound_exprs {
        rewritten_select.push(rewrite_for_aggregate_output(
            expr,
            &bound_group_by,
            &mut aggregates,
        )?);
    }

    // 5. Rewrite HAVING if present (shares aggregate list with SELECT)
    let rewritten_having = if let Some(ref having_expr) = select.having {
        let bound_having = having_expr.bind(scan_columns)?;
        validate_bound_aggregates(&bound_having)?;
        Some(rewrite_for_aggregate_output(
            bound_having,
            &bound_group_by,
            &mut aggregates,
        )?)
    } else {
        None
    };

    // 6. Resolve ORDER BY expressions (shares aggregate list with SELECT/HAVING).
    // Must be resolved before building the Aggregate node because ORDER BY
    // expressions like `ORDER BY COUNT(*)` may add new aggregates.
    let sort_items = if !select.order_by.is_empty() {
        let mut items = Vec::new();
        for ob in &select.order_by {
            let sort_item = resolve_order_by_expr(ob, &rewritten_select, &select_descs, |expr| {
                let bound = expr.bind(scan_columns)?;
                validate_bound_aggregates(&bound)?;
                rewrite_for_aggregate_output(bound, &bound_group_by, &mut aggregates)
            })?;
            items.push(sort_item);
        }
        Some(items)
    } else {
        None
    };

    // 7. Build Aggregate output schema (done after ORDER BY so the schema
    // includes any aggregates added by ORDER BY expressions).
    let mut agg_columns = Vec::new();
    for (i, gb_expr) in bound_group_by.iter().enumerate() {
        if let BoundExpr::Column { index, .. } = gb_expr {
            agg_columns.push(scan_columns[*index].clone());
        } else {
            // GROUP BY expression: synthetic descriptor
            agg_columns.push(ColumnDesc {
                name: format!("group_{}", i),
                source: None,
                ty: gb_expr.ty().unwrap_or(Type::Text),
            });
        }
    }
    for op in &aggregates {
        agg_columns.push(ColumnDesc {
            name: op.to_string().to_lowercase(),
            source: None,
            ty: op.output_type(),
        });
    }

    // 8. Build Aggregate plan node
    let mut result = QueryPlan::Aggregate {
        input: Box::new(plan),
        group_by: bound_group_by,
        aggregates,
        columns: agg_columns,
    };

    // 9. Apply HAVING filter
    if let Some(having_pred) = rewritten_having {
        result = QueryPlan::Filter {
            input: Box::new(result),
            predicate: having_pred,
        };
    }

    // 10. Apply Sort if ORDER BY was present
    if let Some(items) = sort_items {
        result = QueryPlan::Sort {
            input: Box::new(result),
            items,
        };
    }

    // 11. Build Projection (update column types from rewritten expressions first)
    for (i, expr) in rewritten_select.iter().enumerate() {
        if let Some(ty) = expr.ty() {
            select_descs[i].ty = ty;
        }
    }
    result = QueryPlan::Projection {
        input: Box::new(result),
        exprs: rewritten_select,
        columns: select_descs,
    };

    Ok(result)
}

/// Plans an INSERT statement into a logical [`DmlPlan::Insert`].
///
/// Resolves column names to positions, handles SERIAL auto-population,
/// binds value expressions, and applies type coercion to match target
/// column types.
///
/// # Arguments
///
/// * `insert` - The parsed INSERT statement
/// * `catalog` - Catalog for table/column metadata lookups
///
/// # Errors
///
/// Returns [`ExecutorError`] for unknown tables/columns, column count
/// mismatches, duplicate columns, or type coercion failures.
pub fn plan_insert(insert: &InsertStmt, catalog: &Catalog) -> Result<DmlPlan, ExecutorError> {
    // Look up the target table and columns
    let entry =
        catalog
            .resolve_table(&insert.table)
            .ok_or_else(|| ExecutorError::TableNotFound {
                name: insert.table.clone(),
            })?;
    let (table_info, column_infos) = (&entry.info, entry.columns.as_slice());
    let column_count = column_infos.len();

    // Determine the column mapping: which table column each value expression maps to.
    // If no column list is specified, values map 1:1 to table columns.
    let column_mapping = if insert.columns.is_empty() {
        // No column list: values must match table column count
        (0..column_count).collect::<Vec<_>>()
    } else {
        resolve_insert_columns(&insert.columns, column_infos)?
    };

    // Identify SERIAL columns for auto-population
    let serial_columns: Vec<(usize, u32)> = column_infos
        .iter()
        .enumerate()
        .filter(|(_, col)| col.is_serial())
        .map(|(i, col)| (i, col.seq_id))
        .collect();

    // Columns explicitly provided by the user
    let provided_columns: HashSet<usize> = column_mapping.iter().copied().collect();

    // Build schema (column types) for type coercion
    let schema: Vec<Type> = column_infos.iter().map(|c| c.ty).collect();

    // Bind each row of values
    let mut bound_rows = Vec::with_capacity(insert.values.len());
    for row_exprs in &insert.values {
        if row_exprs.len() != column_mapping.len() {
            return Err(ExecutorError::ColumnCountMismatch {
                expected: column_mapping.len(),
                found: row_exprs.len(),
            });
        }

        // Start with NULL for all columns
        let mut bound_row = vec![BoundExpr::Null; column_count];

        // Fill in provided values with type coercion
        // NOTE: VALUES expressions are bound with an empty column list because
        // they cannot reference table columns. Column refs in VALUES would
        // produce ColumnNotFound. INSERT ... SELECT (which needs column
        // resolution) would require a different binding approach.
        for (expr_idx, &col_idx) in column_mapping.iter().enumerate() {
            let bound = row_exprs[expr_idx].bind(&[])?;
            let target_type = schema[col_idx];
            bound_row[col_idx] = bound.coerce(target_type);
        }

        // SERIAL columns that were not explicitly provided remain as Null —
        // the executor will call nextval for these.

        bound_rows.push(bound_row);
    }

    Ok(DmlPlan::Insert {
        table_name: insert.table.clone(),
        table_id: table_info.table_id,
        first_page: table_info.first_page,
        schema,
        values: bound_rows,
        serial_columns: serial_columns
            .into_iter()
            .filter(|(i, _)| !provided_columns.contains(i))
            .collect(),
    })
}

/// Plans an UPDATE statement into a logical [`DmlPlan::Update`].
///
/// Builds a SeqScan (with optional Filter for WHERE), resolves SET assignment
/// column names, binds value expressions against the scan schema, and applies
/// type coercion for target column types.
///
/// # Errors
///
/// Returns [`ExecutorError`] for unknown tables/columns, or expression binding
/// errors.
pub fn plan_update(update: &UpdateStmt, catalog: &Catalog) -> Result<DmlPlan, ExecutorError> {
    // Build the input scan plan
    let scan_plan = build_seq_scan_plan(&update.table, None, catalog)?;

    let input = apply_filter(scan_plan, update.where_clause.as_ref())?;

    let input_columns = input.columns().to_vec();

    // NOTE: This duplicates the table/column lookup already done inside build_seq_scan_plan.
    // With Catalog this is a cheap HashMap lookup, so no performance concern.
    let entry =
        catalog
            .resolve_table(&update.table)
            .ok_or_else(|| ExecutorError::TableNotFound {
                name: update.table.clone(),
            })?;
    let (table_info, column_infos) = (&entry.info, entry.columns.as_slice());
    let schema: Vec<Type> = column_infos.iter().map(|c| c.ty).collect();

    // Build assignments: start with identity (preserve original values)
    let mut bound_assignments: Vec<BoundExpr> = (0..column_infos.len())
        .map(|i| BoundExpr::Column {
            index: i,
            name: Some(column_infos[i].column_name.clone()),
            ty: column_infos[i].ty,
        })
        .collect();

    // Apply SET assignments
    for assignment in &update.assignments {
        let col_idx = column_infos
            .iter()
            .position(|c| c.column_name.to_lowercase() == assignment.column.to_lowercase())
            .ok_or_else(|| ExecutorError::ColumnNotFound {
                name: assignment.column.clone(),
            })?;

        let bound = assignment.value.bind(&input_columns)?;
        let target_type = schema[col_idx];
        bound_assignments[col_idx] = bound.coerce(target_type);
    }

    Ok(DmlPlan::Update {
        table_name: update.table.clone(),
        input: Box::new(input),
        assignments: bound_assignments,
        schema,
        first_page: table_info.first_page,
    })
}

/// Plans a DELETE statement into a logical [`DmlPlan::Delete`].
///
/// Builds a SeqScan (with optional Filter for WHERE) as the input plan.
///
/// # Errors
///
/// Returns [`ExecutorError`] for unknown tables or expression binding errors.
pub fn plan_delete(delete: &DeleteStmt, catalog: &Catalog) -> Result<DmlPlan, ExecutorError> {
    // Build the input scan plan
    let scan_plan = build_seq_scan_plan(&delete.table, None, catalog)?;

    let input = apply_filter(scan_plan, delete.where_clause.as_ref())?;

    Ok(DmlPlan::Delete {
        table_name: delete.table.clone(),
        input: Box::new(input),
    })
}

/// Resolves column names from an INSERT column list to table column indices.
///
/// Returns a Vec of table column indices in the order specified by the user.
/// Validates that all column names exist and no column is specified more than once.
fn resolve_insert_columns(
    column_names: &[String],
    column_infos: &[ColumnInfo],
) -> Result<Vec<usize>, ExecutorError> {
    let mut seen = HashSet::new();
    let mut mapping = Vec::with_capacity(column_names.len());

    for name in column_names {
        let lower = name.to_lowercase();
        if !seen.insert(lower.clone()) {
            return Err(ExecutorError::DuplicateColumn { name: name.clone() });
        }

        let col_idx = column_infos
            .iter()
            .position(|c| c.column_name.to_lowercase() == lower)
            .ok_or_else(|| ExecutorError::ColumnNotFound { name: name.clone() })?;

        mapping.push(col_idx);
    }

    Ok(mapping)
}

/// Wraps a plan in a [`QueryPlan::Filter`] if a WHERE predicate is present.
fn apply_filter(plan: QueryPlan, where_clause: Option<&Expr>) -> Result<QueryPlan, ExecutorError> {
    match where_clause {
        Some(expr) => {
            let columns = plan.columns().to_vec();
            let predicate = expr.bind(&columns)?;
            Ok(QueryPlan::Filter {
                input: Box::new(plan),
                predicate,
            })
        }
        None => Ok(plan),
    }
}

/// Builds a plan from a FROM clause.
fn build_from_plan(from: &FromClause, catalog: &Catalog) -> Result<QueryPlan, ExecutorError> {
    if from.tables.len() != 1 {
        return Err(ExecutorError::Unsupported(
            "multiple tables in FROM (use JOIN)".to_string(),
        ));
    }
    build_table_ref_plan(&from.tables[0], catalog)
}

/// Builds a plan from a table reference.
fn build_table_ref_plan(
    table_ref: &TableRef,
    catalog: &Catalog,
) -> Result<QueryPlan, ExecutorError> {
    match table_ref {
        TableRef::Table { name, alias } => build_seq_scan_plan(name, alias.as_deref(), catalog),
        TableRef::Join { .. } => Err(ExecutorError::Unsupported("JOIN".to_string())),
        TableRef::Subquery { .. } => {
            Err(ExecutorError::Unsupported("subquery in FROM".to_string()))
        }
    }
}

/// Builds a SeqScan plan by looking up the table in the catalog.
///
/// When `alias` is provided, it is used as the column source table name
/// so that qualified references like `t.id` resolve correctly.
///
/// NOTE: When IndexScan is introduced, this will be subsumed by a `build_scan_plan`
/// that takes WHERE predicates and selects between SeqScan and IndexScan.
fn build_seq_scan_plan(
    table_name: &str,
    alias: Option<&str>,
    catalog: &Catalog,
) -> Result<QueryPlan, ExecutorError> {
    // Look up table and columns in catalog
    let entry = catalog
        .resolve_table(table_name)
        .ok_or_else(|| ExecutorError::TableNotFound {
            name: table_name.to_string(),
        })?;
    let (table_info, column_infos) = (&entry.info, entry.columns.as_slice());

    // Build schema (column types) for record deserialization
    let schema: Vec<Type> = column_infos.iter().map(|c| c.ty).collect();

    // Build column descriptors — use alias for column resolution if provided
    let resolve_name = alias.unwrap_or(table_name);
    let columns = build_column_descs(column_infos, table_info.table_id, resolve_name);

    Ok(QueryPlan::SeqScan {
        table_name: table_name.to_string(),
        table_id: table_info.table_id,
        first_page: table_info.first_page,
        schema,
        columns,
    })
}

/// Builds column descriptors from catalog column info.
fn build_column_descs(
    column_infos: &[ColumnInfo],
    table_id: u32,
    table_name: &str,
) -> Vec<ColumnDesc> {
    column_infos
        .iter()
        .enumerate()
        .map(|(i, col)| ColumnDesc {
            name: col.column_name.clone(),
            source: Some(ColumnSource {
                table_name: table_name.to_string(),
                table_oid: table_id,
                column_id: (i + 1) as i16,
            }),
            ty: col.ty,
        })
        .collect()
}

/// Builds a Projection plan from the SELECT list.
fn build_projection_plan(
    input: QueryPlan,
    select_items: &[SelectItem],
) -> Result<QueryPlan, ExecutorError> {
    let input_columns = input.columns().to_vec();
    let mut exprs = Vec::new();
    let mut columns = Vec::new();

    for item in select_items {
        for (expr, desc) in resolve_select_item(item, &input_columns)? {
            exprs.push(expr);
            columns.push(desc);
        }
    }

    Ok(QueryPlan::Projection {
        input: Box::new(input),
        exprs,
        columns,
    })
}

/// Resolves a single [`SelectItem`] into `(BoundExpr, ColumnDesc)` pairs.
///
/// Wildcards expand to all input columns; expressions produce a single pair.
fn resolve_select_item(
    item: &SelectItem,
    input_columns: &[ColumnDesc],
) -> Result<Vec<(BoundExpr, ColumnDesc)>, ExecutorError> {
    match item {
        SelectItem::Wildcard => Ok(expand_columns(input_columns, None)),
        SelectItem::QualifiedWildcard(table_name) => {
            let expanded = expand_columns(input_columns, Some(table_name));
            if expanded.is_empty() {
                return Err(ExecutorError::TableNotFound {
                    name: table_name.clone(),
                });
            }
            Ok(expanded)
        }
        SelectItem::Expr { expr, alias } => {
            let bound = expr.bind(input_columns)?;
            let ty = bound.ty().unwrap_or(Type::Text);
            let alias_name = alias.as_deref().map(str::to_string);
            let (name, source) = match &bound {
                BoundExpr::Column { index, .. } => {
                    let ColumnDesc { name, source, .. } = &input_columns[*index];
                    (alias_name.unwrap_or_else(|| name.clone()), source.clone())
                }
                _ => (alias_name.unwrap_or_else(|| "?column?".to_string()), None),
            };
            Ok(vec![(bound, ColumnDesc { name, source, ty })])
        }
    }
}

/// Checks whether an AST [`Expr`] contains an aggregate function call.
///
/// Used to detect aggregation context and to validate that aggregates are
/// not present in forbidden positions (WHERE, GROUP BY).
/// Does not descend into subqueries, as aggregates in subqueries belong
/// to the inner context.
fn contains_aggregate(expr: &Expr) -> bool {
    match expr {
        // NOTE: Does not recurse into `args` because non-aggregate functions
        // are currently unsupported (Expr::bind returns Unsupported). If
        // scalar functions are added, this must recurse into args.
        Expr::Function { name, .. } => AggregateFunction::from_name(name).is_some(),
        Expr::BinaryOp { left, right, .. } => contains_aggregate(left) || contains_aggregate(right),
        Expr::UnaryOp { operand, .. } => contains_aggregate(operand),
        Expr::IsNull { expr, .. } => contains_aggregate(expr),
        Expr::InList { expr, list, .. } => {
            contains_aggregate(expr) || list.iter().any(contains_aggregate)
        }
        Expr::Between {
            expr, low, high, ..
        } => contains_aggregate(expr) || contains_aggregate(low) || contains_aggregate(high),
        Expr::Like {
            expr,
            pattern,
            escape,
            ..
        } => {
            contains_aggregate(expr)
                || contains_aggregate(pattern)
                || escape.as_deref().is_some_and(contains_aggregate)
        }
        Expr::Case {
            operand,
            when_clauses,
            else_result,
        } => {
            operand.as_deref().is_some_and(contains_aggregate)
                || when_clauses
                    .iter()
                    .any(|wc| contains_aggregate(&wc.condition) || contains_aggregate(&wc.result))
                || else_result.as_deref().is_some_and(contains_aggregate)
        }
        Expr::Cast { expr, .. } => contains_aggregate(expr),
        // Leaf nodes and subqueries — no aggregate in this context
        Expr::Null
        | Expr::Boolean(_)
        | Expr::Integer(_)
        | Expr::Float(_)
        | Expr::String(_)
        | Expr::ColumnRef { .. }
        | Expr::Parameter(_)
        | Expr::InSubquery { .. }
        | Expr::Exists { .. }
        | Expr::Subquery(_) => false,
    }
}

/// Validates aggregate function arguments within a [`BoundExpr`] tree.
///
/// Checks two invariants:
/// - **No nested aggregates**: `COUNT(SUM(x))` is an error
/// - **SUM/AVG arguments must be numeric**: `SUM(text_column)` is an error
fn validate_bound_aggregates(expr: &BoundExpr) -> Result<(), ExecutorError> {
    match expr {
        BoundExpr::AggregateCall { func, args, .. } => {
            // Check for nested aggregates
            for arg in args {
                if bound_contains_aggregate(arg) {
                    return Err(ExecutorError::AggregateNotAllowed {
                        context: "aggregate function call".to_string(),
                    });
                }
            }
            // Check SUM/AVG argument types
            if matches!(func, AggregateFunction::Sum | AggregateFunction::Avg)
                && let Some(arg) = args.first()
                && let Some(ty) = arg.ty()
                && ty.to_wide_numeric().is_none()
            {
                return Err(ExecutorError::TypeMismatch {
                    expected: "numeric".to_string(),
                    found: Some(ty),
                });
            }
            Ok(())
        }
        BoundExpr::BinaryOp { left, right, .. } => {
            validate_bound_aggregates(left)?;
            validate_bound_aggregates(right)
        }
        BoundExpr::UnaryOp { operand, .. } => validate_bound_aggregates(operand),
        BoundExpr::IsNull { expr, .. } => validate_bound_aggregates(expr),
        BoundExpr::InList { expr, list, .. } => {
            validate_bound_aggregates(expr)?;
            for e in list {
                validate_bound_aggregates(e)?;
            }
            Ok(())
        }
        BoundExpr::Between {
            expr, low, high, ..
        } => {
            validate_bound_aggregates(expr)?;
            validate_bound_aggregates(low)?;
            validate_bound_aggregates(high)
        }
        BoundExpr::Like {
            expr,
            pattern,
            escape,
            ..
        } => {
            validate_bound_aggregates(expr)?;
            validate_bound_aggregates(pattern)?;
            if let Some(e) = escape {
                validate_bound_aggregates(e)?;
            }
            Ok(())
        }
        BoundExpr::Case {
            operand,
            when_clauses,
            else_result,
        } => {
            if let Some(op) = operand {
                validate_bound_aggregates(op)?;
            }
            for wc in when_clauses {
                validate_bound_aggregates(&wc.condition)?;
                validate_bound_aggregates(&wc.result)?;
            }
            if let Some(e) = else_result {
                validate_bound_aggregates(e)?;
            }
            Ok(())
        }
        BoundExpr::Cast { expr, .. } => validate_bound_aggregates(expr),
        _ => Ok(()),
    }
}

/// Returns `true` if a [`BoundExpr`] tree contains an [`BoundExpr::AggregateCall`].
fn bound_contains_aggregate(expr: &BoundExpr) -> bool {
    match expr {
        BoundExpr::AggregateCall { .. } => true,
        BoundExpr::BinaryOp { left, right, .. } => {
            bound_contains_aggregate(left) || bound_contains_aggregate(right)
        }
        BoundExpr::UnaryOp { operand, .. } => bound_contains_aggregate(operand),
        BoundExpr::IsNull { expr, .. } => bound_contains_aggregate(expr),
        BoundExpr::InList { expr, list, .. } => {
            bound_contains_aggregate(expr) || list.iter().any(bound_contains_aggregate)
        }
        BoundExpr::Between {
            expr, low, high, ..
        } => {
            bound_contains_aggregate(expr)
                || bound_contains_aggregate(low)
                || bound_contains_aggregate(high)
        }
        BoundExpr::Like {
            expr,
            pattern,
            escape,
            ..
        } => {
            bound_contains_aggregate(expr)
                || bound_contains_aggregate(pattern)
                || escape.as_deref().is_some_and(bound_contains_aggregate)
        }
        BoundExpr::Case {
            operand,
            when_clauses,
            else_result,
        } => {
            operand.as_deref().is_some_and(bound_contains_aggregate)
                || when_clauses.iter().any(|wc| {
                    bound_contains_aggregate(&wc.condition) || bound_contains_aggregate(&wc.result)
                })
                || else_result.as_deref().is_some_and(bound_contains_aggregate)
        }
        BoundExpr::Cast { expr, .. } => bound_contains_aggregate(expr),
        _ => false,
    }
}

/// Rewrites a [`BoundExpr`] for use on top of an Aggregate node's output.
///
/// Four rewrite rules applied in order:
///
/// 1. **`AggregateCall` extraction**: Moves the aggregate operation into the
///    shared `aggregates` list (deduplicating via `PartialEq`) and replaces
///    the call with a `Column` reference pointing to the aggregate's output
///    position (`group_by.len() + agg_index`).
///
/// 2. **GROUP BY match**: If the entire expression structurally matches a
///    GROUP BY expression (via `PartialEq`), it is replaced with a `Column`
///    reference pointing to the matching group key position.
///
/// 3. **Leaf handling**: Literal constants pass through unchanged. Unresolved
///    `Column` references that don't match any GROUP BY key produce
///    [`ExecutorError::NonAggregatedColumn`].
///
/// 4. **Composite expressions**: Recursed into child nodes.
fn rewrite_for_aggregate_output(
    expr: BoundExpr,
    group_by: &[BoundExpr],
    aggregates: &mut Vec<AggregateOp>,
) -> Result<BoundExpr, ExecutorError> {
    // Rule 1: Extract AggregateCall
    if let BoundExpr::AggregateCall {
        func,
        args,
        distinct,
    } = &expr
    {
        let op = AggregateOp {
            func: *func,
            args: args.clone(),
            distinct: *distinct,
        };
        // Dedup: reuse existing position if an identical aggregate exists
        let output_ty = op.output_type();
        let agg_idx = if let Some(pos) = aggregates.iter().position(|a| a == &op) {
            pos
        } else {
            aggregates.push(op);
            aggregates.len() - 1
        };
        let output_idx = group_by.len() + agg_idx;
        return Ok(BoundExpr::Column {
            index: output_idx,
            name: None,
            ty: output_ty,
        });
    }

    // Rule 2: Whole-expression GROUP BY match
    for (i, gb) in group_by.iter().enumerate() {
        if &expr == gb {
            let ty = expr.ty().unwrap_or(Type::Text);
            return Ok(BoundExpr::Column {
                index: i,
                name: None,
                ty,
            });
        }
    }

    // Rule 3: Leaf handling
    match &expr {
        BoundExpr::Column { name, .. } => {
            return Err(ExecutorError::NonAggregatedColumn {
                name: name.as_deref().unwrap_or("?column?").to_string(),
            });
        }
        BoundExpr::Null
        | BoundExpr::Boolean(_)
        | BoundExpr::Integer(_)
        | BoundExpr::Float(_)
        | BoundExpr::String(_) => {
            return Ok(expr);
        }
        _ => {}
    }

    // Rule 4: Composite expressions — recurse into children
    match expr {
        BoundExpr::BinaryOp { left, op, right } => Ok(BoundExpr::BinaryOp {
            left: Box::new(rewrite_for_aggregate_output(*left, group_by, aggregates)?),
            op,
            right: Box::new(rewrite_for_aggregate_output(*right, group_by, aggregates)?),
        }),
        BoundExpr::UnaryOp { op, operand } => Ok(BoundExpr::UnaryOp {
            op,
            operand: Box::new(rewrite_for_aggregate_output(
                *operand, group_by, aggregates,
            )?),
        }),
        BoundExpr::IsNull { expr, negated } => Ok(BoundExpr::IsNull {
            expr: Box::new(rewrite_for_aggregate_output(*expr, group_by, aggregates)?),
            negated,
        }),
        BoundExpr::InList {
            expr,
            list,
            negated,
        } => {
            let rewritten_list = list
                .into_iter()
                .map(|e| rewrite_for_aggregate_output(e, group_by, aggregates))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(BoundExpr::InList {
                expr: Box::new(rewrite_for_aggregate_output(*expr, group_by, aggregates)?),
                list: rewritten_list,
                negated,
            })
        }
        BoundExpr::Between {
            expr,
            low,
            high,
            negated,
        } => Ok(BoundExpr::Between {
            expr: Box::new(rewrite_for_aggregate_output(*expr, group_by, aggregates)?),
            low: Box::new(rewrite_for_aggregate_output(*low, group_by, aggregates)?),
            high: Box::new(rewrite_for_aggregate_output(*high, group_by, aggregates)?),
            negated,
        }),
        BoundExpr::Like {
            expr,
            pattern,
            escape,
            negated,
            case_insensitive,
        } => Ok(BoundExpr::Like {
            expr: Box::new(rewrite_for_aggregate_output(*expr, group_by, aggregates)?),
            pattern: Box::new(rewrite_for_aggregate_output(
                *pattern, group_by, aggregates,
            )?),
            escape: escape
                .map(|e| rewrite_for_aggregate_output(*e, group_by, aggregates).map(Box::new))
                .transpose()?,
            negated,
            case_insensitive,
        }),
        BoundExpr::Case {
            operand,
            when_clauses,
            else_result,
        } => {
            let rewritten_operand = operand
                .map(|op| rewrite_for_aggregate_output(*op, group_by, aggregates).map(Box::new))
                .transpose()?;
            let rewritten_whens = when_clauses
                .into_iter()
                .map(|wc| {
                    Ok(BoundWhenClause {
                        condition: rewrite_for_aggregate_output(
                            wc.condition,
                            group_by,
                            aggregates,
                        )?,
                        result: rewrite_for_aggregate_output(wc.result, group_by, aggregates)?,
                    })
                })
                .collect::<Result<Vec<_>, ExecutorError>>()?;
            let rewritten_else = else_result
                .map(|e| rewrite_for_aggregate_output(*e, group_by, aggregates).map(Box::new))
                .transpose()?;
            Ok(BoundExpr::Case {
                operand: rewritten_operand,
                when_clauses: rewritten_whens,
                else_result: rewritten_else,
            })
        }
        BoundExpr::Cast { expr, ty } => Ok(BoundExpr::Cast {
            expr: Box::new(rewrite_for_aggregate_output(*expr, group_by, aggregates)?),
            ty,
        }),
        // Already handled above: Null, Boolean, Integer, Float, String, Column, AggregateCall
        _ => unreachable!(),
    }
}

/// Resolves a single ORDER BY expression into a [`SortItem`].
///
/// Resolution follows three cases in order:
///
/// **Case A**: Integer literal N → positional reference (1-indexed).
/// Uses the already-rewritten SELECT expression at position N-1.
///
/// **Case B**: Simple column name matching a SELECT output name (including aliases).
/// Uses the already-rewritten SELECT expression for that output column.
///
/// **Case C**: No positional/alias match.
/// Calls `fallback_bind` to bind and (optionally) rewrite the expression.
fn resolve_order_by_expr(
    ob: &crate::sql::OrderByItem,
    rewritten_select: &[BoundExpr],
    select_descs: &[ColumnDesc],
    mut fallback_bind: impl FnMut(&Expr) -> Result<BoundExpr, ExecutorError>,
) -> Result<SortItem, ExecutorError> {
    let sort_expr = match &ob.expr {
        // Case A: Positional reference (e.g., ORDER BY 1)
        Expr::Integer(n) => {
            let pos = *n;
            if pos < 1 || pos as usize > rewritten_select.len() {
                return Err(ExecutorError::Unsupported(format!(
                    "ORDER BY position {} is not in select list (1..{})",
                    pos,
                    rewritten_select.len()
                )));
            }
            rewritten_select[(pos - 1) as usize].clone()
        }

        // Case B: Simple column name matching a SELECT output name (including aliases)
        Expr::ColumnRef {
            table: None,
            column,
        } => {
            if let Some(pos) = select_descs
                .iter()
                .position(|d| d.name.eq_ignore_ascii_case(column))
            {
                rewritten_select[pos].clone()
            } else {
                // Not an alias — fall through to Case C
                fallback_bind(&ob.expr)?
            }
        }

        // Case C: Arbitrary expression
        _ => fallback_bind(&ob.expr)?,
    };

    Ok(SortItem {
        expr: sort_expr,
        direction: ob.direction,
        nulls: ob.nulls,
    })
}

/// Plans ORDER BY for non-aggregation queries.
///
/// Inserts a Sort node between the current plan (after Filter, before Projection).
/// ORDER BY expressions are resolved via alias, positional, or scan-schema binding.
fn plan_order_by_simple(plan: QueryPlan, select: &SelectStmt) -> Result<QueryPlan, ExecutorError> {
    if select.order_by.is_empty() {
        return Ok(plan);
    }

    let input_columns = plan.columns().to_vec();

    // Pre-compute SELECT aliases and bound expressions for alias/positional resolution
    let mut select_bound_exprs = Vec::new();
    let mut select_descs = Vec::new();
    for item in &select.columns {
        for (expr, desc) in resolve_select_item(item, &input_columns)? {
            select_bound_exprs.push(expr);
            select_descs.push(desc);
        }
    }

    let mut sort_items = Vec::new();
    for ob in &select.order_by {
        let sort_item = resolve_order_by_expr(ob, &select_bound_exprs, &select_descs, |expr| {
            // Case C: Bind against the scan schema (pre-Projection)
            expr.bind(&input_columns)
        })?;
        sort_items.push(sort_item);
    }

    Ok(QueryPlan::Sort {
        input: Box::new(plan),
        items: sort_items,
    })
}

/// Plans LIMIT/OFFSET into a [`QueryPlan::Limit`] node.
///
/// Binds limit/offset as constant expressions (no column references allowed),
/// evaluates them at planning time, validates type (integer) and sign
/// (non-negative), and converts to u64.
fn plan_limit_offset(plan: QueryPlan, select: &SelectStmt) -> Result<QueryPlan, ExecutorError> {
    if select.limit.is_none() && select.offset.is_none() {
        return Ok(plan);
    }

    let limit = if let Some(ref limit_expr) = select.limit {
        Some(eval_constant_u64(limit_expr, "LIMIT")?)
    } else {
        None
    };

    let offset = if let Some(ref offset_expr) = select.offset {
        eval_constant_u64(offset_expr, "OFFSET")?
    } else {
        0
    };

    // Skip creating a Limit node if it would be a no-op (no limit, zero offset)
    if limit.is_none() && offset == 0 {
        return Ok(plan);
    }

    Ok(QueryPlan::Limit {
        input: Box::new(plan),
        limit,
        offset,
    })
}

/// Evaluates a constant expression to a non-negative u64.
///
/// Used for LIMIT/OFFSET where the value must be an integer literal
/// or constant expression. Column references are not allowed.
fn eval_constant_u64(expr: &Expr, context: &str) -> Result<u64, ExecutorError> {
    use crate::datum::Value;
    use crate::heap::Record;

    // Bind with empty column list — column refs are not allowed
    let bound = expr.bind(&[])?;
    let empty_record = Record::new(vec![]);
    let value = bound.evaluate(&empty_record)?;

    match value {
        Value::Smallint(n) => {
            if n < 0 {
                Err(ExecutorError::Unsupported(format!("negative {}", context)))
            } else {
                Ok(n as u64)
            }
        }
        Value::Integer(n) => {
            if n < 0 {
                Err(ExecutorError::Unsupported(format!("negative {}", context)))
            } else {
                Ok(n as u64)
            }
        }
        Value::Bigint(n) => {
            if n < 0 {
                Err(ExecutorError::Unsupported(format!("negative {}", context)))
            } else {
                Ok(n as u64)
            }
        }
        _ => Err(ExecutorError::TypeMismatch {
            expected: "integer".to_string(),
            found: value.ty(),
        }),
    }
}

/// Expands input columns into `(BoundExpr::Column, ColumnDesc)` pairs.
///
/// When `table_name` is `Some`, only columns whose source table matches are
/// included. When `None`, all columns are expanded. The `BoundExpr::Column`
/// index always refers to the position in the full input schema so that
/// downstream evaluation resolves correctly.
fn expand_columns(
    input_columns: &[ColumnDesc],
    table_name: Option<&str>,
) -> Vec<(BoundExpr, ColumnDesc)> {
    input_columns
        .iter()
        .enumerate()
        .filter(|(_, col)| match table_name {
            Some(name) => col.source.as_ref().is_some_and(|s| s.table_name == name),
            None => true,
        })
        .map(|(i, col)| {
            let expr = BoundExpr::Column {
                index: i,
                name: Some(col.name.clone()),
                ty: col.ty,
            };
            (expr, col.clone())
        })
        .collect()
}

#[cfg(test)]
mod tests {
    //! NOTE: This module depends on `crate::engine` (a higher layer) for test
    //! setup. Constructing a `Catalog` requires a running engine with
    //! bootstrapped system tables, which is prohibitively verbose to set up by
    //! hand, so we use `Engine` helpers as a pragmatic exception to the normal
    //! layering direction.

    use std::sync::Arc;

    use super::*;
    use crate::catalog::Catalog;
    use crate::engine::tests::open_test_engine;
    use crate::sql::tests::{parse_delete, parse_insert, parse_select, parse_update};
    use crate::tx::CommandId;

    async fn setup_catalog() -> Arc<Catalog> {
        let db = open_test_engine().await;
        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        db.catalog(&snapshot).await.unwrap()
    }

    /// Sets up a catalog with a user-defined table.
    async fn setup_catalog_with_table(ddl: &str) -> Arc<Catalog> {
        let db = open_test_engine().await;
        db.create_test_table(ddl).await;

        let txid = db.tx_manager().begin();
        let snapshot = db.tx_manager().snapshot(txid, CommandId::FIRST);
        db.catalog(&snapshot).await.unwrap()
    }

    #[tokio::test]
    async fn test_plan_select_from_sys_tables() {
        let catalog = setup_catalog().await;
        let select = parse_select("SELECT * FROM sys_tables");

        let plan = plan_select(&select, &catalog).unwrap();

        assert_eq!(plan.columns().len(), 3);
        assert_eq!(plan.columns()[0].name, "table_id");
        assert_eq!(plan.columns()[1].name, "table_name");
        assert_eq!(plan.columns()[2].name, "first_page");
    }

    #[tokio::test]
    async fn test_plan_select_no_from() {
        let catalog = setup_catalog().await;
        let select = parse_select("SELECT 42");

        let plan = plan_select(&select, &catalog).unwrap();

        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].name, "?column?");
    }

    #[tokio::test]
    async fn test_plan_select_table_not_found() {
        let catalog = setup_catalog().await;
        let select = parse_select("SELECT * FROM nonexistent");

        let result = plan_select(&select, &catalog);
        assert!(matches!(result, Err(ExecutorError::TableNotFound { .. })));
    }

    #[tokio::test]
    async fn test_plan_select_with_where() {
        let catalog = setup_catalog().await;
        let select = parse_select("SELECT table_name FROM sys_tables WHERE table_id = 1");

        let plan = plan_select(&select, &catalog).unwrap();

        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].name, "table_name");
        let source = plan.columns()[0]
            .source
            .as_ref()
            .expect("should have source");
        assert_eq!(source.table_name, "sys_tables");
        assert_ne!(source.table_oid, 0);
        assert_ne!(source.column_id, 0);
    }

    #[tokio::test]
    async fn test_plan_select_expr_has_no_table_metadata() {
        let catalog = setup_catalog().await;
        let select = parse_select("SELECT 1 + table_id FROM sys_tables");

        let plan = plan_select(&select, &catalog).unwrap();

        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].name, "?column?");
        assert!(plan.columns()[0].source.is_none());
    }

    #[tokio::test]
    async fn test_plan_select_qualified_column_ref() {
        let catalog = setup_catalog().await;
        let select = parse_select("SELECT sys_tables.table_name FROM sys_tables");

        let plan = plan_select(&select, &catalog).unwrap();

        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].name, "table_name");
        let source = plan.columns()[0]
            .source
            .as_ref()
            .expect("should have source");
        assert_eq!(source.table_name, "sys_tables");
        assert_ne!(source.table_oid, 0);
        assert_ne!(source.column_id, 0);
    }

    #[tokio::test]
    async fn test_plan_select_qualified_wildcard() {
        let catalog = setup_catalog().await;
        let select = parse_select("SELECT sys_tables.* FROM sys_tables");

        let plan = plan_select(&select, &catalog).unwrap();

        assert_eq!(plan.columns().len(), 3);
        assert_eq!(plan.columns()[0].name, "table_id");
        assert_eq!(plan.columns()[1].name, "table_name");
        assert_eq!(plan.columns()[2].name, "first_page");
    }

    #[tokio::test]
    async fn test_plan_select_qualified_wildcard_wrong_table() {
        let catalog = setup_catalog().await;
        let select = parse_select("SELECT nonexistent.* FROM sys_tables");

        let result = plan_select(&select, &catalog);
        assert!(matches!(result, Err(ExecutorError::TableNotFound { .. })));
    }

    #[tokio::test]
    async fn test_plan_select_with_table_alias() {
        let catalog = setup_catalog().await;
        let select = parse_select("SELECT t.table_name FROM sys_tables AS t");

        let plan = plan_select(&select, &catalog).unwrap();

        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].name, "table_name");
        let source = plan.columns()[0]
            .source
            .as_ref()
            .expect("should have source");
        assert_eq!(source.table_name, "t");
    }

    #[tokio::test]
    async fn test_plan_select_alias_hides_original_name() {
        let catalog = setup_catalog().await;
        let select = parse_select("SELECT sys_tables.table_name FROM sys_tables AS t");

        let result = plan_select(&select, &catalog);
        assert!(matches!(result, Err(ExecutorError::ColumnNotFound { .. })));
    }

    #[tokio::test]
    async fn test_infer_data_type_literals() {
        let catalog = setup_catalog().await;

        // Integer literal → bigint
        let select = parse_select("SELECT 42");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bigint);

        // Float literal → Double
        let select = parse_select("SELECT 3.14");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Double);

        // Boolean literal → Bool
        let select = parse_select("SELECT TRUE");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bool);

        // String literal → Text
        let select = parse_select("SELECT 'hello'");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Text);

        // NULL → Text (fallback)
        let select = parse_select("SELECT NULL");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Text);
    }

    #[tokio::test]
    async fn test_infer_data_type_operators() {
        let catalog = setup_catalog().await;

        // Comparison → Bool
        let select = parse_select("SELECT 1 = 1");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bool);

        // Arithmetic (int + int) → Bigint
        let select = parse_select("SELECT 1 + 2");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bigint);

        // Arithmetic (int + float) → Double via numeric promotion
        let select = parse_select("SELECT 1 + 2.5");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Double);

        // Arithmetic (float + int) → Double via numeric promotion
        let select = parse_select("SELECT 2.5 + 1");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Double);

        // Arithmetic (float + float) → Double
        let select = parse_select("SELECT 1.0 * 2.5");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Double);

        // Concatenation → Text
        let select = parse_select("SELECT 'a' || 'b'");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Text);

        // IS NULL → Bool
        let select = parse_select("SELECT 1 IS NULL");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bool);

        // IN list → Bool
        let select = parse_select("SELECT 1 IN (1, 2)");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bool);

        // BETWEEN → Bool
        let select = parse_select("SELECT 1 BETWEEN 0 AND 2");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bool);

        // LIKE → Bool
        let select = parse_select("SELECT 'a' LIKE '%'");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bool);

        // CAST → target type
        let select = parse_select("SELECT CAST(1 AS TEXT)");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Text);

        // Unary minus → inherits operand type
        let select = parse_select("SELECT -42");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Bigint);
    }

    #[tokio::test]
    async fn test_infer_data_type_column_ref() {
        let catalog = setup_catalog().await;

        // Column reference preserves source type
        let select = parse_select("SELECT table_id FROM sys_tables");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Integer);

        let select = parse_select("SELECT table_name FROM sys_tables");
        let plan = plan_select(&select, &catalog).unwrap();
        assert_eq!(plan.columns()[0].ty, Type::Text);
    }

    #[tokio::test]
    async fn test_plan_select_alias_qualified_wildcard() {
        let catalog = setup_catalog().await;
        let select = parse_select("SELECT t.* FROM sys_tables AS t");

        let plan = plan_select(&select, &catalog).unwrap();

        assert_eq!(plan.columns().len(), 3);
        assert_eq!(plan.columns()[0].name, "table_id");
    }

    // --- INSERT planner tests ---

    #[tokio::test]
    async fn test_plan_insert_basic() {
        let catalog = setup_catalog_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let insert = parse_insert("INSERT INTO users VALUES (1, 'Alice')");

        let plan = plan_insert(&insert, &catalog).unwrap();

        let DmlPlan::Insert {
            table_name,
            values,
            schema,
            serial_columns,
            ..
        } = &plan
        else {
            panic!("expected DmlPlan::Insert");
        };
        assert_eq!(table_name, "users");
        assert_eq!(values.len(), 1);
        assert_eq!(values[0].len(), 2);
        assert_eq!(schema, &[Type::Integer, Type::Text]);
        assert!(serial_columns.is_empty());
    }

    #[tokio::test]
    async fn test_plan_insert_with_column_list() {
        let catalog = setup_catalog_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let insert = parse_insert("INSERT INTO users (name, id) VALUES ('Bob', 2)");

        let plan = plan_insert(&insert, &catalog).unwrap();

        let DmlPlan::Insert { values, schema, .. } = &plan else {
            panic!("expected DmlPlan::Insert");
        };
        assert_eq!(schema.len(), 2);
        assert_eq!(values.len(), 1);
        // Value at index 0 (id) should be integer 2 cast to Integer
        // (Bigint literal → Integer column)
        let BoundExpr::Cast { ty, .. } = &values[0][0] else {
            panic!("expected Cast for id column, got {:?}", &values[0][0]);
        };
        assert_eq!(*ty, Type::Integer);
        // Value at index 1 (name) should be the string 'Bob' (no cast needed, Text→Text)
        assert!(matches!(&values[0][1], BoundExpr::String(s) if s == "Bob"));
    }

    #[tokio::test]
    async fn test_plan_insert_fewer_columns() {
        let catalog = setup_catalog_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        // Only specify id, name should default to NULL
        let insert = parse_insert("INSERT INTO users (id) VALUES (1)");

        let plan = plan_insert(&insert, &catalog).unwrap();

        let DmlPlan::Insert { values, .. } = &plan else {
            panic!("expected DmlPlan::Insert");
        };
        assert_eq!(values[0].len(), 2);
        // name column (index 1) should be NULL
        assert!(matches!(&values[0][1], BoundExpr::Null));
    }

    #[tokio::test]
    async fn test_plan_insert_serial_auto_populate() {
        let catalog = setup_catalog_with_table("CREATE TABLE users (id SERIAL, name TEXT)").await;
        // Don't specify id — should be auto-populated
        let insert = parse_insert("INSERT INTO users (name) VALUES ('Alice')");

        let plan = plan_insert(&insert, &catalog).unwrap();

        let DmlPlan::Insert {
            serial_columns,
            values,
            ..
        } = &plan
        else {
            panic!("expected DmlPlan::Insert");
        };
        // SERIAL column should be in the auto-populate list
        assert_eq!(serial_columns.len(), 1);
        assert_eq!(serial_columns[0].0, 0); // column index 0 (id)
        assert!(serial_columns[0].1 > 0); // non-zero seq_id
        // id column should be NULL (to be replaced by nextval at execution)
        assert!(matches!(&values[0][0], BoundExpr::Null));
    }

    #[tokio::test]
    async fn test_plan_insert_serial_explicit_value() {
        let catalog = setup_catalog_with_table("CREATE TABLE users (id SERIAL, name TEXT)").await;
        // Explicitly provide id — should NOT auto-populate
        let insert = parse_insert("INSERT INTO users (id, name) VALUES (99, 'Bob')");

        let plan = plan_insert(&insert, &catalog).unwrap();

        let DmlPlan::Insert { serial_columns, .. } = &plan else {
            panic!("expected DmlPlan::Insert");
        };
        // SERIAL column explicitly provided → not in auto-populate list
        assert!(serial_columns.is_empty());
    }

    #[tokio::test]
    async fn test_plan_insert_column_count_mismatch() {
        let catalog = setup_catalog_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        // 3 values but only 2 columns
        let insert = parse_insert("INSERT INTO users VALUES (1, 'Alice', 'extra')");

        let result = plan_insert(&insert, &catalog);
        assert!(matches!(
            result,
            Err(ExecutorError::ColumnCountMismatch {
                expected: 2,
                found: 3
            })
        ));
    }

    #[tokio::test]
    async fn test_plan_insert_duplicate_column() {
        let catalog = setup_catalog_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let insert = parse_insert("INSERT INTO users (id, id) VALUES (1, 2)");

        let result = plan_insert(&insert, &catalog);
        assert!(matches!(result, Err(ExecutorError::DuplicateColumn { .. })));
    }

    #[tokio::test]
    async fn test_plan_insert_column_not_found() {
        let catalog = setup_catalog_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let insert = parse_insert("INSERT INTO users (id, nonexistent) VALUES (1, 'x')");

        let result = plan_insert(&insert, &catalog);
        assert!(matches!(result, Err(ExecutorError::ColumnNotFound { .. })));
    }

    #[tokio::test]
    async fn test_plan_insert_table_not_found() {
        let catalog = setup_catalog().await;
        let insert = parse_insert("INSERT INTO nonexistent VALUES (1)");

        let result = plan_insert(&insert, &catalog);
        assert!(matches!(result, Err(ExecutorError::TableNotFound { .. })));
    }

    #[tokio::test]
    async fn test_plan_insert_type_coercion() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (val SMALLINT)").await;
        // Integer literal 42 (Bigint) → should be coerced to Smallint
        let insert = parse_insert("INSERT INTO t VALUES (42)");

        let plan = plan_insert(&insert, &catalog).unwrap();

        let DmlPlan::Insert { values, .. } = &plan else {
            panic!("expected DmlPlan::Insert");
        };
        // Should have a Cast wrapping the integer literal
        let BoundExpr::Cast { ty, .. } = &values[0][0] else {
            panic!(
                "expected Cast expression for type coercion, got {:?}",
                &values[0][0]
            );
        };
        assert_eq!(*ty, Type::Smallint);
    }

    #[tokio::test]
    async fn test_plan_insert_multi_row() {
        let catalog = setup_catalog_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let insert =
            parse_insert("INSERT INTO users VALUES (1, 'Alice'), (2, 'Bob'), (3, 'Carol')");

        let plan = plan_insert(&insert, &catalog).unwrap();

        let DmlPlan::Insert { values, .. } = &plan else {
            panic!("expected DmlPlan::Insert");
        };
        assert_eq!(values.len(), 3);
    }

    #[tokio::test]
    async fn test_plan_insert_null_no_cast() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (val INTEGER)").await;
        // NULL should pass through without a Cast wrapper
        let insert = parse_insert("INSERT INTO t VALUES (NULL)");

        let plan = plan_insert(&insert, &catalog).unwrap();

        let DmlPlan::Insert { values, .. } = &plan else {
            panic!("expected DmlPlan::Insert");
        };
        assert!(matches!(&values[0][0], BoundExpr::Null));
    }

    #[tokio::test]
    async fn test_plan_insert_explain() {
        let catalog = setup_catalog_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let insert = parse_insert("INSERT INTO users VALUES (1, 'Alice'), (2, 'Bob')");

        let plan = plan_insert(&insert, &catalog).unwrap();
        assert_eq!(plan.explain(), "Insert on users (2 rows)");
    }

    // --- UPDATE planner tests ---

    #[tokio::test]
    async fn test_plan_update_basic() {
        let catalog = setup_catalog_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let update = parse_update("UPDATE users SET name = 'Bob'");

        let plan = plan_update(&update, &catalog).unwrap();

        let DmlPlan::Update {
            table_name,
            schema,
            assignments,
            ..
        } = &plan
        else {
            panic!("expected DmlPlan::Update");
        };
        assert_eq!(table_name, "users");
        assert_eq!(schema, &[Type::Integer, Type::Text]);
        assert_eq!(assignments.len(), 2);
        // id should be identity (Column { index: 0 })
        assert!(matches!(
            &assignments[0],
            BoundExpr::Column { index: 0, .. }
        ));
        // name should be the string literal 'Bob'
        assert!(matches!(&assignments[1], BoundExpr::String(s) if s == "Bob"));
    }

    #[tokio::test]
    async fn test_plan_update_with_where() {
        let catalog = setup_catalog_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let update = parse_update("UPDATE users SET name = 'Bob' WHERE id = 1");

        let plan = plan_update(&update, &catalog).unwrap();

        let DmlPlan::Update { input, .. } = &plan else {
            panic!("expected DmlPlan::Update");
        };
        // Input should be a Filter wrapping a SeqScan
        assert!(matches!(input.as_ref(), QueryPlan::Filter { .. }));
        assert_eq!(
            plan.explain(),
            "Update on users\n  Filter: ($col0 (users.id) = 1)\n    SeqScan on users (cols: id, name)"
        );
    }

    #[tokio::test]
    async fn test_plan_update_type_coercion() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (val SMALLINT)").await;
        // Integer literal 42 (Bigint) → should be coerced to Smallint
        let update = parse_update("UPDATE t SET val = 42");

        let plan = plan_update(&update, &catalog).unwrap();

        let DmlPlan::Update { assignments, .. } = &plan else {
            panic!("expected DmlPlan::Update");
        };
        let BoundExpr::Cast { ty, .. } = &assignments[0] else {
            panic!("expected Cast for type coercion, got {:?}", &assignments[0]);
        };
        assert_eq!(*ty, Type::Smallint);
    }

    #[tokio::test]
    async fn test_plan_update_referencing_column() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE counters (id INTEGER, count INTEGER)").await;
        // SET count = count + 1 — references existing column
        let update = parse_update("UPDATE counters SET count = count + 1");

        let plan = plan_update(&update, &catalog).unwrap();

        let DmlPlan::Update { assignments, .. } = &plan else {
            panic!("expected DmlPlan::Update");
        };
        // id should be identity
        assert!(matches!(
            &assignments[0],
            BoundExpr::Column { index: 0, .. }
        ));
        // count should be a Cast(BinaryOp(Column + Integer)) since count+1 infers as Bigint
        // and target is Integer
        assert!(matches!(&assignments[1], BoundExpr::Cast { .. }));
    }

    #[tokio::test]
    async fn test_plan_update_column_not_found() {
        let catalog = setup_catalog_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let update = parse_update("UPDATE users SET nonexistent = 1");

        let result = plan_update(&update, &catalog);
        assert!(matches!(result, Err(ExecutorError::ColumnNotFound { .. })));
    }

    #[tokio::test]
    async fn test_plan_update_table_not_found() {
        let catalog = setup_catalog().await;
        let update = parse_update("UPDATE nonexistent SET x = 1");

        let result = plan_update(&update, &catalog);
        assert!(matches!(result, Err(ExecutorError::TableNotFound { .. })));
    }

    // --- DELETE planner tests ---

    #[tokio::test]
    async fn test_plan_delete_basic() {
        let catalog = setup_catalog_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let delete = parse_delete("DELETE FROM users");

        let plan = plan_delete(&delete, &catalog).unwrap();

        let DmlPlan::Delete {
            table_name, input, ..
        } = &plan
        else {
            panic!("expected DmlPlan::Delete");
        };
        assert_eq!(table_name, "users");
        // No WHERE → input is bare SeqScan
        assert!(matches!(input.as_ref(), QueryPlan::SeqScan { .. }));
    }

    #[tokio::test]
    async fn test_plan_delete_with_where() {
        let catalog = setup_catalog_with_table("CREATE TABLE users (id INTEGER, name TEXT)").await;
        let delete = parse_delete("DELETE FROM users WHERE id = 1");

        let plan = plan_delete(&delete, &catalog).unwrap();

        let DmlPlan::Delete { input, .. } = &plan else {
            panic!("expected DmlPlan::Delete");
        };
        assert!(matches!(input.as_ref(), QueryPlan::Filter { .. }));
        assert_eq!(
            plan.explain(),
            "Delete on users\n  Filter: ($col0 (users.id) = 1)\n    SeqScan on users (cols: id, name)"
        );
    }

    #[tokio::test]
    async fn test_plan_delete_table_not_found() {
        let catalog = setup_catalog().await;
        let delete = parse_delete("DELETE FROM nonexistent");

        let result = plan_delete(&delete, &catalog);
        assert!(matches!(result, Err(ExecutorError::TableNotFound { .. })));
    }

    // --- Aggregate planner tests ---

    #[tokio::test]
    async fn test_plan_select_scalar_aggregate() {
        let catalog = setup_catalog().await;
        let select = parse_select("SELECT COUNT(*) FROM sys_tables");

        let plan = plan_select(&select, &catalog).unwrap();

        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].ty, Type::Bigint);
    }

    #[tokio::test]
    async fn test_plan_select_scalar_aggregate_with_alias() {
        let catalog = setup_catalog().await;
        let select = parse_select("SELECT COUNT(*) AS total FROM sys_tables");

        let plan = plan_select(&select, &catalog).unwrap();

        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].name, "total");
        assert_eq!(plan.columns()[0].ty, Type::Bigint);
    }

    #[tokio::test]
    async fn test_plan_select_group_by_single_column() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        let select = parse_select("SELECT dept, COUNT(*) FROM emp GROUP BY dept");

        let plan = plan_select(&select, &catalog).unwrap();

        assert_eq!(plan.columns().len(), 2);
        assert_eq!(plan.columns()[0].name, "dept");
        assert_eq!(plan.columns()[0].ty, Type::Text);
        assert_eq!(plan.columns()[1].ty, Type::Bigint);
    }

    #[tokio::test]
    async fn test_plan_select_group_by_multiple_columns() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, role TEXT, salary INTEGER)")
                .await;
        let select = parse_select("SELECT dept, role, SUM(salary) FROM emp GROUP BY dept, role");

        let plan = plan_select(&select, &catalog).unwrap();

        assert_eq!(plan.columns().len(), 3);
        assert_eq!(plan.columns()[0].name, "dept");
        assert_eq!(plan.columns()[1].name, "role");
        assert_eq!(plan.columns()[2].ty, Type::Bigint); // SUM(integer) → Bigint
    }

    #[tokio::test]
    async fn test_plan_select_group_by_with_having() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        let select =
            parse_select("SELECT dept, COUNT(*) FROM emp GROUP BY dept HAVING COUNT(*) > 1");

        let plan = plan_select(&select, &catalog).unwrap();

        // Plan should be: Projection → Filter (HAVING) → Aggregate → SeqScan
        assert_eq!(plan.columns().len(), 2);
    }

    #[tokio::test]
    async fn test_plan_select_having_without_group_by() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        // Scalar aggregate with HAVING
        let select = parse_select("SELECT COUNT(*) FROM emp HAVING COUNT(*) > 0");

        let plan = plan_select(&select, &catalog).unwrap();

        assert_eq!(plan.columns().len(), 1);
        assert_eq!(plan.columns()[0].ty, Type::Bigint);
    }

    #[tokio::test]
    async fn test_plan_select_multiple_aggregates() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        let select = parse_select("SELECT MIN(salary), MAX(salary), AVG(salary) FROM emp");

        let plan = plan_select(&select, &catalog).unwrap();

        assert_eq!(plan.columns().len(), 3);
        assert_eq!(plan.columns()[0].ty, Type::Integer); // MIN preserves type
        assert_eq!(plan.columns()[1].ty, Type::Integer); // MAX preserves type
        assert_eq!(plan.columns()[2].ty, Type::Double); // AVG always Double
    }

    #[tokio::test]
    async fn test_plan_select_aggregate_with_literal() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        // Literal in SELECT with aggregation is allowed
        let select = parse_select("SELECT 1, COUNT(*) FROM emp");

        let plan = plan_select(&select, &catalog).unwrap();

        assert_eq!(plan.columns().len(), 2);
        assert_eq!(plan.columns()[0].ty, Type::Bigint); // literal 1
        assert_eq!(plan.columns()[1].ty, Type::Bigint); // COUNT(*)
    }

    #[tokio::test]
    async fn test_plan_select_duplicate_aggregate_reuses_position() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        // Same COUNT(*) used in SELECT and HAVING should share the aggregate position
        let select =
            parse_select("SELECT dept, COUNT(*) FROM emp GROUP BY dept HAVING COUNT(*) > 1");

        let plan = plan_select(&select, &catalog).unwrap();

        // Should succeed (the planner deduplicates the COUNT(*) aggregate)
        assert_eq!(plan.columns().len(), 2);
    }

    #[tokio::test]
    async fn test_plan_select_explain_aggregate() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        let select = parse_select("SELECT dept, COUNT(*) FROM emp GROUP BY dept");

        let plan = plan_select(&select, &catalog).unwrap();
        let explain = plan.explain();

        assert!(explain.contains("Aggregate:"));
        assert!(explain.contains("group_by="));
        assert!(explain.contains("COUNT(*)"));
    }

    // --- Aggregate error tests ---

    #[tokio::test]
    async fn test_plan_select_aggregate_in_where_error() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        let select = parse_select("SELECT * FROM emp WHERE COUNT(*) > 1");

        let Err(err) = plan_select(&select, &catalog) else {
            panic!("expected error");
        };
        let ExecutorError::AggregateNotAllowed { context } = &err else {
            panic!("expected AggregateNotAllowed, got {:?}", err);
        };
        assert!(context.contains("WHERE"));
    }

    #[tokio::test]
    async fn test_plan_select_aggregate_in_group_by_error() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        let select = parse_select("SELECT dept FROM emp GROUP BY COUNT(*)");

        let Err(err) = plan_select(&select, &catalog) else {
            panic!("expected error");
        };
        let ExecutorError::AggregateNotAllowed { context } = &err else {
            panic!("expected AggregateNotAllowed, got {:?}", err);
        };
        assert!(context.contains("GROUP BY"));
    }

    #[tokio::test]
    async fn test_plan_select_non_aggregated_column_error() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        let select = parse_select("SELECT dept, salary FROM emp GROUP BY dept");

        let Err(err) = plan_select(&select, &catalog) else {
            panic!("expected error");
        };
        let ExecutorError::NonAggregatedColumn { name } = &err else {
            panic!("expected NonAggregatedColumn, got {:?}", err);
        };
        assert!(name.contains("salary"));
    }

    #[tokio::test]
    async fn test_plan_select_sum_text_type_error() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        let select = parse_select("SELECT SUM(dept) FROM emp");

        let result = plan_select(&select, &catalog);
        assert!(matches!(
            result,
            Err(ExecutorError::TypeMismatch { expected, .. }) if expected == "numeric"
        ));
    }

    #[tokio::test]
    async fn test_plan_select_avg_text_type_error() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        let select = parse_select("SELECT AVG(dept) FROM emp");

        let result = plan_select(&select, &catalog);
        assert!(matches!(
            result,
            Err(ExecutorError::TypeMismatch { expected, .. }) if expected == "numeric"
        ));
    }

    #[tokio::test]
    async fn test_plan_select_nested_aggregate_error() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        let select = parse_select("SELECT COUNT(SUM(salary)) FROM emp");

        let Err(err) = plan_select(&select, &catalog) else {
            panic!("expected error");
        };
        let ExecutorError::AggregateNotAllowed { context } = &err else {
            panic!("expected AggregateNotAllowed, got {:?}", err);
        };
        assert!(context.contains("aggregate function call"));
    }

    #[tokio::test]
    async fn test_plan_select_having_without_aggregate_error() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        // HAVING without any aggregate context → error
        let select = parse_select("SELECT * FROM emp HAVING true");

        let result = plan_select(&select, &catalog);
        assert!(matches!(result, Err(ExecutorError::Unsupported(msg)) if msg.contains("HAVING")));
    }

    #[tokio::test]
    async fn test_plan_select_wildcard_with_group_by_error() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        // SELECT * with GROUP BY — expanded columns are not all in GROUP BY
        let select = parse_select("SELECT * FROM emp GROUP BY dept");

        let result = plan_select(&select, &catalog);
        assert!(matches!(
            result,
            Err(ExecutorError::NonAggregatedColumn { .. })
        ));
    }

    // --- ORDER BY planner tests ---

    #[tokio::test]
    async fn test_plan_select_order_by_single_column() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER, name TEXT)").await;
        let select = parse_select("SELECT * FROM t ORDER BY id");

        let plan = plan_select(&select, &catalog).unwrap();
        let explain = plan.explain();
        assert!(explain.contains("Sort:"), "explain: {}", explain);
    }

    #[tokio::test]
    async fn test_plan_select_order_by_desc() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER, name TEXT)").await;
        let select = parse_select("SELECT * FROM t ORDER BY id DESC");

        let plan = plan_select(&select, &catalog).unwrap();
        let explain = plan.explain();
        assert!(explain.contains("DESC"), "explain: {}", explain);
    }

    #[tokio::test]
    async fn test_plan_select_order_by_alias() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER, name TEXT)").await;
        let select = parse_select("SELECT name AS n FROM t ORDER BY n");

        let plan = plan_select(&select, &catalog).unwrap();
        let explain = plan.explain();
        assert!(explain.contains("Sort:"), "explain: {}", explain);
    }

    #[tokio::test]
    async fn test_plan_select_order_by_positional() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER, name TEXT)").await;
        let select = parse_select("SELECT id, name FROM t ORDER BY 2");

        let plan = plan_select(&select, &catalog).unwrap();
        let explain = plan.explain();
        assert!(explain.contains("Sort:"), "explain: {}", explain);
    }

    #[tokio::test]
    async fn test_plan_select_order_by_positional_out_of_range() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER, name TEXT)").await;
        let select = parse_select("SELECT id, name FROM t ORDER BY 3");

        let result = plan_select(&select, &catalog);
        assert!(matches!(result, Err(ExecutorError::Unsupported(msg)) if msg.contains("position")));
    }

    #[tokio::test]
    async fn test_plan_select_order_by_positional_zero() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER, name TEXT)").await;
        let select = parse_select("SELECT id FROM t ORDER BY 0");

        let result = plan_select(&select, &catalog);
        assert!(matches!(result, Err(ExecutorError::Unsupported(msg)) if msg.contains("position")));
    }

    #[tokio::test]
    async fn test_plan_select_order_by_expression() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER, name TEXT)").await;
        let select = parse_select("SELECT * FROM t ORDER BY id + 1");

        let plan = plan_select(&select, &catalog).unwrap();
        let explain = plan.explain();
        assert!(explain.contains("Sort:"), "explain: {}", explain);
    }

    #[tokio::test]
    async fn test_plan_select_order_by_with_group_by() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        let select = parse_select("SELECT dept, COUNT(*) FROM emp GROUP BY dept ORDER BY dept");

        let plan = plan_select(&select, &catalog).unwrap();
        let explain = plan.explain();
        assert!(explain.contains("Sort:"), "explain: {}", explain);
        assert!(explain.contains("Aggregate:"), "explain: {}", explain);
    }

    #[tokio::test]
    async fn test_plan_select_order_by_aggregate_expr() {
        let catalog =
            setup_catalog_with_table("CREATE TABLE emp (dept TEXT, salary INTEGER)").await;
        // ORDER BY an aggregate expression not in SELECT
        let select = parse_select("SELECT dept FROM emp GROUP BY dept ORDER BY COUNT(*)");

        let plan = plan_select(&select, &catalog).unwrap();
        let explain = plan.explain();
        assert!(explain.contains("Sort:"), "explain: {}", explain);
    }

    #[tokio::test]
    async fn test_plan_select_order_by_triggers_aggregation() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER)").await;
        // ORDER BY COUNT(*) triggers aggregation context for the entire query.
        // Since id is not in GROUP BY and not aggregated → NonAggregatedColumn
        let select = parse_select("SELECT id FROM t ORDER BY COUNT(*)");

        let result = plan_select(&select, &catalog);
        assert!(matches!(
            result,
            Err(ExecutorError::NonAggregatedColumn { .. })
        ));
    }

    #[tokio::test]
    async fn test_plan_select_order_by_nulls_first() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER)").await;
        let select = parse_select("SELECT * FROM t ORDER BY id NULLS FIRST");

        let plan = plan_select(&select, &catalog).unwrap();
        let explain = plan.explain();
        assert!(explain.contains("NULLS FIRST"), "explain: {}", explain);
    }

    // --- LIMIT/OFFSET planner tests ---

    #[tokio::test]
    async fn test_plan_select_limit() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER)").await;
        let select = parse_select("SELECT * FROM t LIMIT 10");

        let plan = plan_select(&select, &catalog).unwrap();
        let explain = plan.explain();
        assert!(explain.contains("Limit:"), "explain: {}", explain);
        assert!(explain.contains("limit=10"), "explain: {}", explain);
    }

    #[tokio::test]
    async fn test_plan_select_offset() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER)").await;
        let select = parse_select("SELECT * FROM t OFFSET 5");

        let plan = plan_select(&select, &catalog).unwrap();
        let explain = plan.explain();
        assert!(explain.contains("Limit:"), "explain: {}", explain);
        assert!(explain.contains("offset=5"), "explain: {}", explain);
    }

    #[tokio::test]
    async fn test_plan_select_limit_and_offset() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER)").await;
        let select = parse_select("SELECT * FROM t LIMIT 10 OFFSET 5");

        let plan = plan_select(&select, &catalog).unwrap();
        let explain = plan.explain();
        assert!(explain.contains("limit=10"), "explain: {}", explain);
        assert!(explain.contains("offset=5"), "explain: {}", explain);
    }

    #[tokio::test]
    async fn test_plan_select_negative_limit_error() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER)").await;
        let select = parse_select("SELECT * FROM t LIMIT -1");

        let result = plan_select(&select, &catalog);
        assert!(matches!(
            result,
            Err(ExecutorError::Unsupported(msg)) if msg.contains("negative")
        ));
    }

    #[tokio::test]
    async fn test_plan_select_negative_offset_error() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER)").await;
        let select = parse_select("SELECT * FROM t OFFSET -1");

        let result = plan_select(&select, &catalog);
        assert!(matches!(
            result,
            Err(ExecutorError::Unsupported(msg)) if msg.contains("negative")
        ));
    }

    #[tokio::test]
    async fn test_plan_select_limit_non_integer_error() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER)").await;
        let select = parse_select("SELECT * FROM t LIMIT 'abc'");

        let result = plan_select(&select, &catalog);
        assert!(matches!(
            result,
            Err(ExecutorError::TypeMismatch { expected, .. }) if expected == "integer"
        ));
    }

    #[tokio::test]
    async fn test_plan_select_limit_zero() {
        let catalog = setup_catalog_with_table("CREATE TABLE t (id INTEGER)").await;
        let select = parse_select("SELECT * FROM t LIMIT 0");

        let plan = plan_select(&select, &catalog).unwrap();
        let explain = plan.explain();
        assert!(explain.contains("limit=0"), "explain: {}", explain);
    }
}
