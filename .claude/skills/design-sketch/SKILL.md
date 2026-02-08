---
name: design-sketch
description: Creates a design document before implementation that settles naming, module structure, edge cases, and commit-unit plan. Prevents post-implementation refactoring churn. Typically invoked as part of the `step` workflow, but can be used standalone.
arguments:
  - name: step-number
    description: The roadmap step number to design for (e.g., "11", "12")
    required: true
---

# Design Sketch

Create a design document that settles structural decisions **before** writing code. The document is written to `docs/design-sketch-{step-number}.md` for human review. No code is written by this skill.

## Workflow

### Phase 1: Context Gathering

1. Read `README.md` to find the step's goal, scope, and relevant ADR entries
2. Read all `docs/*.md` to understand prior architectural patterns and naming conventions
3. Read existing source code that this step will integrate with:
   - Use `Grep` and `Read` to find the modules this step touches
   - Note existing naming patterns, error types, and module organization
4. If a `docs/design-sketch-{step-number}.md` already exists, read it and build upon its content

### Phase 2: Design Document Generation

Write `docs/design-sketch-{step-number}.md` with the following sections.

#### Template

````markdown
# Design Sketch: Step {N} — {Title}

> {Goal from README.md}

## Type Glossary

Define every new public type with its name, module location, and one-line purpose.
Explicitly distinguish terms that could be confused.

| Type        | Module             | Purpose                                                                  |
| ----------- | ------------------ | ------------------------------------------------------------------------ |
| `BoundExpr` | `executor/expr.rs` | AST Expr with column names resolved to positional indices                |
| `Row`       | `executor/row.rs`  | Logical row flowing through Volcano iterator (Record + optional TupleId) |

### Naming Decisions

Document any naming ambiguities and the chosen resolution:

- "tuple" vs "row": "tuple" = on-disk (TupleHeader + Record), "row" = in-executor logical unit
- ...

## Module Structure

### New Modules

List each new file with its responsibility and key public items.

- `src/executor/expr.rs` — Bound expression types and evaluation
  - `pub enum BoundExpr`
  - `pub fn evaluate(&self, record: &Record) -> Result<Value>`

### Modified Modules

List each existing file that will be changed, and what changes.

- `src/db/session.rs` — Add SELECT/EXPLAIN execution path
  - New method: `execute_select(&mut self, stmt: &SelectStmt) -> Result<QueryResult>`

### Dependency Graph

```text
session → planner → catalog (read-only)
session → node → context (I/O abstraction)
planner ✗ node (no direct dependency)
```

Verify: no circular dependencies, upper layers never imported by lower layers.

## Error Hierarchy

| Error Type      | Module              | Wraps / Variants                      | Converted to                             |
| --------------- | ------------------- | ------------------------------------- | ---------------------------------------- |
| `ExecutorError` | `executor/error.rs` | `TypeMismatch`, `ColumnNotFound`, ... | `DatabaseError::Executor(ExecutorError)` |

## Edge Case Checklist

Generate a checklist specific to this step's domain. Research what edge cases are relevant by considering:

- What data types does this step handle? (NULL, NaN, overflow, empty string, etc.)
- What state transitions exist? (transaction states, lock states, etc.)
- What concurrency scenarios apply? (latch ordering, visibility, etc.)
- What protocol-level concerns exist? (wire format, command tags, etc.)

Example for an expression evaluation step:

- [ ] NULL propagation in all binary operators (AND/OR short-circuit)
- [ ] NaN comparison ordering (PostgreSQL: NaN > all non-NaN)
- [ ] Integer overflow (checked_add/sub/mul/neg)
- [ ] CAST boundary values (f64 → i64 at limits, i64 → i16 range)
- [ ] Division by zero (integer = error, float = Infinity/NaN)
- [ ] Empty string vs NULL distinction

The checklist should be **generated from domain analysis**, not copied from a fixed template. Different steps have different edge cases.

## Commit Plan

Break the implementation into ordered commits. Each commit should be independently compilable and testable. Use checkboxes to track progress — the `step` workflow checks items off after each IMPLEMENT → REFINE cycle.

- [ ] **Commit 1: Type definitions** — {list of types} in {modules}
  - Tests: Display/Debug impls, basic construction
- [ ] **Commit 2: Core logic** — {description}
  - Tests: {what to test, including relevant edge cases from checklist}
- [ ] **Commit 3: Integration** — {description}
  - Tests: {integration tests}
````

### Phase 3: Self-Verification

Before presenting the document, verify:

1. **No unnamed types**: Every type that will exist in code has a name and module location
2. **No ambiguous terms**: Every domain term that could mean multiple things has a definition
3. **Dependency direction**: Draw the dependency arrows and confirm no cycles
4. **Edge case coverage**: Each checklist item maps to at least one test in the commit plan
5. **Commit independence**: Each commit in the plan can compile and pass tests on its own

### Phase 4: Present for Review

Output the design document content and ask the user to review it. Highlight any decisions where you are uncertain and present alternatives.

Do NOT enter plan mode or write implementation code. The design sketch is the deliverable.

## Integration with Step Workflow

- **Orchestrated by `step` skill**: The `step` skill invokes this as the ARCHITECT phase
- **Before implementation**: The approved design sketch becomes the specification for the IMPLEMENT phase
