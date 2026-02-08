---
name: review
description: Read-only structural analysis of implementation changes (naming consistency, module boundaries, dependency direction, error design, API surface). Reports issues but does not fix them. Invoked by the step workflow's REFINE phase, or standalone via "review", "check structure", "pre-review".
arguments: []
---

# Review

Read-only structural analysis of implementation changes. Identifies issues but does not fix them.

## Execution Model

Always run this review in an **isolated subagent** (`Task` tool, `subagent_type=general-purpose`) to avoid context bias. The subagent reads this file for the methodology and returns the review report.

Pass the following to the subagent:

- **Scope**: What changes to review (e.g., `git diff` for uncommitted, `git diff main..step-{N}` for branch)
- **Design sketch** (optional): Path to design-sketch for naming/structure reference

When invoked standalone (e.g., user says "review"), default scope is uncommitted changes (`git diff`).

## When to Use

- Invoked by the `step` workflow's REFINE phase (reviewing uncommitted changes per commit plan item)
- Invoked by the `step` workflow's COMPLETE phase (reviewing the entire step branch)
- Standalone when the user says "review architecture", "check structure", or "pre-review"

---

## Methodology (for the subagent)

The sections below are instructions for the review subagent.

### Phase 1: Gather Changes

1. Run the appropriate diff command(s) for the specified scope
   - Uncommitted changes: `git diff` (staged + unstaged)
   - Branch diff: `git diff main..{branch}` (all committed changes on the branch)
   - If no scope is specified, default to uncommitted changes (`git diff`)
2. Run `--name-only` variant to identify all affected files
3. Read the affected files in full
4. If a design sketch is referenced, read it and identify relevant commit plan items and the type glossary

### Phase 2: Structural Analysis

Run each check below. For each issue found, note the file, line, and specific concern.

#### Check 1: Naming Consistency

- Are the same concepts named consistently across all files?
  - Look for synonyms: e.g., "tuple" and "row" used for the same concept
  - Look for abbreviation inconsistency: e.g., `col` vs `column`, `expr` vs `expression`
- Do type names match their module location?
  - e.g., a type in `executor/` should not be named `HeapTuple`
- Are method names consistent with existing codebase conventions?
  - Read adjacent modules to check naming patterns

#### Check 2: Module Boundaries

- Is each type defined in the module that uses it most?
  - A type defined in module A but primarily used in module B should probably move to B
- Are there types that serve as "pass-through" between modules?
  - These often indicate a missing abstraction or a type in the wrong module
- Is the public API surface appropriate for cross-module consumers?
  - For each `pub` item, consider: does it make sense for other top-level modules (e.g., `executor` consuming `catalog`, `planner` consuming `parser`) to depend on this?
  - Look for internal implementation details leaking into the cross-module API (e.g., storage-layer types exposed through executor's public interface)
  - Look for `pub` fields on structs that should have accessor methods

#### Check 3: Dependency Direction

- Draw the dependency graph from imports
- Verify: no circular dependencies between modules
- Verify: higher-level modules (db, server) depend on lower-level (executor, catalog, heap), not the reverse
- Look for: lower-level modules importing types from higher-level modules (a strong smell)

#### Check 4: Error Type Design

- Are there redundant error variants? (variants that wrap the same underlying error differently)
- Are there unused error variants? (defined but never constructed)
- Is the error conversion chain clean? (A → B → C, no shortcuts that bypass layers)
- Are sentinel values used where `Option` would be more appropriate?

#### Check 5: API Ergonomics

- Do callers need to reach into struct internals? (Indicates missing method)
- Are there sequences of calls that are always done together? (Indicates missing helper)
- Are there `clone()` or `Arc::clone()` calls that indicate ownership confusion?

#### Check 6: Edge Case Coverage (if design-sketch provided)

- Compare the edge case checklist from the design sketch against actual tests
- Flag any uncovered edge cases

#### Check 7: Consistency with Existing Patterns

- Read 2-3 existing modules to understand established patterns:
  - Error type naming: `{Module}Error` pattern
  - Module file structure: named files, not `mod.rs`
  - Documentation: rustdoc on public items
  - Test structure: `#[cfg(test)] mod tests` placement
- Flag any deviations from established patterns

### Phase 3: Report

Present findings in this format:

```
## Architecture Review: {scope description}

### Issues Found

#### [Severity: High/Medium/Low] {Category}: {Brief description}
- **Location**: `src/foo/bar.rs:42`
- **Problem**: {What's wrong}
- **Suggestion**: {How to fix it}
- **Evidence**: {Found in PR #12/#13/#15 pattern, or specific code reference}

### No Issues

{List checks that passed cleanly}

### Summary
- {N} high-severity issues (should fix before review)
- {N} medium-severity issues (recommend fixing)
- {N} low-severity issues (optional improvements)
```

Severity guidelines:

- **High**: Would definitely be caught in human review and require a fix commit (wrong module, circular dependency, naming contradiction)
- **Medium**: Likely to be caught and cause discussion (suboptimal API, missing `pub(crate)`, inconsistent naming)
- **Low**: Stylistic or minor (could be slightly better naming, slightly cleaner error chain)

### Important Notes

- This review is **read-only** — report issues but do not modify code
- If no design-sketch is provided, skip Check 6 but note this in the report
