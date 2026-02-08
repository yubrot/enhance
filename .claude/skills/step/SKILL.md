---
name: step
description: Unified entry point for the roadmap step lifecycle. Detects current phase from artifacts and advances through ARCHITECT → IMPLEMENT → REFINE → COMPLETE. IMPLEMENT and REFINE cycle per Commit Plan item, using design-sketch-{N}.md as a todo list. Use when starting, continuing, or completing any roadmap step.
arguments:
  - name: step-number
    description: The roadmap step number (e.g., "11", "12")
    required: true
---

# Step Workflow Orchestrator

This skill manages the full lifecycle of a roadmap step. Each invocation detects the current phase from artifacts and advances to the next. The Commit Plan in `docs/design-sketch-{N}.md` serves as the todo list — IMPLEMENT and REFINE cycle once per item.

## Branch Convention

Each step works on a dedicated branch `step-{N}` created from `main`. All commits during the step are made on this branch. Before phase detection, ensure the working tree is on `step-{N}` (switch to it if it exists, or note that ARCHITECT will create it).

## Autonomous Execution

The ARCHITECT phase is **interactive** — it gathers context and decisions from the user, and presents the design sketch for approval.

Once ARCHITECT completes and the design sketch is approved, the workflow proceeds **autonomously** through all remaining phases (IMPLEMENT → REFINE → ... → COMPLETE) without waiting for user confirmation. Report progress at each phase transition but do not pause for approval.

## Phase Detection

Check artifacts **in this order** to determine the current phase:

1. Step N is marked ✅ in README.md → **DONE** (inform user)
2. `docs/{N}.md` exists → **DONE** (inform user)
3. `docs/design-sketch-{N}.md` does not exist → **ARCHITECT** (start, interactive)
4. `docs/design-sketch-{N}.md` exists — parse "Commit Plan" checkboxes:
   a. If all items are `[x]` → **COMPLETE**
   b. If `git diff --name-only` shows uncommitted `src/` changes → **REFINE** (for the current item)
   c. Otherwise → **IMPLEMENT** (next `[ ]` item)

For ARCHITECT: confirm with the user before proceeding.
For IMPLEMENT/REFINE/COMPLETE: report progress ("Commit Plan item {M}/{total}: {title}") and proceed autonomously.

## Phases

| Phase     | Action                                                | Delegation                       |
| --------- | ----------------------------------------------------- | -------------------------------- |
| ARCHITECT | Gather context, decisions, and create design sketch   | See [architect.md](architect.md) |
| IMPLEMENT | Write code for the next unchecked commit plan item    | See [implement.md](implement.md) |
| REFINE    | Review, fix issues, mark item done, and commit        | See [refine.md](refine.md)      |
| COMPLETE  | Review full step, mark done, and create documentation | See [complete.md](complete.md)  |
