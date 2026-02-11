# ARCHITECT Phase

Gather context, make architectural decisions with the user, and create the design sketch.

## Step 0: Branch Setup

Create the step branch from `main`:

```bash
git checkout -b step-{N}
```

## Step 1: Context Gathering

Use `Task` tool (`subagent_type=Explore`) to gather:

- Step title, goal, and description from README.md
- Difficulty rating from docs/todo.md
- Related ADR entries from README.md tables
- Prior decisions from all docs/\*.md files
- Existing source modules this step will integrate with

## Step 2: Prerequisite Assessment

Analyze the existing codebase for changes needed **before** the feature implementation can begin cleanly. Use `Task` tool (`subagent_type=Explore`) to check:

- **Naming inconsistencies**: Will this step introduce terms that conflict with existing names? (e.g., "tuple" vs "row" ambiguity before adding DML)
- **Type/error hierarchy gaps**: Do existing types need renaming, splitting, or new variants before the feature fits naturally?
- **Module structure debt**: Are there modules that should be reorganized before adding new functionality on top?
- **Missing abstractions**: Are there patterns duplicated across the codebase that this step will duplicate further?

Present findings to the user. Any prerequisite refactoring identified here becomes part of the Commit Plan (as early items, before the feature commits) in the design sketch.

## Step 3: Decision Gathering

Ask the user about key architectural decisions for this step. Each question MUST include:

1. **What we're deciding** and why it matters
2. **Options with trade-offs** (pros/cons for each)
3. **Real RDBMS examples** (PostgreSQL, MySQL, SQLite, Oracle, SQL Server)
4. **Recommendation** aligned with project goals (learning, PostgreSQL as reference)

Use `AskUserQuestion` for structured choices where possible.

## Step 4: Design Sketch

Invoke the `design-sketch` skill with the step number. Pass the gathered context and user decisions so the skill can produce the document without redundant exploration:

- **Step context**: title, goal, scope from README.md
- **Prior patterns**: naming conventions, module organization from existing docs and source
- **Prerequisite refactoring**: changes identified in Step 2 (to be included as early Commit Plan items)
- **User decisions**: architectural choices made in Step 3
- **Integration points**: existing modules and types this step will touch

This context is already in the conversation (since skills share context). Summarize it concisely when invoking the skill so that design-sketch can focus on document generation.
