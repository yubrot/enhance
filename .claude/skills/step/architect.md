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

## Step 2: Decision Gathering

Ask the user about key architectural decisions for this step. Each question MUST include:

1. **What we're deciding** and why it matters
2. **Options with trade-offs** (pros/cons for each)
3. **Real RDBMS examples** (PostgreSQL, MySQL, SQLite, Oracle, SQL Server)
4. **Recommendation** aligned with project goals (learning, PostgreSQL as reference)

Use `AskUserQuestion` for structured choices where possible.

## Step 3: Design Sketch

Invoke the `design-sketch` skill with the step number. Pass the gathered context and user decisions so the skill can produce the document without redundant exploration:

- **Step context**: title, goal, scope from README.md
- **Prior patterns**: naming conventions, module organization from existing docs and source
- **User decisions**: architectural choices made in Step 2
- **Integration points**: existing modules and types this step will touch

This context is already in the conversation (since skills share context). Summarize it concisely when invoking the skill so that design-sketch can focus on document generation.
