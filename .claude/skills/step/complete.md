# COMPLETE Phase

Review the full step, mark it as done, and create documentation.

## Pre-check

Verify that **all** Commit Plan items in `docs/design-sketch-{N}.md` are checked (`- [x]`). If any `- [ ]` items remain, do NOT proceed — return to IMPLEMENT phase.

## Step 1: Full Step Review (Subagent)

Launch a `Task` tool (`subagent_type=general-purpose`) to perform the review in an isolated context. Pass the following instructions:

- Read `.claude/skills/review/SKILL.md` and follow the methodology
- Scope: `git diff main..step-{N}`
- Design sketch: `docs/design-sketch-{N}.md`
- Return the review report

Fix any issues found before proceeding.

## Step 2: Documentation Drafting (Subagent)

Use `Task` tool (`subagent_type=general-purpose`) to:

1. Analyze the implementation code (read all changed/new files)
2. Read `git log` for commit history on this step
3. Read `docs/design-sketch-{N}.md` for intended design
4. Draft the documentation report content

## Step 3: Actions (in main context)

1. **Mark README.md**: Find the step line and add ✅ after the number
   - e.g., `11. DML Operations:` → `11. ✅ DML Operations:`

2. **Remove from docs/todo.md**: Delete the table row for this step number

3. **Create docs/{N}.md**: Write the documentation report:

```markdown
# Step {N}: {Step Title}

> {Goal from README.md}

# This Step I Learned

{Architectural decisions, design rationale, "why" not "what".
Focus on what the sub-agent drafted, edited for accuracy.}

# Looking Forward

{Deferred items (from NOTE: comments), production gaps, future steps.}
```

4. **Clean up**: Delete `docs/design-sketch-{N}.md` (design is now captured in `docs/{N}.md`)
