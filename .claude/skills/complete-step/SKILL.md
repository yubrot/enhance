---
name: complete-step
description: Marks a roadmap step as completed by adding a checkmark emoji to README.md, removing the step from docs/todo.md, and creating a documentation report at docs/[step-number].md. Analyzes implementation code to document architectural decisions and production gaps. Use when user says "complete step", "mark step done", or "finish step X".
arguments:
  - name: step-number
    description: The roadmap step number to mark as complete (e.g., "7")
    required: true
---

# Completing a Roadmap Step

## Workflow

1. **Validate step number**: Confirm the step exists in README.md and is not already marked complete

2. **Mark complete in README.md**: Find the line matching the step number pattern (e.g., `7. Lexer & Parser:`) and add the checkmark emoji after the number, making it `7. ✅ Lexer & Parser:`

3. **Remove from docs/todo.md**: Delete the table row for this step number (format: `| 7 | **Title** | ... |`)

4. **Create docs/[step-number].md**: Generate a documentation report following the established format

## Documentation Report Format

```markdown
# Week X: [Step Title from README]

> [Goal description from README for this step]

# This Step I Learned

[Document architectural/design decisions and their rationale. Focus on "why" not "what".]

# Looking Forward

[Document what was deferred, production readiness gaps, and future considerations.]
```

## Writing Guidelines

**For "This Step I Learned":**

- Read existing docs/\*.md to match the writing style
- Analyze the actual implementation code to understand what was built
- Use `git log` or `git diff main..HEAD` to see what changed
- Focus on architecture decisions and design rationale (the "why")
- Include diagrams (mermaid) where helpful
- Document trade-offs and alternatives considered

**For "Looking Forward":**

- Identify what was intentionally deferred (check NOTE: comments in code)
- List production readiness gaps
- Reference future roadmap steps that build on this work
