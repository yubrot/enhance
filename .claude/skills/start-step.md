---
name: start-step
description: Starts implementation of a roadmap step by reviewing project context, gathering architectural decisions from user with trade-off analysis and real RDBMS examples, then entering plan mode. Use when beginning work on a new step.
arguments:
  - name: step-number
    description: The roadmap step number to implement (e.g., "7", "8")
    required: true
---

# Starting a Roadmap Step

## Workflow

### Phase 1: Context Gathering

1. **Read project context**:
   - Read README.md to find the step's goal and scope
   - Read all existing docs/\*.md files to understand prior decisions
   - Read docs/todo.md to check difficulty rating and recommended approach

2. **Identify the step details**:
   - Extract the step title, goal, and description from README.md
   - Note the difficulty rating from docs/todo.md
   - Review any related architectural decisions from README.md tables

### Phase 2: Difficulty-Based Strategy

Apply the strategy from docs/todo.md based on difficulty:

| Difficulty | Strategy                                                                                                            |
| :--------: | ------------------------------------------------------------------------------------------------------------------- |
|    2-3     | Proceed to plan mode after minimal clarification                                                                    |
|     4      | Fix design first through detailed questions, then plan in small increments                                          |
|     5      | **Require explicit confirmation of logic at pseudocode level** before coding. Focus on concurrency/state management |

### Phase 3: Decision Gathering

Before entering plan mode, identify and ask about key architectural decisions for this step.

**Question Format Requirements:**

When asking the user for decisions, ALWAYS include:

1. **Clear explanation of the decision**: What are we deciding and why it matters
2. **Options with trade-offs**: Each option should explain pros/cons
3. **Real RDBMS examples**: Which databases use which approach
   - PostgreSQL, MySQL, SQLite, Oracle, SQL Server are common references
4. **Recommendation**: Based on project goals (learning, PostgreSQL compatibility)

**Example question structure:**

```
## [Decision Topic]

[Brief context: why this decision matters]

### Options:

1. **[Option A]**
   - Trade-offs: [pros/cons]
   - Used by: [PostgreSQL, MySQL, etc.]

2. **[Option B]**
   - Trade-offs: [pros/cons]
   - Used by: [Oracle, SQL Server, etc.]

### Recommendation: [Option X] because [rationale aligned with project goals]
```

### Phase 4: Enter Plan Mode

After gathering decisions, enter plan mode to:

1. Explore the existing codebase for integration points
2. Design the implementation approach
3. Create a detailed plan for user approval
4. For difficulty 5 items, include pseudocode for critical sections

## Writing Style

- The user is not an RDBMS implementation expert, so explain concepts clearly
- Always ground explanations in concrete examples
- Prefer PostgreSQL-aligned choices unless there's a compelling reason otherwise
- Reference the project's existing architectural decisions from README.md
