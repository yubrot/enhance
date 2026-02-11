# REFINE Phase

Review the current commit plan item, fix any issues, mark it done, and commit.

## IMPLEMENT ↔ REFINE Cycle

After ARCHITECT, the workflow cycles through IMPLEMENT → REFINE for each Commit Plan item:

1. **IMPLEMENT**: Code the next unchecked `- [ ]` item and run tests (no commit)
2. **REFINE**: This phase (described below)
3. **Loop**: Return to IMPLEMENT for the next unchecked item, or proceed to COMPLETE if all items are `[x]`

## Procedure

### Step 1: Review (Subagent)

Launch a **new** `Task` tool (`subagent_type=general-purpose`) to perform the review in an isolated context. Pass the following instructions:

- Read `.claude/skills/review/SKILL.md` and follow the methodology
- Scope: uncommitted changes (`git diff`)
- Design sketch: `docs/design-sketch-{N}.md`
- Return the review report

Using a subagent ensures the review is not influenced by implementation context.

### Step 2: Fix Issues (if any)

If the review reports High or Medium severity issues:

1. Fix the issues in code
2. Run `cargo test` and `cargo clippy`
3. Launch a **fresh** review subagent (do NOT resume the previous one) to re-review the full diff
4. Repeat until no High/Medium issues remain

**Important**: Every review iteration MUST use a new `Task` invocation — never resume a previous review agent. A fresh agent re-reads the diff from scratch without prior assumptions, which means it can catch issues that the previous iteration overlooked or that were introduced by the fixes themselves.

Low severity issues: present to the user and let them decide whether to fix now or defer.

### Step 3: Record Deviations

Before marking the item done, compare what was actually implemented against the commit plan item description in `docs/design-sketch-{N}.md`. Check for deviations such as:

- Scope changes (implemented more or less than planned)
- Different naming or module placement than specified
- Additional or removed types, functions, or error variants
- Different test strategy than described
- Design decisions that diverged from the Type Glossary, Module Structure, or Edge Case Checklist

If any deviations exist, append a `Deviation:` note directly under the commit plan item in the design sketch. Use concise, factual language describing **what** changed and **why**.

Example:

```markdown
- [x] **Commit 3: HeapWriter — multi-page insert** — ...
  - Tests: ...
  - Deviation: Added `HeapWriter::insert_on_page` as a separate public method (not in original plan) because `update_tuple` needed same-page insertion without chain walking. Also renamed `allocate_page` to `extend_chain` to better reflect the linking semantics.
```

If no deviations occurred, skip this step — do not add a `Deviation: none` note.

### Step 4: Mark Done and Commit

Once the review passes and any deviations are recorded:

1. Check off the item (`- [ ]` → `- [x]`) in `docs/design-sketch-{N}.md`
2. Commit all changes (implementation + fixes + design-sketch update) using the `commit` skill
