# REFINE Phase

Review the current commit plan item, fix any issues, mark it done, and commit.

## IMPLEMENT ↔ REFINE Cycle

After ARCHITECT, the workflow cycles through IMPLEMENT → REFINE for each Commit Plan item:

1. **IMPLEMENT**: Code the next unchecked `- [ ]` item and run tests (no commit)
2. **REFINE**: This phase (described below)
3. **Loop**: Return to IMPLEMENT for the next unchecked item, or proceed to COMPLETE if all items are `[x]`

## Procedure

### Step 1: Review (Subagent)

Launch a `Task` tool (`subagent_type=general-purpose`) to perform the review in an isolated context. Pass the following instructions:

- Read `.claude/skills/review/SKILL.md` and follow the methodology
- Scope: uncommitted changes (`git diff`)
- Design sketch: `docs/design-sketch-{N}.md`
- Return the review report

Using a subagent ensures the review is not influenced by implementation context.

### Step 2: Fix Issues (if any)

If the review reports High or Medium severity issues:

1. Fix the issues in code
2. Run `cargo test` and `cargo clippy`
3. Re-run the review subagent to confirm the fixes resolved the issues
4. Repeat until no High/Medium issues remain

Low severity issues: present to the user and let them decide whether to fix now or defer.

### Step 3: Mark Done and Commit

Once the review passes:

1. Check off the item (`- [ ]` → `- [x]`) in `docs/design-sketch-{N}.md`
2. Commit all changes (implementation + fixes + design-sketch update) using the `commit` skill
