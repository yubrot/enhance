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

### Step 2: Triage Issues

Classify each High/Medium issue from the review into one of two categories:

- **Quality fix**: Naming tweaks, missing docs, unused imports, test gaps, minor API cleanup — changes that do NOT alter the design sketch's Type Glossary, Module Structure, or Dependency Graph
- **Design correction**: Module moves, type splits/renames, new public types, API signature changes, dependency direction changes — changes that **would require updating the design sketch** to remain accurate

#### Quality Fixes

1. Fix the issues in code
2. Run `cargo test` and `cargo clippy`
3. Launch a **fresh** review subagent (do NOT resume the previous one) to re-review the full diff
4. Repeat until no High/Medium quality issues remain

**Important**: Every review iteration MUST use a new `Task` invocation — never resume a previous review agent. A fresh agent re-reads the diff from scratch without prior assumptions, which means it can catch issues that the previous iteration overlooked or that were introduced by the fixes themselves.

#### Design Corrections

If any issues are classified as design corrections, **pause autonomous execution** and present them to the user with `AskUserQuestion`:

- Describe each design correction concisely (what the review found, what structural change it implies)
- Offer two choices per issue:
  1. **Update design sketch**: Modify `docs/design-sketch-{N}.md` (Type Glossary, Module Structure, signatures, etc.) to reflect the correction, then apply the code fix. This ensures subsequent Commit Plan items build on the corrected design.
  2. **Proceed as-is**: Treat it as a quality fix (no design sketch update). Use this when the review finding is debatable or the impact on future items is negligible.

After the user decides, apply the chosen action for each issue. If any design sketch updates were made, re-read the updated design sketch before continuing.

#### Low Severity

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
