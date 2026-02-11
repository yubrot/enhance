# IMPLEMENT Phase

Write code for the **next unchecked commit plan item** from the approved design sketch.

## Procedure

1. Run `/compact` before proceeding. This keeps context lean across cycles
2. Read `docs/design-sketch-{N}.md` **in full** (the design sketch may have been updated by REFINE design corrections) and identify the next `- [ ]` item in the Commit Plan
3. Implement **only that item**:
   - Write the code as specified in the design sketch
   - Run `cargo test` and `cargo clippy`
4. Leave changes uncommitted — the REFINE phase will review, fix issues, and commit

## Constraints

- Follow the Type Glossary naming exactly
- Place types in the modules specified by the Module Structure
- Implement the Error Hierarchy as designed
- Cover relevant Edge Case Checklist items with tests (as noted in the commit plan item)
- Do NOT deviate from the design sketch without asking the user
- Do NOT implement multiple commit plan items at once — one item per IMPLEMENT → REFINE cycle
