# enhance

See @README.md for project vision, architectural decisions, and roadmap.
See @docs/ for step-by-step implementation reports.

## Build and Test Commands

```bash
# Build the project
cargo build

# Run all tests
cargo test

# Run a specific test
cargo test test_name

# Run tests with output visible
cargo test -- --nocapture

# Run the server (listens on 127.0.0.1:15432)
cargo run

# Shorthand for psql to the server
mise run psql
```

## Development Philosophy

### Production-Reachable Architecture

This is a learning project, but we never take shortcuts that bypass real data paths:

- The gap between this codebase and a production system is **scope** (fewer features, simpler algorithms), not **structure** (fake data paths, bypassed layers)
- Queries always traverse the full pipeline: parse → plan → execute → heap I/O → MVCC visibility
- Use `NOTE:` comments to document deferred production improvements, keeping the gap visible

### Communication Style

- When refactoring Rust code, always run `cargo test` AND `cargo clippy --all-targets` after changes. Do not consider a task complete until both pass with zero warnings
- Do NOT make changes beyond what was explicitly requested. If you notice adjacent improvements (removing doc comments, inlining variables, removing calls), mention them but do not apply them without explicit approval
- When the user suggests a design change, critically evaluate it against domain semantics before implementing. If the suggestion could violate correctness (e.g., RDBMS transaction semantics, PostgreSQL behavior), raise the concern BEFORE writing code rather than implementing and reverting
- PostgreSQL is a design reference, not a compatibility target (see @README.md). Describe enhance's own behavior rather than implying PostgreSQL compatibility

### Code Style

- Use named module files (`src/foo.rs`) instead of `mod.rs` files
- Add rustdoc comments (`///`) to all public items
- Prefer `Result` over panicking for recoverable errors
- Use `NOTE:` comments to document deferred production improvements (see Development Philosophy above)
- In tests, prefer `let-else` with `panic!` in the else branch over `match` with a wildcard panic arm when asserting on a specific enum variant. This reduces nesting and improves readability. Use judgment: if `let-else` would be more verbose (e.g., when only checking the variant with `assert!(matches!(...))`), keep the existing form
- In tests, upper layers may use lower-layer functionality to set up test data. For example, executor and server tests should use `Parser::new(sql).parse()` to obtain AST nodes instead of constructing them manually
