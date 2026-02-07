# enhance

enhance is an educational RDBMS implementation built from scratch in Rust. The goal is to understand database internals by manually implementing everything from the wire protocol (using PostgreSQL's protocol for psql compatibility) to the storage engine. This is a learning-focused project, not production software.

See @README.md and @docs/ for the current status of this project.

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

## Communication Style

- When refactoring Rust code, always run `cargo test` AND `cargo clippy` after changes. Do not consider a task complete until both pass with zero warnings
- Do NOT make changes beyond what was explicitly requested. If you notice adjacent improvements (removing doc comments, inlining variables, removing calls), mention them but do not apply them without explicit approval
- When the user suggests a design change, critically evaluate it against domain semantics before implementing. If the suggestion could violate correctness (e.g., RDBMS transaction semantics, PostgreSQL behavior), raise the concern BEFORE writing code rather than implementing and reverting
- This is a self-built RDBMS engine in Rust. PostgreSQL is a design reference, NOT a compatibility target. Do not imply PostgreSQL compatibility in documentation or code comments

## Code Style

- Use named module files (`src/foo.rs`) instead of `mod.rs` files
- Add rustdoc comments (`///`) to all public items
- Prefer `Result` over panicking for recoverable errors
- Throughout the codebase, `NOTE:` comments document production improvements that are intentionally deferred to keep the learning implementation minimal

