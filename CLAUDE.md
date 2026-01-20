# enhance

enhance is an educational RDBMS implementation built from scratch in Rust. The goal is to understand database internals by manually implementing everything from the PostgreSQL wire protocol to the storage engine. This is a learning-focused project, not production software.

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

## Code Style

- Use named module files (`src/foo.rs`) instead of `mod.rs` files
- Add rustdoc comments (`///`) to all public items
- Prefer `Result` over panicking for recoverable errors
- Throughout the codebase, `NOTE:` comments document production improvements that are intentionally deferred to keep the learning implementation minimal

