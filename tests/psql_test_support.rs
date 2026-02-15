//! Test utilities for psql integration tests.
//!
//! Provides a simple interface for setting up a test server and running psql commands.

use std::process::{Command, Stdio};

use tokio::net::TcpListener;
use tokio::task::JoinHandle;

use enhance::engine::Engine;
use enhance::server::Server;
use enhance::storage::MemoryStorage;

/// Result of running a psql command.
#[derive(Debug)]
pub struct PsqlOutput {
    /// Combined stdout/stderr output.
    pub output: String,
    /// Exit code of the psql process.
    pub exit_code: i32,
}

impl PsqlOutput {
    /// Asserts that psql exited successfully (exit code 0).
    pub fn assert_success(&self) {
        assert_eq!(
            self.exit_code, 0,
            "psql should exit cleanly. output: {}",
            self.output
        );
    }

    /// Asserts that the output contains the given substring.
    pub fn assert_output_contains(&self, expected: &str) {
        assert!(
            self.output.contains(expected),
            "output should contain '{}': {}",
            expected,
            self.output
        );
    }
}

/// A test server wrapper that handles setup and teardown.
///
/// The server is started when created and automatically aborted when dropped.
pub struct PsqlTestServer {
    port: u16,
    handle: JoinHandle<()>,
}

impl PsqlTestServer {
    /// Starts a new test server on an available port.
    pub async fn start() -> Self {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let port = listener.local_addr().unwrap().port();

        // Initialize engine with in-memory storage
        let storage = MemoryStorage::new();
        let engine = Engine::open(storage, 100).await.unwrap();

        let server = Server::new(listener, engine);
        let handle = tokio::spawn(async move {
            let _ = server.serve().await;
        });

        Self { port, handle }
    }

    /// Runs psql with input piped to stdin for meta-commands
    /// (`\parse`, `\bind_named`, etc.) that require interactive mode.
    pub fn run_psql(&self, input: &str) -> PsqlOutput {
        let mut child = Command::new("psql")
            .args([
                "-h",
                "127.0.0.1",
                "-p",
                &self.port.to_string(),
                "-U",
                "postgres",
            ])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("Failed to execute psql");

        if let Some(mut stdin) = child.stdin.take() {
            use std::io::Write;
            stdin.write_all(input.as_bytes()).unwrap();
        }

        let output = child.wait_with_output().expect("Failed to wait on psql");

        let combined = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );

        PsqlOutput {
            output: combined,
            exit_code: output.status.code().unwrap_or(-1),
        }
    }

    /// Runs psql with the given query using `-c` flag and returns the result.
    pub fn run_psql_c(&self, query: &str) -> PsqlOutput {
        let output = Command::new("psql")
            .args([
                "-h",
                "127.0.0.1",
                "-p",
                &self.port.to_string(),
                "-U",
                "postgres",
                "-c",
                query,
            ])
            .output()
            .expect("Failed to execute psql");

        let combined = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );

        PsqlOutput {
            output: combined,
            exit_code: output.status.code().unwrap_or(-1),
        }
    }

    /// Connects to the test server using a `TcpStream`.
    pub async fn connect(&self) -> tokio::net::TcpStream {
        tokio::net::TcpStream::connect(format!("127.0.0.1:{}", self.port))
            .await
            .unwrap()
    }
}

impl Drop for PsqlTestServer {
    fn drop(&mut self) {
        self.handle.abort();
    }
}
