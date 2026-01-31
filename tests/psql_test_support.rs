//! Test utilities for psql integration tests.
//!
//! Provides a simple interface for setting up a test server and running psql commands.

use std::process::Command;

use tokio::net::TcpListener;
use tokio::task::JoinHandle;

use enhance::db::Database;
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

        // Initialize database with in-memory storage
        let storage = MemoryStorage::new();
        let database = Database::open(storage, 100).await.unwrap();

        let server = Server::new(listener, database);
        let handle = tokio::spawn(async move {
            let _ = server.serve().await;
        });

        Self { port, handle }
    }

    /// Runs psql with the given input and returns the result.
    ///
    /// The input is piped to psql's stdin.
    pub fn run_psql(&self, input: &str) -> PsqlOutput {
        let output = Command::new("sh")
            .arg("-c")
            .arg(format!(
                "echo '{}' | psql -h 127.0.0.1 -p {} -U postgres 2>&1",
                input, self.port
            ))
            .output()
            .expect("Failed to execute psql");

        PsqlOutput {
            output: String::from_utf8_lossy(&output.stdout).to_string(),
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
