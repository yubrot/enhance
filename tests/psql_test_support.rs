//! Test utilities for psql integration tests.
//!
//! Provides a simple interface for setting up a test server and running psql commands.

use std::process::Command;
use std::time::Duration;

use tokio::net::{TcpListener, TcpStream};
use tokio::task::JoinHandle;

use enhance::server::Server;

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
    #[allow(dead_code)]
    pub fn assert_output_contains(&self, expected: &str) {
        assert!(
            self.output.contains(expected),
            "output should contain '{}': {}",
            expected,
            self.output
        );
    }

    /// Asserts that the output contains any of the given substrings.
    pub fn assert_output_contains_any(&self, expected: &[&str]) {
        let found = expected.iter().any(|s| self.output.contains(s));
        assert!(
            found,
            "output should contain one of {:?}: {}",
            expected, self.output
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
    ///
    /// Waits for the server to be ready before returning.
    pub async fn start() -> Self {
        let port = Self::find_available_port().await;
        let addr = format!("127.0.0.1:{}", port);

        let server = Server::new(&addr);
        let handle = tokio::spawn(async move {
            let _ = server.run().await;
        });

        // Wait for server to accept connections
        Self::wait_for_server(port).await;

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

    /// Finds an available port by binding to port 0.
    async fn find_available_port() -> u16 {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        listener.local_addr().unwrap().port()
    }

    /// Waits for the server to accept TCP connections.
    async fn wait_for_server(port: u16) {
        let addr = format!("127.0.0.1:{}", port);
        for _ in 0..50 {
            if TcpStream::connect(&addr).await.is_ok() {
                return;
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
        panic!("Server did not become ready within 500ms");
    }
}

impl Drop for PsqlTestServer {
    fn drop(&mut self) {
        self.handle.abort();
    }
}
