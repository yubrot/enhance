use std::process::Command;
use std::time::Duration;

use tokio::net::TcpListener;

use enhance::server::Server;

/// Find an available port by binding to port 0.
async fn find_available_port() -> u16 {
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    listener.local_addr().unwrap().port()
}

/// Run psql and return (stdout, stderr, exit_code).
/// Uses echo to pipe commands to psql's stdin.
fn run_psql_with_input(port: u16, input: &str) -> (String, String, i32) {
    let output = Command::new("sh")
        .arg("-c")
        .arg(format!(
            "echo '{}' | psql -h 127.0.0.1 -p {} -U postgres 2>&1",
            input, port
        ))
        .output()
        .expect("Failed to execute psql");

    (
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::new(), // stderr is redirected to stdout with 2>&1
        output.status.code().unwrap_or(-1),
    )
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_connect_and_quit() {
    let port = find_available_port().await;
    let addr = format!("127.0.0.1:{}", port);

    // Start server in background
    let server = Server::new(&addr);
    let server_handle = tokio::spawn(async move {
        let _ = server.run().await;
    });

    // Wait for server to be ready
    tokio::time::sleep(Duration::from_millis(200)).await;

    // Run psql with \q to quit immediately
    let (output, _, exit_code) = run_psql_with_input(port, "\\q");

    // Should exit cleanly
    assert_eq!(exit_code, 0, "psql should exit cleanly. output: {}", output);

    // Cleanup
    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_query_returns_error() {
    let port = find_available_port().await;
    let addr = format!("127.0.0.1:{}", port);

    // Start server
    let server = Server::new(&addr);
    let server_handle = tokio::spawn(async move {
        let _ = server.run().await;
    });

    tokio::time::sleep(Duration::from_millis(200)).await;

    // Run psql with a query - should get "not yet implemented" error
    let (output, _, _exit_code) = run_psql_with_input(port, "SELECT 1;\\q");

    // Output should contain our error message
    assert!(
        output.contains("not yet implemented") || output.contains("Queries not yet implemented"),
        "output should contain 'not yet implemented': {}",
        output
    );

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_multiple_connections() {
    let port = find_available_port().await;
    let addr = format!("127.0.0.1:{}", port);

    // Start server
    let server = Server::new(&addr);
    let server_handle = tokio::spawn(async move {
        let _ = server.run().await;
    });

    tokio::time::sleep(Duration::from_millis(200)).await;

    // Connect multiple times sequentially
    for i in 0..3 {
        let (output, _, exit_code) = run_psql_with_input(port, "\\q");
        assert_eq!(
            exit_code, 0,
            "Connection {} should succeed. output: {}",
            i, output
        );
    }

    server_handle.abort();
    let _ = server_handle.await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_connection_completes_quickly() {
    let port = find_available_port().await;
    let addr = format!("127.0.0.1:{}", port);

    // Start server
    let server = Server::new(&addr);
    let server_handle = tokio::spawn(async move {
        let _ = server.run().await;
    });

    tokio::time::sleep(Duration::from_millis(200)).await;

    // Test that connection completes within reasonable time
    let start = std::time::Instant::now();
    let (output, _, exit_code) = run_psql_with_input(port, "\\q");
    let elapsed = start.elapsed();

    assert_eq!(
        exit_code, 0,
        "Connection should succeed. output: {}",
        output
    );
    assert!(
        elapsed < Duration::from_secs(3),
        "Connection should complete quickly, took {:?}",
        elapsed
    );

    server_handle.abort();
    let _ = server_handle.await;
}
