mod psql_test_support;

use std::time::{Duration, Instant};

use psql_test_support::PsqlTestServer;

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_connect_and_quit() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql("\\q");
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_query_returns_error() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql("SELECT 1;\\q");
    result.assert_output_contains_any(&["not yet implemented", "Queries not yet implemented"]);
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_multiple_connections() {
    let server = PsqlTestServer::start().await;

    for _ in 0..3 {
        let result = server.run_psql("\\q");
        result.assert_success();
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_connection_completes_quickly() {
    let server = PsqlTestServer::start().await;

    let start = Instant::now();
    let result = server.run_psql("\\q");
    let elapsed = start.elapsed();

    result.assert_success();
    assert!(
        elapsed < Duration::from_secs(3),
        "Connection should complete quickly, took {:?}",
        elapsed
    );
}
