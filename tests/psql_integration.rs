mod psql_test_support;

use std::time::{Duration, Instant};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

use psql_test_support::PsqlTestServer;

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_connect_and_quit() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql("\\q");
    result.assert_success();
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

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_cancel_request() {
    let server = PsqlTestServer::start().await;

    // 1. First connection: Start and get PID/Secret
    let mut stream1 = server.connect().await;

    // Send StartupMessage: length(23) + version(3.0) + user(postgres) + \0\0
    stream1.write_i32(23).await.unwrap(); // Total length
    stream1.write_i32(3 << 16).await.unwrap(); // Protocol version 3.0
    stream1.write_all(b"user\0postgres\0\0").await.unwrap();

    // Read responses until we get BackendKeyData ('K')
    let mut pid = 0;
    let mut secret = 0;
    loop {
        let tag = stream1.read_u8().await.unwrap();
        let len = stream1.read_i32().await.unwrap();
        let body_len = (len - 4) as usize;
        let mut body = vec![0u8; body_len];
        stream1.read_exact(&mut body).await.unwrap();

        if tag == b'K' {
            pid = i32::from_be_bytes(body[0..4].try_into().unwrap());
            secret = i32::from_be_bytes(body[4..8].try_into().unwrap());
        }
        if tag == b'Z' {
            break;
        } // ReadyForQuery
    }

    assert!(pid != 0, "Should have received PID");

    // 2. Second connection: Send CancelRequest
    let mut stream2 = server.connect().await;
    // length(16) + code(80877102) + pid + secret
    stream2.write_i32(16).await.unwrap();
    stream2.write_i32(80877102).await.unwrap();
    stream2.write_i32(pid).await.unwrap();
    stream2.write_i32(secret).await.unwrap();
    stream2.flush().await.unwrap();

    // 3. Verify stream1 is closed/cancelled
    // In our implementation, stream1 should close when it receives the cancellation signal.
    let mut buf = [0u8; 1];
    let res = tokio::time::timeout(Duration::from_secs(1), stream1.read(&mut buf)).await;
    match res {
        Ok(Ok(0)) => {} // EOF - closed as expected
        Ok(Ok(_)) => panic!("Stream should have been closed"),
        Ok(Err(_)) => {} // Error is also fine (e.g. connection reset)
        Err(_) => panic!("Timed out waiting for connection to close"),
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_set_command() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql("SET client_encoding = 'UTF8';\\q");
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_simple_query() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql("SELECT 1;\\q");
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_multiple_queries() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql("SELECT 1; SELECT 2; SELECT 3;\\q");
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_create_table() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql("CREATE TABLE test (id INT);\\q");
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_insert_update_delete() {
    let server = PsqlTestServer::start().await;

    let result = server
        .run_psql("INSERT INTO test VALUES (1); UPDATE test SET id = 2; DELETE FROM test;\\q");
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_transaction_commands() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql("BEGIN; SELECT 1; COMMIT;\\q");
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_empty_query() {
    let server = PsqlTestServer::start().await;

    // Empty query should be handled gracefully
    let result = server.run_psql(";\\q");
    result.assert_success();
}
