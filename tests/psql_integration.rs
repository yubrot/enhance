mod psql_test_support;

use std::time::{Duration, Instant};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

use psql_test_support::PsqlTestServer;

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_connect_and_quit() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql("\\q\n");
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_multiple_connections() {
    let server = PsqlTestServer::start().await;

    for _ in 0..3 {
        let result = server.run_psql("\\q\n");
        result.assert_success();
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_connection_completes_quickly() {
    let server = PsqlTestServer::start().await;

    let start = Instant::now();
    let result = server.run_psql("\\q\n");
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

    let result = server.run_psql_c("SET client_encoding = 'UTF8';");
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_simple_query() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql_c("SELECT 1;");
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_multiple_queries() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql("SELECT 1; SELECT 2; SELECT 3;\n\\q\n");
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_create_table() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql_c("CREATE TABLE test (id INT);");
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_insert_update_delete() {
    let server = PsqlTestServer::start().await;

    let result = server
        .run_psql("INSERT INTO test VALUES (1); UPDATE test SET id = 2; DELETE FROM test;\n\\q\n");
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_transaction_commands() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql("BEGIN; SELECT 1; COMMIT;\n\\q\n");
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_empty_query() {
    let server = PsqlTestServer::start().await;

    // Empty query should be handled gracefully
    let result = server.run_psql(";\n\\q\n");
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_extended_parse_bind_execute() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql(
        r#"
SELECT $1::int \parse stmt1
\bind_named stmt1 42 \g
\q
"#,
    );
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_extended_rebind_execute() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql(
        r#"
SELECT $1::int \parse stmt1
\bind_named stmt1 1 \g
\bind_named stmt1 2 \g
\bind_named stmt1 3 \g
\q
"#,
    );
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_extended_close_prepared() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql(
        r#"
SELECT 1 \parse stmt1
\close_prepared stmt1
\q
"#,
    );
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_extended_error_recovery() {
    let server = PsqlTestServer::start().await;

    // Cause an error by binding to nonexistent statement,
    // then verify that subsequent commands work after Sync
    let result = server.run_psql(
        r#"
\bind_named nonexistent 42 \g
SELECT 1 \parse stmt1
\bind_named stmt1 \g
\q
"#,
    );
    // The first bind fails with error, but Sync resets error state,
    // so subsequent parse/bind/execute succeed
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_syntax_error_with_position() {
    let server = PsqlTestServer::start().await;

    // Test that syntax errors include position information
    let result = server.run_psql_c("SELECT FROM users;");
    // psql displays position with caret (^) pointing to error location
    result.assert_output_contains(
        "
LINE 1: SELECT FROM users;
               ^",
    );
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_complex_select() {
    let server = PsqlTestServer::start().await;

    // ORDER BY is not yet supported (Step 12), so this should return an error
    let result = server.run_psql_c(
        "SELECT id, name, age FROM users WHERE active = TRUE AND age >= 18 ORDER BY name ASC LIMIT 10;",
    );

    result.assert_output_contains("unsupported");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_select_from_catalog() {
    let server = PsqlTestServer::start().await;

    // Test SELECT * FROM sys_tables returns actual catalog data
    let result = server.run_psql_c("SELECT * FROM sys_tables;");
    result.assert_success();
    result.assert_output_contains("sys_tables");
    result.assert_output_contains("sys_columns");
    result.assert_output_contains("sys_sequences");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_select_with_where() {
    let server = PsqlTestServer::start().await;

    // Test SELECT with WHERE filter
    let result = server.run_psql_c("SELECT table_name FROM sys_tables WHERE table_id = 1;");
    result.assert_success();
    result.assert_output_contains("sys_tables");
    result.assert_output_contains("(1 row)");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_select_expression() {
    let server = PsqlTestServer::start().await;

    // Test SELECT with arithmetic expression (no FROM)
    let result = server.run_psql_c("SELECT 1 + 2;");
    result.assert_success();
    result.assert_output_contains("3");
    result.assert_output_contains("(1 row)");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_select_concat() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql_c("SELECT 'hello' || ' world';");
    result.assert_success();
    result.assert_output_contains("hello world");
    result.assert_output_contains("(1 row)");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_explain_select() {
    let server = PsqlTestServer::start().await;

    // Test EXPLAIN output
    let result = server.run_psql_c("EXPLAIN SELECT * FROM sys_tables;");
    result.assert_success();
    result.assert_output_contains("SeqScan");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_select_table_not_found() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql_c("SELECT * FROM nonexistent;");
    result.assert_output_contains("does not exist");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_comments() {
    let server = PsqlTestServer::start().await;

    // Test that SQL comments are handled correctly
    // SELECT 1+2 evaluates to 3
    let result = server.run_psql_c("SELECT 1 /* this is a comment */ + 2; -- line comment");
    result.assert_success();
    result.assert_output_contains("(1 row)");
}
