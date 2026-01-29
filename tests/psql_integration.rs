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

    // Create table, insert, update, delete with RETURNING
    let result = server.run_psql(
        "CREATE TABLE dml_test (id SERIAL, name TEXT, age INTEGER); \
         INSERT INTO dml_test (name, age) VALUES ('Alice', 30) RETURNING id, name; \
         UPDATE dml_test SET age = 31 WHERE name = 'Alice' RETURNING *; \
         DELETE FROM dml_test WHERE id = 1 RETURNING name; \
         \\q",
    );
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

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_extended_parse_bind_execute() {
    let server = PsqlTestServer::start().await;

    let result = server.run_psql(
        r#"
SELECT $1::int \parse stmt1
\bind_named stmt1 42 \g
\q"#,
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
\q"#,
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
\q"#,
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
\q"#,
    );
    // The first bind fails with error, but Sync resets error state,
    // so subsequent parse/bind/execute succeed
    result.assert_success();
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_syntax_error_with_position() {
    let server = PsqlTestServer::start().await;

    // Test that syntax errors include position information
    let result = server.run_psql(r#"SELECT FROM "users";"#);
    // psql displays position with caret (^) pointing to error location
    result.assert_output_contains(
        r#"
LINE 1: SELECT FROM "users";
               ^"#,
    );
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_complex_select() {
    let server = PsqlTestServer::start().await;

    // LIMIT is not yet supported
    // Test that we correctly report unsupported features
    let result = server.run_psql(
        "SELECT id, name, age FROM users WHERE active = TRUE AND age >= 18 ORDER BY name ASC LIMIT 10;",
    );
    result.assert_output_contains("unsupported feature: LIMIT");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_comments() {
    let server = PsqlTestServer::start().await;

    // Test that SQL comments are parsed correctly.
    // Note: SELECT without FROM is not supported (we require a table).
    let result = server.run_psql("SELECT 1 /* this is a comment */ + 2; -- line comment");
    result.assert_output_contains("unsupported feature: SELECT without FROM");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_basic_select() {
    let server = PsqlTestServer::start().await;

    // Create a table and select from it
    let result = server.run_psql("CREATE TABLE test_select (id INTEGER, name TEXT);");
    result.assert_success();
    result.assert_output_contains("CREATE TABLE");

    // SELECT * from empty table should return 0 rows
    let result = server.run_psql("SELECT * FROM test_select;");
    result.assert_success();
    result.assert_output_contains("(0 rows)");

    // SELECT with WHERE clause from empty table
    let result = server.run_psql("SELECT id, name FROM test_select WHERE id > 0;");
    result.assert_success();
    result.assert_output_contains("(0 rows)");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_select_from_catalog() {
    let server = PsqlTestServer::start().await;

    // Select from system catalog table
    let result = server.run_psql("SELECT * FROM sys_tables;");
    result.assert_success();
    // Should show the 3 system catalog tables
    result.assert_output_contains("sys_tables");
    result.assert_output_contains("sys_columns");
    result.assert_output_contains("sys_sequences");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_explain() {
    let server = PsqlTestServer::start().await;

    // Create a table and EXPLAIN a query
    let result = server.run_psql("CREATE TABLE test_explain (id INTEGER, name TEXT);");
    result.assert_success();

    let result = server.run_psql("EXPLAIN SELECT * FROM test_explain;");
    result.assert_success();
    result.assert_output_contains("Seq Scan on test_explain");

    // EXPLAIN with WHERE clause shows Filter
    let result = server.run_psql("EXPLAIN SELECT * FROM test_explain WHERE id > 5;");
    result.assert_success();
    result.assert_output_contains("Filter");
    result.assert_output_contains("Seq Scan on test_explain");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_order_by() {
    let server = PsqlTestServer::start().await;

    // Create and populate a table with only integers (to avoid shell escaping issues with strings)
    let result = server.run_psql("CREATE TABLE test_sort (id INTEGER, value INTEGER);");
    result.assert_success();

    let result = server.run_psql("INSERT INTO test_sort VALUES (3, 30);");
    result.assert_success();

    let result = server.run_psql("INSERT INTO test_sort VALUES (1, 10);");
    result.assert_success();

    let result = server.run_psql("INSERT INTO test_sort VALUES (2, 20);");
    result.assert_success();

    // ORDER BY ASC - values should be ordered 10, 20, 30
    let result = server.run_psql("SELECT * FROM test_sort ORDER BY id ASC;");
    result.assert_success();
    result.assert_output_contains("(3 rows)");
    // Verify values are present
    result.assert_output_contains("10");
    result.assert_output_contains("20");
    result.assert_output_contains("30");
    // Verify order: 10 appears before 20 before 30
    let output = &result.output;
    let pos_10 = output.find(" 10").expect("10 should be in output");
    let pos_20 = output.find(" 20").expect("20 should be in output");
    let pos_30 = output.find(" 30").expect("30 should be in output");
    assert!(
        pos_10 < pos_20 && pos_20 < pos_30,
        "ASC order incorrect: 10={}, 20={}, 30={}\nOutput: {}",
        pos_10, pos_20, pos_30, output
    );

    // ORDER BY DESC - values should be ordered 30, 20, 10
    let result = server.run_psql("SELECT * FROM test_sort ORDER BY id DESC;");
    result.assert_success();
    let output = &result.output;
    let pos_10 = output.find(" 10").expect("10 should be in output");
    let pos_20 = output.find(" 20").expect("20 should be in output");
    let pos_30 = output.find(" 30").expect("30 should be in output");
    assert!(
        pos_30 < pos_20 && pos_20 < pos_10,
        "DESC order incorrect: 30={}, 20={}, 10={}\nOutput: {}",
        pos_30, pos_20, pos_10, output
    );
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_aggregate_functions() {
    let server = PsqlTestServer::start().await;

    // Create and populate a table
    let result = server.run_psql("CREATE TABLE test_agg (id INTEGER, value INTEGER);");
    result.assert_success();

    let result = server.run_psql("INSERT INTO test_agg VALUES (1, 10);");
    result.assert_success();

    let result = server.run_psql("INSERT INTO test_agg VALUES (2, 20);");
    result.assert_success();

    let result = server.run_psql("INSERT INTO test_agg VALUES (3, 30);");
    result.assert_success();

    // COUNT(*)
    let result = server.run_psql("SELECT COUNT(*) FROM test_agg;");
    result.assert_success();
    result.assert_output_contains("3");

    // SUM
    let result = server.run_psql("SELECT SUM(value) FROM test_agg;");
    result.assert_success();
    result.assert_output_contains("60");

    // AVG
    let result = server.run_psql("SELECT AVG(value) FROM test_agg;");
    result.assert_success();
    result.assert_output_contains("20");

    // MIN/MAX
    let result = server.run_psql("SELECT MIN(value), MAX(value) FROM test_agg;");
    result.assert_success();
    result.assert_output_contains("10");
    result.assert_output_contains("30");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psql_group_by() {
    let server = PsqlTestServer::start().await;

    // Create and populate a table with groups (use integer for dept to avoid shell escaping)
    let result = server.run_psql("CREATE TABLE test_group (dept INTEGER, salary INTEGER);");
    result.assert_success();

    // dept 1 = 50000 + 60000 = 110000
    let result = server.run_psql("INSERT INTO test_group VALUES (1, 50000);");
    result.assert_success();

    let result = server.run_psql("INSERT INTO test_group VALUES (1, 60000);");
    result.assert_success();

    // dept 2 = 80000 + 90000 = 170000
    let result = server.run_psql("INSERT INTO test_group VALUES (2, 80000);");
    result.assert_success();

    let result = server.run_psql("INSERT INTO test_group VALUES (2, 90000);");
    result.assert_success();

    // GROUP BY with aggregate
    let result = server.run_psql("SELECT dept, SUM(salary) FROM test_group GROUP BY dept;");
    result.assert_success();
    result.assert_output_contains("(2 rows)");
    // Check for expected sum values
    result.assert_output_contains("110000");
    result.assert_output_contains("170000");
}
