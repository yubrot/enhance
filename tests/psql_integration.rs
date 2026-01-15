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

#[tokio::test(flavor = "multi_thread")]
async fn test_extended_query_protocol() {
    let server = PsqlTestServer::start().await;
    let mut stream = server.connect().await;

    // Startup handshake
    stream.write_i32(23).await.unwrap();
    stream.write_i32(3 << 16).await.unwrap();
    stream.write_all(b"user\0postgres\0\0").await.unwrap();

    // Wait for ReadyForQuery
    loop {
        let tag = stream.read_u8().await.unwrap();
        let len = stream.read_i32().await.unwrap();
        let mut body = vec![0u8; (len - 4) as usize];
        if !body.is_empty() {
            stream.read_exact(&mut body).await.unwrap();
        }
        if tag == b'Z' {
            break;
        }
    }

    // Send Parse message: unnamed statement, "SELECT 1", no params
    stream.write_u8(b'P').await.unwrap(); // Parse
    stream.write_i32(4 + 1 + 9 + 2).await.unwrap(); // length
    stream.write_all(b"\0").await.unwrap(); // statement name (unnamed)
    stream.write_all(b"SELECT 1\0").await.unwrap(); // query
    stream.write_i16(0).await.unwrap(); // param count

    // Send Bind message: unnamed portal to unnamed statement
    stream.write_u8(b'B').await.unwrap(); // Bind
    stream.write_i32(4 + 1 + 1 + 2 + 2 + 2).await.unwrap(); // length
    stream.write_all(b"\0").await.unwrap(); // portal name (unnamed)
    stream.write_all(b"\0").await.unwrap(); // statement name (unnamed)
    stream.write_i16(0).await.unwrap(); // format code count
    stream.write_i16(0).await.unwrap(); // param count
    stream.write_i16(0).await.unwrap(); // result format count

    // Send Execute message: unnamed portal, all rows
    stream.write_u8(b'E').await.unwrap(); // Execute
    stream.write_i32(4 + 1 + 4).await.unwrap(); // length
    stream.write_all(b"\0").await.unwrap(); // portal name (unnamed)
    stream.write_i32(0).await.unwrap(); // max rows (0 = all)

    // Send Sync message
    stream.write_u8(b'S').await.unwrap(); // Sync
    stream.write_i32(4).await.unwrap(); // length (no body)

    stream.flush().await.unwrap();

    // Read responses
    let mut got_parse_complete = false;
    let mut got_bind_complete = false;
    let mut got_command_complete = false;
    let mut got_ready = false;

    while !got_ready {
        let tag = stream.read_u8().await.unwrap();
        let len = stream.read_i32().await.unwrap();
        let mut body = vec![0u8; (len - 4) as usize];
        if !body.is_empty() {
            stream.read_exact(&mut body).await.unwrap();
        }

        match tag {
            b'1' => got_parse_complete = true,
            b'2' => got_bind_complete = true,
            b'C' => got_command_complete = true,
            b'Z' => got_ready = true,
            b'E' => {
                let error_msg = String::from_utf8_lossy(&body);
                panic!("Received error: {:?}", error_msg)
            }
            _ => {}
        }
    }

    assert!(got_parse_complete, "Should receive ParseComplete");
    assert!(got_bind_complete, "Should receive BindComplete");
    assert!(got_command_complete, "Should receive CommandComplete");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_extended_query_describe() {
    let server = PsqlTestServer::start().await;
    let mut stream = server.connect().await;

    // Startup handshake
    stream.write_i32(23).await.unwrap();
    stream.write_i32(3 << 16).await.unwrap();
    stream.write_all(b"user\0postgres\0\0").await.unwrap();

    // Wait for ReadyForQuery
    loop {
        let tag = stream.read_u8().await.unwrap();
        let len = stream.read_i32().await.unwrap();
        let mut body = vec![0u8; (len - 4) as usize];
        if !body.is_empty() {
            stream.read_exact(&mut body).await.unwrap();
        }
        if tag == b'Z' {
            break;
        }
    }

    // Parse a statement with params
    stream.write_u8(b'P').await.unwrap();
    stream.write_i32(4 + 6 + 18 + 2 + 4 + 4).await.unwrap(); // length
    stream.write_all(b"test\0").await.unwrap(); // statement name
    stream.write_all(b"SELECT $1, $2\0").await.unwrap(); // query
    stream.write_i16(2).await.unwrap(); // param count
    stream.write_i32(23).await.unwrap(); // INT4
    stream.write_i32(25).await.unwrap(); // TEXT

    // Describe the statement
    stream.write_u8(b'D').await.unwrap(); // Describe
    stream.write_i32(4 + 1 + 5).await.unwrap(); // length
    stream.write_u8(b'S').await.unwrap(); // type: Statement
    stream.write_all(b"test\0").await.unwrap(); // name

    // Send Sync
    stream.write_u8(b'S').await.unwrap();
    stream.write_i32(4).await.unwrap();

    stream.flush().await.unwrap();

    // Read responses
    let mut got_parse_complete = false;
    let mut got_parameter_description = false;
    let mut got_no_data = false;

    loop {
        let tag = stream.read_u8().await.unwrap();
        let len = stream.read_i32().await.unwrap();
        let mut body = vec![0u8; (len - 4) as usize];
        if !body.is_empty() {
            stream.read_exact(&mut body).await.unwrap();
        }

        match tag {
            b'1' => got_parse_complete = true,
            b't' => {
                got_parameter_description = true;
                // Verify parameter types
                let param_count = i16::from_be_bytes([body[0], body[1]]);
                assert_eq!(param_count, 2, "Should have 2 parameters");
                let param1_oid = i32::from_be_bytes([body[2], body[3], body[4], body[5]]);
                let param2_oid = i32::from_be_bytes([body[6], body[7], body[8], body[9]]);
                assert_eq!(param1_oid, 23, "First param should be INT4");
                assert_eq!(param2_oid, 25, "Second param should be TEXT");
            }
            b'n' => got_no_data = true,
            b'Z' => break,
            b'E' => {
                let error_msg = String::from_utf8_lossy(&body);
                panic!("Received error: {:?}", error_msg)
            }
            _ => {}
        }
    }

    assert!(got_parse_complete, "Should receive ParseComplete");
    assert!(
        got_parameter_description,
        "Should receive ParameterDescription"
    );
    assert!(got_no_data, "Should receive NoData");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_extended_query_close() {
    let server = PsqlTestServer::start().await;
    let mut stream = server.connect().await;

    // Startup handshake
    stream.write_i32(23).await.unwrap();
    stream.write_i32(3 << 16).await.unwrap();
    stream.write_all(b"user\0postgres\0\0").await.unwrap();

    // Wait for ReadyForQuery
    loop {
        let tag = stream.read_u8().await.unwrap();
        let len = stream.read_i32().await.unwrap();
        let mut body = vec![0u8; (len - 4) as usize];
        if !body.is_empty() {
            stream.read_exact(&mut body).await.unwrap();
        }
        if tag == b'Z' {
            break;
        }
    }

    // Parse a statement
    stream.write_u8(b'P').await.unwrap();
    stream.write_i32(4 + 6 + 9 + 2).await.unwrap();
    stream.write_all(b"stmt\0").await.unwrap();
    stream.write_all(b"SELECT 1\0").await.unwrap();
    stream.write_i16(0).await.unwrap();

    // Close the statement
    stream.write_u8(b'C').await.unwrap(); // Close
    stream.write_i32(4 + 1 + 5).await.unwrap(); // length
    stream.write_u8(b'S').await.unwrap(); // type: Statement
    stream.write_all(b"stmt\0").await.unwrap(); // name

    // Send Sync
    stream.write_u8(b'S').await.unwrap();
    stream.write_i32(4).await.unwrap();

    stream.flush().await.unwrap();

    // Read responses
    let mut got_parse_complete = false;
    let mut got_close_complete = false;

    loop {
        let tag = stream.read_u8().await.unwrap();
        let len = stream.read_i32().await.unwrap();
        let mut body = vec![0u8; (len - 4) as usize];
        if !body.is_empty() {
            stream.read_exact(&mut body).await.unwrap();
        }

        match tag {
            b'1' => got_parse_complete = true,
            b'3' => got_close_complete = true,
            b'Z' => break,
            b'E' => {
                let error_msg = String::from_utf8_lossy(&body);
                panic!("Received error: {:?}", error_msg)
            }
            _ => {}
        }
    }

    assert!(got_parse_complete, "Should receive ParseComplete");
    assert!(got_close_complete, "Should receive CloseComplete");
}
