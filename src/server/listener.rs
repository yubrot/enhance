use std::sync::Arc;
use std::sync::atomic::{AtomicI32, Ordering};

use tokio::net::TcpListener;

use crate::server::connection::Connection;

/// TCP server implementing PostgreSQL wire protocol.
pub struct Server {
    addr: String,
    /// Next process ID (NOTE: This server does not actually fork a process)
    next_process_id: Arc<AtomicI32>,
}

impl Server {
    pub fn new(addr: impl Into<String>) -> Self {
        Self {
            addr: addr.into(),
            next_process_id: Arc::new(AtomicI32::new(1)),
        }
    }

    pub async fn run(&self) -> Result<(), std::io::Error> {
        let listener = TcpListener::bind(&self.addr).await?;
        println!("enhance: listening on {}", self.addr);

        // NOTE: This is a minimal implementation suitable for learning/development.
        // For production use, the following improvements would be necessary:
        //
        // 1. Graceful Shutdown:
        //    - Use tokio::signal to handle SIGINT/SIGTERM
        //    - Use tokio::sync::broadcast to notify all connections
        //    - Wait for active connections to finish (with timeout)
        //
        // 2. Connection Limiting:
        //    - Use tokio::sync::Semaphore to limit concurrent connections
        //    - Reject new connections when limit is reached (prevent resource exhaustion)
        //
        // 3. Better Error Handling:
        //    - Don't propagate accept() errors immediately (may be transient)
        //    - Log errors and continue accepting (e.g., EMFILE can recover)
        //    - Use exponential backoff on repeated failures
        //
        // 4. Resource Management:
        //    - Track spawned tasks (e.g., JoinSet) to prevent leaks
        //    - Set TCP socket options (SO_KEEPALIVE, TCP_NODELAY)
        //    - Implement connection timeouts
        //
        // 5. Observability:
        //    - Replace println! with proper structured logging (tracing crate)
        //    - Expose metrics (active connections, total accepted, errors)
        //    - Add health check endpoint

        loop {
            let (socket, peer_addr) = listener.accept().await?;
            let process_id = self.next_process_id.fetch_add(1, Ordering::SeqCst);

            println!(
                "Accepted connection from {} (pid={})",
                peer_addr, process_id
            );

            // NOTE: Spawned task is detached - no tracking of completion
            // Production: Use JoinSet or similar to track and await all tasks on shutdown
            tokio::spawn(async move {
                let mut connection = Connection::new(socket, process_id);
                if let Err(e) = connection.run().await {
                    eprintln!("Connection error (pid={}): {}", process_id, e);
                }
                println!("Connection closed (pid={})", process_id);
            });
        }
    }
}
