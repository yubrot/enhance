use std::sync::Arc;
use std::sync::atomic::{AtomicI32, Ordering};

use tokio::net::TcpListener;

use crate::engine::Engine;
use crate::server::connection::Connection;
use crate::server::handshake::{Handshake, HandshakeResult};
use crate::server::registry::Registry;
use crate::storage::{Replacer, Storage};

/// TCP server implementing PostgreSQL wire protocol.
pub struct Server<S: Storage, R: Replacer> {
    listener: TcpListener,
    next_pid: Arc<AtomicI32>,
    registry: Arc<Registry>,
    engine: Arc<Engine<S, R>>,
}

impl<S: Storage + 'static, R: Replacer + 'static> Server<S, R> {
    /// Creates a new server with a given listener and engine.
    pub fn new(listener: TcpListener, engine: Arc<Engine<S, R>>) -> Self {
        Self {
            listener,
            next_pid: Arc::new(AtomicI32::new(1)),
            registry: Arc::new(Registry::new()),
            engine,
        }
    }

    /// Starts accepting connections and serving clients.
    pub async fn serve(self) -> Result<(), std::io::Error> {
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
            let (socket, peer_addr) = self.listener.accept().await?;
            let pid = self.next_pid.fetch_add(1, Ordering::SeqCst);
            let registry = self.registry.clone();
            let engine = self.engine.clone();

            println!("(pid={}) Accepted connection from {}", pid, peer_addr);

            tokio::spawn(async move {
                let handshake = Handshake::new(socket, pid);
                let (mut connection, secret_key) = match handshake.run().await {
                    Ok(HandshakeResult::Success { framed, secret_key }) => {
                        println!("(pid={}) Connection ready", pid);
                        (Connection::new(framed, pid, engine), secret_key)
                    }
                    Ok(HandshakeResult::CancelRequested {
                        pid: target_pid,
                        secret_key,
                    }) => {
                        println!("(pid={}) Cancel request: target_pid={}", pid, target_pid);
                        registry.cancel(target_pid, secret_key);
                        println!("(pid={}) Connection closed", pid);
                        return;
                    }
                    Err(e) => {
                        eprintln!("(pid={}) Handshake error: {}", pid, e);
                        return;
                    }
                };

                let cancel_token = registry.register(pid, secret_key);
                if let Err(e) = connection.run(cancel_token).await {
                    eprintln!("(pid={}) Connection error: {}", pid, e);
                }
                registry.unregister(pid);
                println!("(pid={}) Connection closed", pid);
            });
        }
    }
}
