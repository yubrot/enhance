use enhance::engine::Engine;
use enhance::server::Server;
use enhance::storage::MemoryStorage;
use tokio::net::TcpListener;

// NOTE: Production improvements needed:
// - Use clap or similar for CLI argument parsing (--host, --port, --config)
// - Load configuration from file (e.g., enhance.conf)
// - Initialize structured logging (tracing crate with JSON output)
// - Set up signal handlers for graceful shutdown
// - Daemonization support for background operation
// - PID file management for process supervision
// - Support for FileStorage with configurable data directory

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // NOTE: Production would read from config or environment variables
    let addr = "127.0.0.1:15432";
    let pool_size = 1000;

    println!("enhance: A From-Scratch RDBMS Implementation");
    println!("Starting on {}", addr);

    // Initialize storage
    // NOTE: For production, use FileStorage for persistence:
    // let storage = FileStorage::open("enhance.db").await?;
    let storage = MemoryStorage::new();

    // Initialize engine (bootstraps catalog if new)
    let engine = Engine::open(storage, pool_size).await?;

    // Bind listener
    let listener = TcpListener::bind(addr).await?;

    // Create and run server
    let server = Server::new(listener, engine);
    server.serve().await?;

    Ok(())
}
