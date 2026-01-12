use enhance::server::Server;

// NOTE: Production improvements needed:
// - Use clap or similar for CLI argument parsing (--host, --port, --config)
// - Load configuration from file (e.g., enhance.conf)
// - Initialize structured logging (tracing crate with JSON output)
// - Set up signal handlers for graceful shutdown
// - Daemonization support for background operation
// - PID file management for process supervision

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // NOTE: Production would read from config or environment variables
    let addr = "127.0.0.1:15432";
    println!("enhance: A From-Scratch RDBMS Implementation");
    println!("Starting on {}", addr);

    let server = Server::bind(addr).await?;
    server.serve().await?;

    Ok(())
}
