use enhance::server::Server;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let addr = "127.0.0.1:15432";
    println!("enhance: A From-Scratch RDBMS Implementation");
    println!("Starting on {}", addr);

    let server = Server::new(addr);
    server.run().await?;

    Ok(())
}
