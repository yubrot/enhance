//! TCP server for PostgreSQL-compatible connections.
//!
//! This module provides the network layer that accepts client connections
//! and manages their lifecycle using the PostgreSQL wire protocol.
//!
//! ## Architecture
//!
//! ```text
//! +--------+
//! | Server |  <- Accepts TCP connections
//! +--------+
//!      |
//!      v
//! +------------+     +-----------+
//! | Connection | --> | Handshake |  <- SSL/Startup negotiation
//! +------------+     +-----------+
//!      |
//!      v
//! +----------+
//! | Registry |  <- Manages active sessions for cancel requests
//! +----------+
//! ```
//!
//! ## Terminology
//!
//! - **Server**: TCP listener that spawns connections
//! - **Connection**: Per-client session handling query execution
//! - **Handshake**: SSL negotiation and startup parameter exchange
//! - **Registry**: Tracks active connections for cancel request routing

pub mod connection;
pub mod handshake;
pub mod listener;
pub mod registry;

pub use listener::Server;
