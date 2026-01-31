//! PostgreSQL wire protocol implementation.
//!
//! This module implements the PostgreSQL v3.0 wire protocol, enabling
//! communication with standard PostgreSQL clients like `psql`. Both Simple
//! Query and Extended Query protocols are supported.
//!
//! ## Architecture
//!
//! ```text
//! +----------+                           +----------+
//! |  Client  |  --- FrontendMessage -->  |  Server  |
//! |  (psql)  |  <-- BackendMessage  ---  | (enhance)|
//! +----------+                           +----------+
//!               ^                   ^
//!               |   PostgresCodec   |
//!               +-------------------+
//! ```
//!
//! ## Terminology
//!
//! - **FrontendMessage**: Messages from client to server (Query, Parse, Bind, etc.)
//! - **StartupMessage**: Special frontend messages for connection handshake (SSL, Startup, Cancel)
//! - **BackendMessage**: Messages from server to client (RowDescription, DataRow, etc.)
//! - **Codec**: Framing and serialization for the wire protocol

pub mod backend;
pub mod codec;
pub mod error;
pub mod frontend;
pub mod types;

pub use backend::{
    BackendMessage, DataValue, ErrorField, ErrorInfo, FieldDescription, TransactionStatus,
    sql_state,
};
pub use codec::{PostgresCodec, StartupCodec};
pub use error::ProtocolError;
pub use frontend::{
    BindMessage, CloseMessage, CloseTarget, DescribeMessage, DescribeTarget, ExecuteMessage,
    FrontendMessage, ParseMessage, StartupMessage, StartupParameters,
};
pub use types::{ErrorFieldCode, FormatCode, type_oid};
