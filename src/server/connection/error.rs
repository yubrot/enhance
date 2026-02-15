use crate::protocol::ProtocolError;

/// Connection error types.
#[derive(Debug)]
pub enum ConnectionError {
    Io(std::io::Error),
    Protocol(ProtocolError),
}

impl std::fmt::Display for ConnectionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConnectionError::Io(e) => write!(f, "I/O error: {}", e),
            ConnectionError::Protocol(e) => write!(f, "Protocol error: {}", e),
        }
    }
}

impl std::error::Error for ConnectionError {}

impl From<std::io::Error> for ConnectionError {
    fn from(e: std::io::Error) -> Self {
        ConnectionError::Io(e)
    }
}

impl From<ProtocolError> for ConnectionError {
    fn from(e: ProtocolError) -> Self {
        ConnectionError::Protocol(e)
    }
}
