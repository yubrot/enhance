use crate::catalog::CatalogError;
use crate::executor::ExecutorError;
use crate::protocol::ProtocolError;
use crate::tx::TxError;

/// Connection error types.
#[derive(Debug)]
pub enum ConnectionError {
    Io(std::io::Error),
    Protocol(ProtocolError),
    Transaction(TxError),
    Catalog(CatalogError),
    Executor(ExecutorError),
}

impl std::fmt::Display for ConnectionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConnectionError::Io(e) => write!(f, "I/O error: {}", e),
            ConnectionError::Protocol(e) => write!(f, "Protocol error: {}", e),
            ConnectionError::Transaction(e) => write!(f, "Transaction error: {}", e),
            ConnectionError::Catalog(e) => write!(f, "Catalog error: {}", e),
            ConnectionError::Executor(e) => write!(f, "Executor error: {}", e),
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

impl From<TxError> for ConnectionError {
    fn from(e: TxError) -> Self {
        ConnectionError::Transaction(e)
    }
}

impl From<CatalogError> for ConnectionError {
    fn from(e: CatalogError) -> Self {
        ConnectionError::Catalog(e)
    }
}

impl From<ExecutorError> for ConnectionError {
    fn from(e: ExecutorError) -> Self {
        ConnectionError::Executor(e)
    }
}
