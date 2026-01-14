/// Protocol parsing errors
#[derive(Debug)]
pub enum ProtocolError {
    InsufficientData,
    InvalidMessage,
    UnsupportedProtocolVersion(i32),
    MissingParameter(&'static str),
    InvalidUtf8,
    UnknownMessageType(u8),
    Io(std::io::Error),
}

impl std::fmt::Display for ProtocolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProtocolError::InsufficientData => write!(f, "insufficient data"),
            ProtocolError::InvalidMessage => write!(f, "invalid message"),
            ProtocolError::UnsupportedProtocolVersion(v) => {
                write!(f, "unsupported protocol version: {}", v)
            }
            ProtocolError::MissingParameter(p) => write!(f, "missing parameter: {}", p),
            ProtocolError::InvalidUtf8 => write!(f, "invalid UTF-8"),
            ProtocolError::UnknownMessageType(t) => {
                write!(f, "unknown message type: 0x{:02x}", t)
            }
            ProtocolError::Io(e) => write!(f, "I/O error: {}", e),
        }
    }
}

impl std::error::Error for ProtocolError {}

impl From<std::io::Error> for ProtocolError {
    fn from(e: std::io::Error) -> Self {
        ProtocolError::Io(e)
    }
}
