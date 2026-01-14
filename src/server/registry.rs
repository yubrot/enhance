use std::collections::HashMap;
use std::sync::Mutex;
use tokio_util::sync::CancellationToken;

/// A registry of active backend connections.
///
/// This is used to look up connections for query cancellation and other
/// inter-connection communication.
pub struct Registry {
    // pid -> ConnectionHandle
    // NOTE: Consider DashMap?
    connections: Mutex<HashMap<i32, ConnectionHandle>>,
}

struct ConnectionHandle {
    secret_key: i32,
    cancel_token: CancellationToken,
}

impl Default for Registry {
    fn default() -> Self {
        Self::new()
    }
}

impl Registry {
    pub fn new() -> Self {
        Self {
            connections: Mutex::new(HashMap::new()),
        }
    }

    /// Registers a new connection and returns a cancellation token for it.
    pub fn register(&self, pid: i32, secret_key: i32) -> CancellationToken {
        let token = CancellationToken::new();
        self.connections.lock().expect("mutex poisoned").insert(
            pid,
            ConnectionHandle {
                secret_key,
                cancel_token: token.clone(),
            },
        );
        token
    }

    /// Unregisters a connection when it terminates.
    pub fn unregister(&self, pid: i32) {
        self.connections
            .lock()
            .expect("mutex poisoned")
            .remove(&pid);
    }

    /// Attempts to cancel a connection identified by its PID and secret key.
    pub fn cancel(&self, pid: i32, secret_key: i32) {
        let conns = self.connections.lock().expect("mutex poisoned");
        if let Some(handle) = conns.get(&pid)
            && handle.secret_key == secret_key
        {
            handle.cancel_token.cancel();
        }
    }
}
