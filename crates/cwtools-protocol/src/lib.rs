#![forbid(unsafe_code)]

use serde::{Deserialize, Serialize};
use serde_json::Value;

pub const JSON_RPC_VERSION: &str = "2.0";
pub const DEFAULT_MAX_FRAME_BYTES: usize = 16 * 1024 * 1024;
pub const DEFAULT_MAX_HEADER_BYTES: usize = 8 * 1024;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(untagged)]
pub enum RequestId {
    Number(i64),
    String(String),
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
pub struct Message {
    #[serde(default = "json_rpc_version")]
    pub jsonrpc: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub id: Option<RequestId>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub method: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub params: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub result: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<JsonRpcError>,
}

fn json_rpc_version() -> String {
    JSON_RPC_VERSION.to_owned()
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
pub struct JsonRpcError {
    pub code: i64,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<Value>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Lifecycle {
    #[default]
    Created,
    Initializing,
    Initialized,
    Shutdown,
    Exited,
}

impl Lifecycle {
    /// Advances the externally visible LSP lifecycle.
    ///
    /// # Errors
    /// Returns [`LifecycleError`] when `method` is invalid for the current state.
    pub fn observe(&mut self, method: &str) -> Result<(), LifecycleError> {
        let next = match (*self, method) {
            (Self::Created, "initialize") => Self::Initializing,
            (Self::Initializing, "initialized") => Self::Initialized,
            (Self::Initialized, "shutdown") => Self::Shutdown,
            (Self::Shutdown, "exit") => Self::Exited,
            (_, "$/cancelRequest") => return Ok(()),
            _ => {
                return Err(LifecycleError {
                    state: *self,
                    method: method.to_owned(),
                });
            }
        };
        *self = next;
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LifecycleError {
    pub state: Lifecycle,
    pub method: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn message_round_trips() {
        let input = r#"{"jsonrpc":"2.0","id":1,"method":"shutdown","params":null}"#;
        let message: Message = serde_json::from_str(input).unwrap();
        assert_eq!(message.id, Some(RequestId::Number(1)));
        assert_eq!(serde_json::to_value(message).unwrap()["method"], "shutdown");
    }

    #[test]
    fn lifecycle_rejects_out_of_order_methods() {
        let mut lifecycle = Lifecycle::default();
        assert!(lifecycle.observe("initialized").is_err());
        for method in ["initialize", "initialized", "shutdown", "exit"] {
            lifecycle.observe(method).unwrap();
        }
        assert_eq!(lifecycle, Lifecycle::Exited);
    }
}
