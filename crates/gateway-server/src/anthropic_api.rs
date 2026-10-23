//! Anthropic's Messages API (`/v1/messages`), translated to and from the chat path.

use crate::AppState;
use axum::Router;

/// The routes of this module.
pub fn routes() -> Router<AppState> {
    Router::new()
}
