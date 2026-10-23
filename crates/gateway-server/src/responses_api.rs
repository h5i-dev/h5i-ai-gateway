//! OpenAI's Responses API (`/v1/responses`).

use crate::AppState;
use axum::Router;

/// The routes of this module.
pub fn routes() -> Router<AppState> {
    Router::new()
}
