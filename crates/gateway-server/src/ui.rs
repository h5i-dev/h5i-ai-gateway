//! The admin UI, served at `/ui`.

use crate::AppState;
use axum::Router;

/// The routes of this module.
pub fn routes() -> Router<AppState> {
    Router::new()
}
