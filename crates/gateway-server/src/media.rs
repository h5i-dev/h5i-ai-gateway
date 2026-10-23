//! Images and audio: `/v1/images/*`, `/v1/audio/*`.

use crate::AppState;
use axum::Router;

/// The routes of this module.
pub fn routes() -> Router<AppState> {
    Router::new()
}
