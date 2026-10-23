//! The admin UI, served at `/ui`: a single-page console over the management
//! API (keys, teams, models, spend, a chat playground).
//!
//! The pages are hand-written HTML, CSS and JavaScript modules in
//! `crates/gateway-server/ui/`, embedded in the binary, so the console works
//! offline and needs no build step. It holds no privileges of its own: it
//! calls the same endpoints with the key the operator signs in with, and the
//! kernel decides what that key may see and do.
//!
//! - `/ui`, `/ui/` and any other `/ui/...` path (the console's own routes,
//!   such as `/ui/keys`) answer the page, never cached.
//! - `/ui/assets/{version}/{path}` answers an asset. `version` is a hash of
//!   every asset, so a URL names one exact content and is cached for a year;
//!   an outdated version still answers, uncached.

use crate::AppState;
use axum::Router;
use axum::extract::Path;
use axum::http::{HeaderMap, HeaderValue, StatusCode, header};
use axum::response::{IntoResponse, Response};
use axum::routing::get;
use std::sync::OnceLock;

struct Asset {
    path: &'static str,
    mime: &'static str,
    body: &'static [u8],
}

macro_rules! assets {
    ($($path:literal => $mime:expr),* $(,)?) => {
        &[$(Asset { path: $path, mime: $mime, body: include_bytes!(concat!("../ui/", $path)) }),*]
    };
}

const JS: &str = "text/javascript; charset=utf-8";

/// Everything under `/ui/assets/`. Add new files here.
const ASSETS: &[Asset] = assets! {
    "app.css" => "text/css; charset=utf-8",
    "favicon.svg" => "image/svg+xml",
    "js/boot.js" => JS,
    "js/main.js" => JS,
    "js/api.js" => JS,
    "js/dom.js" => JS,
    "js/format.js" => JS,
    "js/charts.js" => JS,
    "js/views/login.js" => JS,
    "js/views/dashboard.js" => JS,
    "js/views/keys.js" => JS,
    "js/views/teams.js" => JS,
    "js/views/spend.js" => JS,
    "js/views/playground.js" => JS,
    "js/views/account.js" => JS,
    "js/views/common.js" => JS,
};

const INDEX: &str = include_str!("../ui/index.html");

/// FNV-1a over every asset's path and bytes, at compile time.
const fn fingerprint() -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    let mut i = 0;
    while i < ASSETS.len() {
        let parts = [ASSETS[i].path.as_bytes(), ASSETS[i].body];
        let mut p = 0;
        while p < parts.len() {
            let mut j = 0;
            while j < parts[p].len() {
                h = (h ^ parts[p][j] as u64).wrapping_mul(0x0100_0000_01b3);
                j += 1;
            }
            h = (h ^ 0xff).wrapping_mul(0x0100_0000_01b3);
            p += 1;
        }
        i += 1;
    }
    h
}

/// The current asset version, as it appears in asset URLs.
pub fn version() -> &'static str {
    static V: OnceLock<String> = OnceLock::new();
    V.get_or_init(|| format!("{:012x}", fingerprint() & 0xffff_ffff_ffff))
}

/// Every embedded asset's path (under `/ui/assets/{version}/`) and content type.
pub fn assets() -> impl Iterator<Item = (&'static str, &'static str)> {
    ASSETS.iter().map(|a| (a.path, a.mime))
}

/// The page, with asset URLs pointing at the current version.
fn index_html() -> &'static str {
    static HTML: OnceLock<String> = OnceLock::new();
    HTML.get_or_init(|| INDEX.replace("{{ASSETS}}", &format!("/ui/assets/{}", version())))
}

/// The routes of this module.
pub fn routes() -> Router<AppState> {
    Router::new()
        .route("/ui", get(index))
        .route("/ui/", get(index))
        .route("/ui/assets/{version}/{*path}", get(asset))
        .route("/ui/{*rest}", get(index))
}

/// Headers every UI response carries: the console loads nothing from
/// anywhere but the gateway, and may not be framed.
fn security_headers(h: &mut HeaderMap) {
    h.insert(
        header::CONTENT_SECURITY_POLICY,
        HeaderValue::from_static(
            "default-src 'none'; script-src 'self'; style-src 'self'; img-src 'self' data:; connect-src 'self'; \
             font-src 'self'; base-uri 'none'; form-action 'self'; frame-ancestors 'none'",
        ),
    );
    h.insert(header::X_CONTENT_TYPE_OPTIONS, HeaderValue::from_static("nosniff"));
    h.insert(header::REFERRER_POLICY, HeaderValue::from_static("no-referrer"));
    h.insert(header::X_FRAME_OPTIONS, HeaderValue::from_static("DENY"));
}

async fn index() -> Response {
    let mut h = HeaderMap::new();
    h.insert(header::CONTENT_TYPE, HeaderValue::from_static("text/html; charset=utf-8"));
    h.insert(header::CACHE_CONTROL, HeaderValue::from_static("no-cache"));
    security_headers(&mut h);
    (h, index_html()).into_response()
}

async fn asset(Path((v, path)): Path<(String, String)>) -> Response {
    let Some(a) = ASSETS.iter().find(|a| a.path == path) else {
        return (StatusCode::NOT_FOUND, "not found").into_response();
    };
    let mut h = HeaderMap::new();
    h.insert(header::CONTENT_TYPE, HeaderValue::from_static(a.mime));
    let cache = if v == version() { "public, max-age=31536000, immutable" } else { "no-cache" };
    h.insert(header::CACHE_CONTROL, HeaderValue::from_static(cache));
    security_headers(&mut h);
    (h, a.body).into_response()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn index_references_versioned_assets_that_exist() {
        let html = index_html();
        assert!(!html.contains("{{ASSETS}}"));
        let prefix = format!("/ui/assets/{}/", version());
        let mut found = 0;
        for part in html.split(&prefix).skip(1) {
            let path = &part[..part.find('"').unwrap()];
            assert!(ASSETS.iter().any(|a| a.path == path), "index.html references missing asset {path}");
            found += 1;
        }
        assert!(found >= 3);
    }

    #[test]
    fn every_module_import_is_an_embedded_asset() {
        for a in ASSETS.iter().filter(|a| a.mime == JS) {
            let src = std::str::from_utf8(a.body).unwrap();
            let dir = a.path.rsplit_once('/').map(|(d, _)| d).unwrap_or("");
            for line in src.lines().filter(|l| l.starts_with("import ")) {
                let spec = line.split(['"', '\'']).nth(1).unwrap();
                let mut parts: Vec<&str> = if dir.is_empty() { Vec::new() } else { dir.split('/').collect() };
                for seg in spec.split('/') {
                    match seg {
                        "." => {}
                        ".." => {
                            parts.pop();
                        }
                        s => parts.push(s),
                    }
                }
                let target = parts.join("/");
                assert!(ASSETS.iter().any(|a| a.path == target), "{} imports {spec}, which is not embedded", a.path);
            }
        }
    }
}
