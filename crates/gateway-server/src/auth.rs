//! Who is calling. Two credentials, as in LiteLLM: the operator's master
//! key, and virtual keys (`sk-...`) issued by `/key/generate`.
//!
//! A virtual key is `sk-` followed by an h5i-app bearer token
//! (`v1.<org>.<key id>.<expiry>.<hmac>`): its signature proves the gateway
//! issued it, and its key id names the kernel's `Key` row. Whether the key
//! may still be used (blocked, expired, deleted, over budget) is the kernel's
//! decision on every request, so revocation takes effect immediately.

use crate::kernel::Gateway;
use axum::http::HeaderMap;
use gateway_kernel::Principal;
use h5i_app_http::{AuthError, Authenticator, HmacAuth};

/// The prefix of a virtual key.
pub const KEY_PREFIX: &str = "sk-";

/// Tokens that never expire on their own still carry an expiry; this is
/// the one they get (the kernel's `expires_at` is what counts).
const LONG_LIVED_SECS: u64 = 100 * 365 * 86_400;

pub struct GatewayAuth {
    master_key: Option<String>,
    org: u64,
    tokens: HmacAuth<Gateway>,
}

impl GatewayAuth {
    /// `secret` signs virtual keys; `org` is the tenant of the master key.
    pub fn new(master_key: Option<String>, secret: impl Into<Vec<u8>>, org: u64) -> Self {
        let tokens = HmacAuth::new(secret, |org, key| Principal { org, key, master: false, now: 0 });
        GatewayAuth { master_key, org, tokens }
    }

    /// A new virtual key for key `key` of tenant `org`, valid until `expires_at`
    /// (Unix seconds; `u64::MAX` for never).
    pub fn issue(&self, org: u64, key: u64, expires_at: u64) -> String {
        let now = unix_now();
        let ttl = if expires_at == u64::MAX { LONG_LIVED_SECS } else { expires_at.saturating_sub(now).max(1) };
        format!("{KEY_PREFIX}{}", self.tokens.issue(org, key, ttl))
    }

    /// The tenant and key id of a virtual key this gateway signed.
    pub fn parse_key(&self, key: &str) -> Result<(u64, u64), AuthError> {
        let token = key.strip_prefix(KEY_PREFIX).ok_or_else(|| AuthError("not a virtual key".into()))?;
        self.tokens.verify(token)
    }

    /// The principal of a credential: the master key or a virtual key.
    pub fn principal(&self, credential: &str) -> Result<Principal, AuthError> {
        if let Some(master) = &self.master_key
            && ct_eq(credential.as_bytes(), master.as_bytes())
        {
            return Ok(Principal { org: self.org, key: 0, master: true, now: 0 });
        }
        let (org, key) = self.parse_key(credential).map_err(|_| AuthError("Authentication Error, Invalid proxy server token passed.".into()))?;
        Ok(Principal { org, key, master: false, now: 0 })
    }
}

/// The credential of a request: `Authorization: Bearer`, or the headers the
/// OpenAI, Anthropic, Azure and Gemini SDKs send their keys in.
pub fn credential(headers: &HeaderMap) -> Option<&str> {
    for name in ["authorization", "x-litellm-api-key"] {
        if let Some(v) = headers.get(name).and_then(|v| v.to_str().ok()) {
            let v = v.trim();
            return Some(v.strip_prefix("Bearer ").or_else(|| v.strip_prefix("bearer ")).unwrap_or(v).trim());
        }
    }
    ["x-api-key", "api-key", "x-goog-api-key"].iter().find_map(|name| headers.get(*name).and_then(|v| v.to_str().ok()).map(str::trim))
}

impl Authenticator<Gateway> for GatewayAuth {
    fn authenticate(&self, headers: &HeaderMap) -> Result<Principal, AuthError> {
        let c = credential(headers).ok_or_else(|| AuthError("No api key passed in.".into()))?;
        self.principal(c)
    }
}

/// Constant-time equality, so comparing with the master key leaks nothing.
fn ct_eq(a: &[u8], b: &[u8]) -> bool {
    a.len() == b.len() && a.iter().zip(b).fold(0u8, |acc, (x, y)| acc | (x ^ y)) == 0
}

pub fn unix_now() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn auth() -> GatewayAuth {
        GatewayAuth::new(Some("sk-master".into()), "secret", 1)
    }

    #[test]
    fn master_and_virtual_keys() {
        let a = auth();
        assert!(a.principal("sk-master").unwrap().master);
        let k = a.issue(3, 42, u64::MAX);
        assert!(k.starts_with("sk-v1.3.42."));
        assert_eq!(a.principal(&k).unwrap(), Principal { org: 3, key: 42, master: false, now: 0 });
        assert!(a.principal("sk-v1.3.42.9999999999.00").is_err());
        let other = GatewayAuth::new(None, "other-secret", 1).issue(3, 42, u64::MAX);
        assert!(a.principal(&other).is_err());
    }

    #[test]
    fn credentials_from_sdk_headers() {
        let mut h = HeaderMap::new();
        h.insert("x-api-key", "sk-master".parse().unwrap());
        assert_eq!(credential(&h), Some("sk-master"));
        h.insert("authorization", "Bearer sk-1".parse().unwrap());
        assert_eq!(credential(&h), Some("sk-1"));
    }
}
