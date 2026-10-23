//! Google Cloud OAuth2 access tokens for Vertex AI.
//!
//! Credential sources, in the order [`crate::Deployment`] resolves them:
//!
//! * a pre-issued access token (`api_key`), used as is;
//! * service-account JSON (`vertex_credentials` / `VERTEXAI_CREDENTIALS` /
//!   `GOOGLE_APPLICATION_CREDENTIALS` / the gcloud ADC file): a JWT signed
//!   with RS256 is exchanged at the key's `token_uri` (RFC 7523 bearer grant);
//! * `authorized_user` JSON (`gcloud auth application-default login`): the
//!   refresh token is exchanged at its `token_uri`;
//! * the GCE metadata server (`GCE_METADATA_HOST`, default
//!   `metadata.google.internal`) as a last resort.
//!
//! Tokens are cached per credential in a [`TokenCache`] shared by every
//! request through one [`crate::Client`], and refreshed
//! [`REFRESH_MARGIN`] before they expire. Each credential has its own async
//! mutex, so concurrent requests trigger a single exchange.

use std::collections::HashMap;
use std::fmt;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use aws_lc_rs::rand::SystemRandom;
use aws_lc_rs::signature::{RSA_PKCS1_SHA256, RsaKeyPair};
use base64::Engine;
use base64::engine::general_purpose::{STANDARD, URL_SAFE_NO_PAD};
use serde_json::{Value, json};

use crate::deployment::Secret;
use crate::error::{ErrorKind, ProviderError};

/// Google's OAuth2 token endpoint.
pub const DEFAULT_TOKEN_URI: &str = "https://oauth2.googleapis.com/token";
/// The scope Vertex AI needs.
pub const CLOUD_PLATFORM_SCOPE: &str = "https://www.googleapis.com/auth/cloud-platform";
/// Default GCE metadata server host.
pub const DEFAULT_METADATA_HOST: &str = "metadata.google.internal";
/// Tokens are refreshed this long before they expire.
pub const REFRESH_MARGIN: Duration = Duration::from_secs(300);
/// Lifetime requested for service-account assertions (the maximum).
const JWT_LIFETIME_SECS: u64 = 3600;
const PROVIDER: &str = "vertex_ai";
const EXCHANGE_TIMEOUT: Duration = Duration::from_secs(30);

/// A service-account key (the JSON downloaded from the console).
#[derive(Clone, PartialEq, Eq)]
pub struct ServiceAccountKey {
    pub client_email: String,
    /// PEM, PKCS#8 (`BEGIN PRIVATE KEY`) or PKCS#1 (`BEGIN RSA PRIVATE KEY`).
    pub private_key: Secret,
    pub private_key_id: Option<String>,
    pub token_uri: String,
    pub project_id: Option<String>,
}

impl fmt::Debug for ServiceAccountKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ServiceAccountKey")
            .field("client_email", &self.client_email)
            .field("private_key", &self.private_key)
            .field("token_uri", &self.token_uri)
            .field("project_id", &self.project_id)
            .finish_non_exhaustive()
    }
}

/// User credentials from `gcloud auth application-default login`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuthorizedUser {
    pub client_id: String,
    pub client_secret: Secret,
    pub refresh_token: Secret,
    pub token_uri: String,
    pub quota_project_id: Option<String>,
}

/// Where Vertex AI access tokens come from.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum GcpCredentials {
    /// A ready OAuth2 access token (`api_key`).
    AccessToken(Secret),
    ServiceAccount(ServiceAccountKey),
    AuthorizedUser(AuthorizedUser),
    /// The GCE / GKE / Cloud Run metadata server at `host` (`host[:port]`).
    MetadataServer {
        host: String,
    },
}

impl GcpCredentials {
    /// Parse a credentials JSON object (`type: service_account` or
    /// `authorized_user`).
    pub fn from_json(v: &Value) -> Result<Self, String> {
        let s = |k: &str| v.get(k).and_then(Value::as_str).map(str::to_owned);
        let need = |k: &str| s(k).ok_or_else(|| format!("credentials JSON lacks '{k}'"));
        let token_uri = s("token_uri").unwrap_or_else(|| DEFAULT_TOKEN_URI.to_owned());
        match s("type").as_deref() {
            Some("service_account") | None if v.get("private_key").is_some() => {
                let key = ServiceAccountKey {
                    client_email: need("client_email")?,
                    private_key: Secret::new(need("private_key")?),
                    private_key_id: s("private_key_id"),
                    token_uri,
                    project_id: s("project_id"),
                };
                // Fail at configuration time rather than on the first call.
                parse_private_key(key.private_key.expose())?;
                Ok(GcpCredentials::ServiceAccount(key))
            }
            Some("authorized_user") => Ok(GcpCredentials::AuthorizedUser(AuthorizedUser {
                client_id: need("client_id")?,
                client_secret: Secret::new(need("client_secret")?),
                refresh_token: Secret::new(need("refresh_token")?),
                token_uri,
                quota_project_id: s("quota_project_id"),
            })),
            Some(other) => Err(format!(
                "credentials of type '{other}' are not supported (use a service account key, \
                 authorized_user credentials, an access token or the metadata server)"
            )),
            None => Err("credentials JSON has no 'type'".into()),
        }
    }

    /// Load credentials from a JSON string or, otherwise, a file path.
    pub fn load(source: &str) -> Result<Self, String> {
        let trimmed = source.trim();
        let text = if trimmed.starts_with('{') {
            trimmed.to_owned()
        } else {
            std::fs::read_to_string(trimmed)
                .map_err(|e| format!("cannot read credentials file '{trimmed}': {e}"))?
        };
        let v: Value = serde_json::from_str(&text)
            .map_err(|e| format!("credentials are not valid JSON: {e}"))?;
        Self::from_json(&v)
    }

    /// The project the credentials belong to, when they say.
    pub fn project_id(&self) -> Option<&str> {
        match self {
            GcpCredentials::ServiceAccount(k) => k.project_id.as_deref(),
            GcpCredentials::AuthorizedUser(u) => u.quota_project_id.as_deref(),
            _ => None,
        }
    }

    fn cache_key(&self) -> String {
        match self {
            GcpCredentials::AccessToken(_) => String::new(),
            GcpCredentials::ServiceAccount(k) => {
                format!(
                    "sa\0{}\0{}\0{}",
                    k.client_email,
                    k.token_uri,
                    k.private_key_id.as_deref().unwrap_or_default()
                )
            }
            GcpCredentials::AuthorizedUser(u) => format!(
                "au\0{}\0{}\0{}",
                u.client_id,
                u.token_uri,
                crate::auth::sigv4::sha256_hex(u.refresh_token.expose().as_bytes())
            ),
            GcpCredentials::MetadataServer { host } => format!("md\0{host}"),
        }
    }
}

/// Decode a PEM RSA private key.
fn parse_private_key(pem: &str) -> Result<RsaKeyPair, String> {
    let pkcs1 = pem.contains("BEGIN RSA PRIVATE KEY");
    let body: String = pem
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with("-----"))
        .collect();
    let der = STANDARD
        .decode(body.as_bytes())
        .map_err(|e| format!("private_key is not valid PEM: {e}"))?;
    let key = if pkcs1 {
        RsaKeyPair::from_der(&der)
    } else {
        RsaKeyPair::from_pkcs8(&der)
    };
    key.map_err(|e| format!("private_key is not a usable RSA key: {e}"))
}

/// The signed assertion for the JWT-bearer grant, issued at `now` (Unix
/// seconds).
pub(crate) fn service_account_jwt(key: &ServiceAccountKey, now: u64) -> Result<String, String> {
    let mut header = json!({"alg": "RS256", "typ": "JWT"});
    if let Some(kid) = &key.private_key_id {
        header["kid"] = Value::String(kid.clone());
    }
    let claims = json!({
        "iss": key.client_email,
        "scope": CLOUD_PLATFORM_SCOPE,
        "aud": key.token_uri,
        "iat": now,
        "exp": now + JWT_LIFETIME_SECS,
    });
    let signing_input = format!(
        "{}.{}",
        URL_SAFE_NO_PAD.encode(header.to_string()),
        URL_SAFE_NO_PAD.encode(claims.to_string())
    );
    let pair = parse_private_key(key.private_key.expose())?;
    let mut sig = vec![0u8; pair.public_modulus_len()];
    pair.sign(
        &RSA_PKCS1_SHA256,
        &SystemRandom::new(),
        signing_input.as_bytes(),
        &mut sig,
    )
    .map_err(|_| "RSA signing failed".to_owned())?;
    Ok(format!("{signing_input}.{}", URL_SAFE_NO_PAD.encode(sig)))
}

/// `application/x-www-form-urlencoded` body.
pub(crate) fn form_body(pairs: &[(&str, &str)]) -> String {
    let enc = |s: &str| {
        let mut out = String::with_capacity(s.len());
        for b in s.bytes() {
            if b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.' | b'~') {
                out.push(b as char);
            } else {
                out.push_str(&format!("%{b:02X}"));
            }
        }
        out
    };
    pairs
        .iter()
        .map(|(k, v)| format!("{}={}", enc(k), enc(v)))
        .collect::<Vec<_>>()
        .join("&")
}

#[derive(Debug, Clone)]
struct Cached {
    value: String,
    /// `None`: never expires (project ids).
    refresh_at: Option<Instant>,
}

type Slot = Arc<tokio::sync::Mutex<Option<Cached>>>;

/// Access tokens (and metadata-server project ids) shared across requests.
#[derive(Debug, Default)]
pub(crate) struct TokenCache {
    slots: Mutex<HashMap<String, Slot>>,
}

impl TokenCache {
    fn slot(&self, key: String) -> Slot {
        let mut slots = self.slots.lock().unwrap_or_else(|p| p.into_inner());
        slots.entry(key).or_default().clone()
    }

    /// A valid access token for `creds`, exchanging (once, even under
    /// concurrency) when there is none or it is about to expire.
    pub async fn access_token(
        &self,
        http: &reqwest::Client,
        creds: &GcpCredentials,
    ) -> Result<String, ProviderError> {
        if let GcpCredentials::AccessToken(t) = creds {
            return Ok(t.expose().to_owned());
        }
        let slot = self.slot(creds.cache_key());
        let mut guard = slot.lock().await;
        if let Some(c) = guard.as_ref()
            && c.refresh_at.is_none_or(|t| Instant::now() < t)
        {
            return Ok(c.value.clone());
        }
        let (token, expires_in) = fetch_token(http, creds).await?;
        let lifetime = Duration::from_secs(expires_in).saturating_sub(REFRESH_MARGIN);
        *guard = Some(Cached {
            value: token.clone(),
            refresh_at: Some(Instant::now() + lifetime),
        });
        Ok(token)
    }

    /// The project of a metadata-server identity (fetched once).
    pub async fn metadata_project(
        &self,
        http: &reqwest::Client,
        host: &str,
    ) -> Result<String, ProviderError> {
        let slot = self.slot(format!("mdproject\0{host}"));
        let mut guard = slot.lock().await;
        if let Some(c) = guard.as_ref() {
            return Ok(c.value.clone());
        }
        let url = format!("http://{host}/computeMetadata/v1/project/project-id");
        let resp = http
            .get(&url)
            .header("Metadata-Flavor", "Google")
            .timeout(EXCHANGE_TIMEOUT)
            .send()
            .await
            .map_err(|e| {
                auth_error(format!(
                    "GCE metadata server unreachable: {}",
                    e.without_url()
                ))
            })?;
        let status = resp.status();
        let text = resp.text().await.unwrap_or_default();
        if !status.is_success() || text.trim().is_empty() {
            return Err(auth_error(format!(
                "GCE metadata server returned HTTP {status} for the project id"
            )));
        }
        let project = text.trim().to_owned();
        *guard = Some(Cached {
            value: project.clone(),
            refresh_at: None,
        });
        Ok(project)
    }
}

fn auth_error(message: String) -> ProviderError {
    ProviderError::new(ErrorKind::Authentication, PROVIDER, message)
}

/// Perform the exchange; returns `(access_token, expires_in seconds)`.
async fn fetch_token(
    http: &reqwest::Client,
    creds: &GcpCredentials,
) -> Result<(String, u64), ProviderError> {
    let request = match creds {
        GcpCredentials::AccessToken(_) => unreachable!("handled by the caller"),
        GcpCredentials::ServiceAccount(key) => {
            let jwt = service_account_jwt(key, crate::providers::now_unix())
                .map_err(|e| ProviderError::config(PROVIDER, e))?;
            http.post(&key.token_uri)
                .header("content-type", "application/x-www-form-urlencoded")
                .body(form_body(&[
                    ("grant_type", "urn:ietf:params:oauth:grant-type:jwt-bearer"),
                    ("assertion", &jwt),
                ]))
        }
        GcpCredentials::AuthorizedUser(u) => http
            .post(&u.token_uri)
            .header("content-type", "application/x-www-form-urlencoded")
            .body(form_body(&[
                ("grant_type", "refresh_token"),
                ("client_id", &u.client_id),
                ("client_secret", u.client_secret.expose()),
                ("refresh_token", u.refresh_token.expose()),
            ])),
        GcpCredentials::MetadataServer { host } => http
            .get(format!(
                "http://{host}/computeMetadata/v1/instance/service-accounts/default/token"
            ))
            .header("Metadata-Flavor", "Google"),
    };
    let resp = request
        .timeout(EXCHANGE_TIMEOUT)
        .send()
        .await
        .map_err(|e| {
            let mut err = ProviderError::from_reqwest(PROVIDER, e);
            if matches!(creds, GcpCredentials::MetadataServer { .. }) {
                err = auth_error(format!(
                    "no Vertex AI credentials configured and the GCE metadata server is unreachable ({})",
                    err.message()
                ));
            }
            err
        })?;
    let status = resp.status();
    let body = resp.text().await.unwrap_or_default();
    if !status.is_success() {
        let v: Value = serde_json::from_str(&body).unwrap_or(Value::Null);
        let detail = v["error_description"]
            .as_str()
            .or_else(|| v["error"].as_str())
            .unwrap_or(body.trim());
        let message = format!("Google OAuth2 token exchange failed (HTTP {status}): {detail}");
        return Err(match status.as_u16() {
            400 | 401 | 403 => auth_error(message),
            s => ProviderError::from_upstream(PROVIDER, s, &message, None),
        });
    }
    let v: Value = serde_json::from_str(&body).map_err(|e| {
        ProviderError::invalid_response(PROVIDER, format!("token response is not JSON: {e}"))
    })?;
    let token = v["access_token"]
        .as_str()
        .filter(|t| !t.is_empty())
        .ok_or_else(|| {
            ProviderError::invalid_response(PROVIDER, "token response without access_token")
        })?;
    let expires_in = v["expires_in"]
        .as_u64()
        .or_else(|| v["expires_in"].as_str().and_then(|s| s.parse().ok()))
        .unwrap_or(3600);
    Ok((token.to_owned(), expires_in))
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use aws_lc_rs::encoding::AsDer;
    use aws_lc_rs::rsa::{KeyPair, KeySize};
    use aws_lc_rs::signature::{KeyPair as _, RSA_PKCS1_2048_8192_SHA256, UnparsedPublicKey};
    use std::sync::OnceLock;

    /// A 2048-bit test key generated once per test run: `(PKCS#8 PEM,
    /// public key DER)`.
    pub(crate) fn test_key() -> &'static (String, Vec<u8>) {
        static KEY: OnceLock<(String, Vec<u8>)> = OnceLock::new();
        KEY.get_or_init(|| {
            let pair = KeyPair::generate(KeySize::Rsa2048).unwrap();
            let der = AsDer::<aws_lc_rs::encoding::Pkcs8V1Der>::as_der(&pair).unwrap();
            let b64 = STANDARD.encode(der.as_ref());
            let mut pem = String::from("-----BEGIN PRIVATE KEY-----\n");
            for line in b64.as_bytes().chunks(64) {
                pem.push_str(std::str::from_utf8(line).unwrap());
                pem.push('\n');
            }
            pem.push_str("-----END PRIVATE KEY-----\n");
            (pem, pair.public_key().as_ref().to_vec())
        })
    }

    pub(crate) fn service_account_json(token_uri: &str) -> Value {
        json!({
            "type": "service_account",
            "project_id": "proj-from-key",
            "private_key_id": "kid-1",
            "private_key": test_key().0,
            "client_email": "gateway@proj-from-key.iam.gserviceaccount.com",
            "client_id": "123",
            "token_uri": token_uri,
        })
    }

    #[test]
    fn parses_service_account_and_authorized_user() {
        let creds = GcpCredentials::from_json(&service_account_json("https://t/token")).unwrap();
        let GcpCredentials::ServiceAccount(key) = &creds else {
            panic!("expected a service account")
        };
        assert_eq!(
            key.client_email,
            "gateway@proj-from-key.iam.gserviceaccount.com"
        );
        assert_eq!(key.token_uri, "https://t/token");
        assert_eq!(creds.project_id(), Some("proj-from-key"));
        assert!(
            !format!("{creds:?}").contains("PRIVATE KEY"),
            "key must be redacted"
        );

        let mut no_uri = service_account_json("x");
        no_uri.as_object_mut().unwrap().remove("token_uri");
        let GcpCredentials::ServiceAccount(key) = GcpCredentials::from_json(&no_uri).unwrap()
        else {
            panic!()
        };
        assert_eq!(key.token_uri, DEFAULT_TOKEN_URI);

        let au = GcpCredentials::from_json(&json!({
            "type": "authorized_user", "client_id": "cid", "client_secret": "cs",
            "refresh_token": "rt", "quota_project_id": "qp"
        }))
        .unwrap();
        assert_eq!(au.project_id(), Some("qp"));
        assert!(
            matches!(au, GcpCredentials::AuthorizedUser(ref u) if u.token_uri == DEFAULT_TOKEN_URI)
        );

        assert!(
            GcpCredentials::from_json(&json!({"type": "external_account"}))
                .unwrap_err()
                .contains("not supported")
        );
        assert!(
            GcpCredentials::from_json(&json!({"type": "service_account", "private_key": "x"}))
                .is_err()
        );
        let mut bad_key = service_account_json("x");
        bad_key["private_key"] =
            json!("-----BEGIN PRIVATE KEY-----\nAAAA\n-----END PRIVATE KEY-----\n");
        assert!(
            GcpCredentials::from_json(&bad_key)
                .unwrap_err()
                .contains("RSA")
        );
    }

    #[test]
    fn loads_from_string_or_file() {
        let json = service_account_json("https://t/token").to_string();
        assert!(matches!(
            GcpCredentials::load(&format!("  {json}")),
            Ok(GcpCredentials::ServiceAccount(_))
        ));
        let path = std::env::temp_dir().join(format!("h5i-gw-sa-{}.json", std::process::id()));
        std::fs::write(&path, &json).unwrap();
        let loaded = GcpCredentials::load(path.to_str().unwrap()).unwrap();
        std::fs::remove_file(&path).unwrap();
        assert_eq!(loaded.project_id(), Some("proj-from-key"));
        assert!(
            GcpCredentials::load("/nonexistent/creds.json")
                .unwrap_err()
                .contains("cannot read")
        );
        assert!(GcpCredentials::load("{not json").is_err());
    }

    #[test]
    fn jwt_is_well_formed_and_verifies() {
        let GcpCredentials::ServiceAccount(key) =
            GcpCredentials::from_json(&service_account_json("https://oauth2.example/token"))
                .unwrap()
        else {
            panic!()
        };
        let jwt = service_account_jwt(&key, 1_700_000_000).unwrap();
        let parts: Vec<&str> = jwt.split('.').collect();
        assert_eq!(parts.len(), 3);
        let header: Value =
            serde_json::from_slice(&URL_SAFE_NO_PAD.decode(parts[0]).unwrap()).unwrap();
        assert_eq!(
            header,
            json!({"alg": "RS256", "typ": "JWT", "kid": "kid-1"})
        );
        let claims: Value =
            serde_json::from_slice(&URL_SAFE_NO_PAD.decode(parts[1]).unwrap()).unwrap();
        assert_eq!(
            claims,
            json!({
                "iss": "gateway@proj-from-key.iam.gserviceaccount.com",
                "scope": CLOUD_PLATFORM_SCOPE,
                "aud": "https://oauth2.example/token",
                "iat": 1_700_000_000u64,
                "exp": 1_700_003_600u64,
            })
        );
        let sig = URL_SAFE_NO_PAD.decode(parts[2]).unwrap();
        let public = UnparsedPublicKey::new(&RSA_PKCS1_2048_8192_SHA256, &test_key().1);
        public
            .verify(format!("{}.{}", parts[0], parts[1]).as_bytes(), &sig)
            .expect("signature verifies with the public key");
        // Tampering breaks it.
        assert!(public.verify(b"x.y", &sig).is_err());
    }

    /// Read one DER TLV: `(tag, content, rest)`.
    fn der_tlv(b: &[u8]) -> (u8, &[u8], &[u8]) {
        let tag = b[0];
        let (len, hdr) = if b[1] & 0x80 == 0 {
            (b[1] as usize, 2)
        } else {
            let n = (b[1] & 0x7F) as usize;
            let len = b[2..2 + n]
                .iter()
                .fold(0usize, |acc, x| acc << 8 | *x as usize);
            (len, 2 + n)
        };
        (tag, &b[hdr..hdr + len], &b[hdr + len..])
    }

    #[test]
    fn pkcs1_keys_are_accepted() {
        // PKCS#8 = SEQUENCE { INTEGER version, AlgorithmIdentifier,
        // OCTET STRING (PKCS#1 RSAPrivateKey) }: unwrap it.
        let pkcs8 = STANDARD
            .decode(
                test_key()
                    .0
                    .lines()
                    .filter(|l| !l.starts_with("-----"))
                    .collect::<String>(),
            )
            .unwrap();
        let (_, seq, _) = der_tlv(&pkcs8);
        let (_, _, rest) = der_tlv(seq); // version
        let (_, _, rest) = der_tlv(rest); // algorithm
        let (tag, pkcs1, _) = der_tlv(rest);
        assert_eq!(tag, 0x04);
        let pem = format!(
            "-----BEGIN RSA PRIVATE KEY-----\n{}\n-----END RSA PRIVATE KEY-----\n",
            STANDARD.encode(pkcs1)
        );
        let pair = parse_private_key(&pem).unwrap();
        assert_eq!(pair.public_key().as_ref(), test_key().1.as_slice());
        assert!(
            parse_private_key(&pem.replace("RSA PRIVATE KEY", "PRIVATE KEY")).is_err(),
            "PKCS#1 DER is not PKCS#8"
        );
    }

    #[test]
    fn form_encoding() {
        assert_eq!(
            form_body(&[
                ("grant_type", "urn:ietf:params:oauth:grant-type:jwt-bearer"),
                ("a", "b c/=")
            ]),
            "grant_type=urn%3Aietf%3Aparams%3Aoauth%3Agrant-type%3Ajwt-bearer&a=b%20c%2F%3D"
        );
    }

    #[tokio::test]
    async fn access_tokens_pass_through_without_network() {
        let cache = TokenCache::default();
        let http = reqwest::Client::new();
        let t = cache
            .access_token(&http, &GcpCredentials::AccessToken(Secret::new("ya29.x")))
            .await
            .unwrap();
        assert_eq!(t, "ya29.x");
    }
}
