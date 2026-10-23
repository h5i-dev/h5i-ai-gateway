//! Upstream authentication that needs more than a static header: AWS SigV4
//! signing (Bedrock) and Google OAuth2 token exchange (Vertex AI).

pub(crate) mod gcp;
pub(crate) mod sigv4;
