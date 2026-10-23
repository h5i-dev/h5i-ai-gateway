//! AWS Signature Version 4 request signing (header-based), self-contained on
//! top of `aws-lc-rs` (already linked by rustls) for SHA-256 and HMAC.
//!
//! Follows the published algorithm: the canonical request (method, URI with
//! each path segment URI-encoded again as non-S3 services require, sorted
//! query, sorted lower-cased headers with trimmed values, signed header list,
//! hex SHA-256 of the payload), the string to sign over the credential scope
//! `date/region/service/aws4_request`, and the HMAC-SHA256 key derivation
//! chain. Like botocore, the payload hash is not sent as a header unless
//! asked for, and only the headers passed in (plus `host`, `x-amz-date` and
//! `x-amz-security-token`) are signed. Verified against AWS's SigV4 test
//! suite and a botocore golden vector (see the tests).

use std::time::{SystemTime, UNIX_EPOCH};

use aws_lc_rs::{digest, hmac};

const ALGORITHM: &str = "AWS4-HMAC-SHA256";

/// What to sign with.
#[derive(Debug, Clone, Copy)]
pub(crate) struct SigningParams<'a> {
    pub access_key_id: &'a str,
    pub secret_access_key: &'a str,
    pub session_token: Option<&'a str>,
    pub region: &'a str,
    pub service: &'a str,
    pub time: SystemTime,
    /// Also send (and sign) `x-amz-content-sha256` (S3-style).
    pub content_sha256_header: bool,
}

/// The request being signed.
#[derive(Debug, Clone, Copy)]
pub(crate) struct SignableRequest<'a> {
    pub method: &'a str,
    pub url: &'a str,
    /// Headers to include in the signature (`host` and the `x-amz-*`
    /// signing headers are added by the signer).
    pub headers: &'a [(String, String)],
    pub body: &'a [u8],
}

/// Intermediate values, exposed for tests.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Signature {
    pub canonical_request: String,
    pub string_to_sign: String,
    pub signature: String,
    /// Headers to add to the request: `x-amz-date`, optionally
    /// `x-amz-security-token` / `x-amz-content-sha256`, and `authorization`.
    pub headers: Vec<(String, String)>,
}

pub(crate) fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        out.push(DIGITS[(b >> 4) as usize] as char);
        out.push(DIGITS[(b & 0xF) as usize] as char);
    }
    out
}

pub(crate) fn sha256_hex(data: &[u8]) -> String {
    hex(digest::digest(&digest::SHA256, data).as_ref())
}

fn hmac_sha256(key: &[u8], data: &[u8]) -> hmac::Tag {
    hmac::sign(&hmac::Key::new(hmac::HMAC_SHA256, key), data)
}

/// `(YYYYMMDD'T'HHMMSS'Z', YYYYMMDD)` in UTC.
pub(crate) fn amz_date(time: SystemTime) -> (String, String) {
    let secs = time.duration_since(UNIX_EPOCH).map_or(0, |d| d.as_secs()) as i64;
    let (days, rem) = (secs.div_euclid(86_400), secs.rem_euclid(86_400));
    let (y, m, d) = civil_from_days(days);
    let date = format!("{y:04}{m:02}{d:02}");
    let stamp = format!("{date}T{:02}{:02}{:02}Z", rem / 3600, (rem % 3600) / 60, rem % 60);
    (stamp, date)
}

/// Days since 1970-01-01 to a proleptic Gregorian date (H. Hinnant).
fn civil_from_days(z: i64) -> (i64, u32, u32) {
    let z = z + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    (if m <= 2 { y + 1 } else { y }, m, d)
}

/// URI-encode per SigV4: unreserved characters stay, everything else
/// (including `%`) becomes `%XX`; `/` is kept when `keep_slash`.
fn uri_encode(s: &str, keep_slash: bool) -> String {
    let mut out = String::with_capacity(s.len());
    for b in s.bytes() {
        if b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.' | b'~') || (keep_slash && b == b'/') {
            out.push(b as char);
        } else {
            out.push_str(&format!("%{b:02X}"));
        }
    }
    out
}

fn percent_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    let hex_digit = |b: u8| (b as char).to_digit(16).map(|d| d as u8);
    while i < bytes.len() {
        if bytes[i] == b'%'
            && i + 2 < bytes.len()
            && let (Some(hi), Some(lo)) = (hex_digit(bytes[i + 1]), hex_digit(bytes[i + 2]))
        {
            let v = hi << 4 | lo;
            out.push(v);
            i += 3;
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn canonical_query(query: Option<&str>) -> String {
    let mut pairs: Vec<(String, String)> = query
        .unwrap_or_default()
        .split('&')
        .filter(|p| !p.is_empty())
        .map(|p| {
            let (k, v) = p.split_once('=').unwrap_or((p, ""));
            (uri_encode(&percent_decode(k), false), uri_encode(&percent_decode(v), false))
        })
        .collect();
    pairs.sort();
    pairs.iter().map(|(k, v)| format!("{k}={v}")).collect::<Vec<_>>().join("&")
}

/// Trim and collapse runs of spaces.
fn canonical_header_value(v: &str) -> String {
    v.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Sign a request. Errors only on an unparseable URL.
pub(crate) fn sign(req: SignableRequest<'_>, params: SigningParams<'_>) -> Result<Signature, String> {
    let url = reqwest::Url::parse(req.url).map_err(|e| format!("invalid URL: {e}"))?;
    let host = match (url.host_str(), url.port()) {
        (Some(h), Some(p)) => format!("{h}:{p}"),
        (Some(h), None) => h.to_owned(),
        (None, _) => return Err("URL has no host".into()),
    };
    let (stamp, date) = amz_date(params.time);
    let payload_hash = sha256_hex(req.body);

    let mut added: Vec<(String, String)> = vec![("x-amz-date".into(), stamp.clone())];
    if let Some(token) = params.session_token {
        added.push(("x-amz-security-token".into(), token.to_owned()));
    }
    if params.content_sha256_header {
        added.push(("x-amz-content-sha256".into(), payload_hash.clone()));
    }

    let mut headers: Vec<(String, String)> = vec![("host".into(), host)];
    for (name, value) in req.headers.iter().chain(&added) {
        let name = name.to_ascii_lowercase();
        if name == "host" || name == "authorization" {
            continue;
        }
        let value = canonical_header_value(value);
        match headers.iter_mut().find(|(n, _)| *n == name) {
            Some((_, existing)) => {
                existing.push(',');
                existing.push_str(&value);
            }
            None => headers.push((name, value)),
        }
    }
    headers.sort_by(|a, b| a.0.cmp(&b.0));
    let signed_headers = headers.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>().join(";");
    let canonical_headers: String = headers.iter().map(|(n, v)| format!("{n}:{v}\n")).collect();

    let path = match url.path() {
        "" => "/",
        p => p,
    };
    let canonical_request = format!(
        "{}\n{}\n{}\n{canonical_headers}\n{signed_headers}\n{payload_hash}",
        req.method,
        uri_encode(path, true),
        canonical_query(url.query()),
    );

    let scope = format!("{date}/{}/{}/aws4_request", params.region, params.service);
    let string_to_sign = format!("{ALGORITHM}\n{stamp}\n{scope}\n{}", sha256_hex(canonical_request.as_bytes()));

    let k_date = hmac_sha256(format!("AWS4{}", params.secret_access_key).as_bytes(), date.as_bytes());
    let k_region = hmac_sha256(k_date.as_ref(), params.region.as_bytes());
    let k_service = hmac_sha256(k_region.as_ref(), params.service.as_bytes());
    let k_signing = hmac_sha256(k_service.as_ref(), b"aws4_request");
    let signature = hex(hmac_sha256(k_signing.as_ref(), string_to_sign.as_bytes()).as_ref());

    added.push((
        "authorization".into(),
        format!("{ALGORITHM} Credential={}/{scope}, SignedHeaders={signed_headers}, Signature={signature}", params.access_key_id),
    ));
    Ok(Signature { canonical_request, string_to_sign, signature, headers: added })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    /// 2015-08-30T12:36:00Z, the AWS test-suite timestamp.
    fn suite_time() -> SystemTime {
        UNIX_EPOCH + Duration::from_secs(1_440_938_160)
    }

    fn suite_params(token: Option<&'static str>, sha_header: bool) -> SigningParams<'static> {
        SigningParams {
            access_key_id: "AKIDEXAMPLE",
            secret_access_key: "wJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEY",
            session_token: token,
            region: "us-east-1",
            service: "service",
            time: suite_time(),
            content_sha256_header: sha_header,
        }
    }

    fn h(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
        pairs.iter().map(|(a, b)| ((*a).to_owned(), (*b).to_owned())).collect()
    }

    #[test]
    fn dates() {
        assert_eq!(amz_date(suite_time()), ("20150830T123600Z".into(), "20150830".into()));
        assert_eq!(amz_date(UNIX_EPOCH + Duration::from_secs(1_704_164_645)).0, "20240102T030405Z");
        assert_eq!(amz_date(UNIX_EPOCH).0, "19700101T000000Z");
        // Leap day.
        assert_eq!(amz_date(UNIX_EPOCH + Duration::from_secs(951_782_400)).1, "20000229");
    }

    /// Cases from the AWS SigV4 test suite (`aws-sig-v4-test-suite`, as
    /// shipped in `aws-sigv4`'s `aws-signing-test-suite/v4`, Apache-2.0):
    /// `(name, method, url, headers, body, session token, sign body,
    /// expected canonical request, expected signature)`.
    #[test]
    #[allow(clippy::type_complexity)]
    fn aws_test_suite() {
        let empty = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
        let cases: &[(&str, &str, &str, &[(&str, &str)], &[u8], Option<&str>, bool, String, &str)] = &[
            (
                "get-vanilla",
                "GET",
                "https://example.amazonaws.com/",
                &[],
                b"",
                None,
                false,
                format!("GET\n/\n\nhost:example.amazonaws.com\nx-amz-date:20150830T123600Z\n\nhost;x-amz-date\n{empty}"),
                "5fa00fa31553b73ebf1942676e86291e8372ff2a2260956d9b8aae1d763fbf31",
            ),
            (
                "post-vanilla",
                "POST",
                "https://example.amazonaws.com/",
                &[],
                b"",
                None,
                false,
                format!("POST\n/\n\nhost:example.amazonaws.com\nx-amz-date:20150830T123600Z\n\nhost;x-amz-date\n{empty}"),
                "5da7c1a2acd57cee7505fc6676e4e544621c30862966e37dddb68e92efbe5d6b",
            ),
            (
                "get-vanilla-query-order-key-case",
                "GET",
                "https://example.amazonaws.com/?Param2=value2&Param1=value1",
                &[],
                b"",
                None,
                false,
                format!("GET\n/\nParam1=value1&Param2=value2\nhost:example.amazonaws.com\nx-amz-date:20150830T123600Z\n\nhost;x-amz-date\n{empty}"),
                "b97d918cfa904a5beff61c982a1b6f458b799221646efd99d3219ec94cdf2500",
            ),
            (
                "post-vanilla-query",
                "POST",
                "https://example.amazonaws.com/?Param1=value1",
                &[],
                b"",
                None,
                false,
                format!("POST\n/\nParam1=value1\nhost:example.amazonaws.com\nx-amz-date:20150830T123600Z\n\nhost;x-amz-date\n{empty}"),
                "28038455d6de14eafc1f9222cf5aa6f1a96197d7deb8263271d420d138af7f11",
            ),
            (
                "get-vanilla-query-unreserved",
                "GET",
                "https://example.amazonaws.com/?-._~0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz=-._~0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz",
                &[],
                b"",
                None,
                false,
                format!("GET\n/\n-._~0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz=-._~0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz\nhost:example.amazonaws.com\nx-amz-date:20150830T123600Z\n\nhost;x-amz-date\n{empty}"),
                "9c3e54bfcdf0b19771a7f523ee5669cdf59bc7cc0884027167c21bb143a40197",
            ),
            (
                "get-unreserved",
                "GET",
                "https://example.amazonaws.com/-._~0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz",
                &[],
                b"",
                None,
                false,
                format!("GET\n/-._~0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz\n\nhost:example.amazonaws.com\nx-amz-date:20150830T123600Z\n\nhost;x-amz-date\n{empty}"),
                "07ef7494c76fa4850883e2b006601f940f8a34d404d0cfa977f52a65bbf5f24f",
            ),
            (
                "get-header-value-trim",
                "GET",
                "https://example.amazonaws.com/",
                &[("My-Header1", " value1"), ("My-Header2", " \"a   b   c\"")],
                b"",
                None,
                false,
                format!("GET\n/\n\nhost:example.amazonaws.com\nmy-header1:value1\nmy-header2:\"a b c\"\nx-amz-date:20150830T123600Z\n\nhost;my-header1;my-header2;x-amz-date\n{empty}"),
                "acc3ed3afb60bb290fc8d2dd0098b9911fcaa05412b367055dee359757a9c736",
            ),
            (
                "post-header-key-sort",
                "POST",
                "https://example.amazonaws.com/",
                &[("My-Header1", "value1")],
                b"",
                None,
                false,
                format!("POST\n/\n\nhost:example.amazonaws.com\nmy-header1:value1\nx-amz-date:20150830T123600Z\n\nhost;my-header1;x-amz-date\n{empty}"),
                "c5410059b04c1ee005303aed430f6e6645f61f4dc9e1461ec8f8916fdf18852c",
            ),
            (
                "get-vanilla-with-session-token",
                "GET",
                "https://example.amazonaws.com/",
                &[],
                b"",
                Some("6e86291e8372ff2a2260956d9b8aae1d763fbf315fa00fa31553b73ebf194267"),
                false,
                format!("GET\n/\n\nhost:example.amazonaws.com\nx-amz-date:20150830T123600Z\nx-amz-security-token:6e86291e8372ff2a2260956d9b8aae1d763fbf315fa00fa31553b73ebf194267\n\nhost;x-amz-date;x-amz-security-token\n{empty}"),
                "07ec1639c89043aa0e3e2de82b96708f198cceab042d4a97044c66dd9f74e7f8",
            ),
            (
                "post-x-www-form-urlencoded",
                "POST",
                "https://example.amazonaws.com/",
                &[("Content-Type", "application/x-www-form-urlencoded"), ("Content-Length", "13")],
                b"Param1=value1",
                None,
                true,
                "POST\n/\n\ncontent-length:13\ncontent-type:application/x-www-form-urlencoded\nhost:example.amazonaws.com\nx-amz-content-sha256:9095672bbd1f56dfc5b65f3e153adc8731a4a654192329106275f4c7b24d0b6e\nx-amz-date:20150830T123600Z\n\ncontent-length;content-type;host;x-amz-content-sha256;x-amz-date\n9095672bbd1f56dfc5b65f3e153adc8731a4a654192329106275f4c7b24d0b6e".to_owned(),
                "d3875051da38690788ef43de4db0d8f280229d82040bfac253562e56c3f20e0b",
            ),
        ];
        for (name, method, url, headers, body, token, sha, canonical, signature) in cases {
            let sig = sign(SignableRequest { method, url, headers: &h(headers), body }, suite_params(*token, *sha)).unwrap();
            assert_eq!(&sig.canonical_request, canonical, "{name}: canonical request");
            assert_eq!(sig.signature, *signature, "{name}: signature");
            let auth = &sig.headers.last().unwrap().1;
            assert!(
                auth.starts_with("AWS4-HMAC-SHA256 Credential=AKIDEXAMPLE/20150830/us-east-1/service/aws4_request, SignedHeaders="),
                "{name}: {auth}"
            );
            assert!(auth.ends_with(&format!("Signature={signature}")));
        }
    }

    #[test]
    fn string_to_sign_matches_suite() {
        let sig = sign(SignableRequest { method: "GET", url: "https://example.amazonaws.com/", headers: &[], body: b"" }, suite_params(None, false))
            .unwrap();
        assert_eq!(
            sig.string_to_sign,
            "AWS4-HMAC-SHA256\n20150830T123600Z\n20150830/us-east-1/service/aws4_request\nbb579772317eb040ac9ed261061d46c1f17a8133879d6129b6e1c25292927e63"
        );
    }

    /// Golden vector produced by botocore's `SigV4Auth` for a Bedrock
    /// `InvokeModel` call (as recorded in LiteLLM's Rust port).
    #[test]
    fn botocore_bedrock_golden_vector() {
        let sig = sign(
            SignableRequest {
                method: "POST",
                url: "https://bedrock-runtime.us-east-1.amazonaws.com/model/amazon.titan-text-express-v1/invoke",
                headers: &h(&[("Content-Type", "application/json")]),
                body: br#"{"input":"hello"}"#,
            },
            SigningParams {
                access_key_id: "AKIDEXAMPLE",
                secret_access_key: "wJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEY",
                session_token: Some("session-token"),
                region: "us-east-1",
                service: "bedrock",
                time: UNIX_EPOCH + Duration::from_secs(1_704_164_645),
                content_sha256_header: false,
            },
        )
        .unwrap();
        assert_eq!(
            sig.headers,
            h(&[
                ("x-amz-date", "20240102T030405Z"),
                ("x-amz-security-token", "session-token"),
                (
                    "authorization",
                    "AWS4-HMAC-SHA256 Credential=AKIDEXAMPLE/20240102/us-east-1/bedrock/aws4_request, SignedHeaders=content-type;host;x-amz-date;x-amz-security-token, Signature=55c027ef47527d3ad63f1735f9d099efdbc99f296ff914bd94e727e24ec0e464"
                ),
            ])
        );
    }

    #[test]
    fn encoded_paths_are_encoded_again_and_ports_kept() {
        let sig = sign(
            SignableRequest {
                method: "POST",
                url: "http://127.0.0.1:8080/model/arn%3Aaws%3Abedrock%3Aus-east-1%3A1%3Ainference-profile%2Fx/converse",
                headers: &[],
                body: b"{}",
            },
            suite_params(None, false),
        )
        .unwrap();
        let mut lines = sig.canonical_request.lines();
        assert_eq!(lines.next(), Some("POST"));
        assert_eq!(lines.next(), Some("/model/arn%253Aaws%253Abedrock%253Aus-east-1%253A1%253Ainference-profile%252Fx/converse"));
        assert!(sig.canonical_request.contains("host:127.0.0.1:8080\n"));
        assert!(sign(SignableRequest { method: "GET", url: "not a url", headers: &[], body: b"" }, suite_params(None, false)).is_err());
    }
}
