//! A `multipart/form-data` encoder (RFC 7578), built in memory so that the
//! upstream request is a plain value the tests can inspect.

use crate::providers::gen_id;

/// A form being encoded.
#[derive(Debug, Clone)]
pub struct Multipart {
    boundary: String,
    body: Vec<u8>,
}

impl Default for Multipart {
    fn default() -> Self {
        Self::new()
    }
}

/// Quotes, CR and LF cannot appear in a quoted header parameter.
fn quoted(s: &str) -> String {
    s.replace('"', "%22").replace(['\r', '\n'], " ")
}

impl Multipart {
    pub fn new() -> Self {
        Self::with_boundary(gen_id("h5i-boundary-"))
    }

    pub fn with_boundary(boundary: impl Into<String>) -> Self {
        Self { boundary: boundary.into(), body: Vec::new() }
    }

    fn head(&mut self, disposition: &str, content_type: Option<&str>) {
        self.body.extend_from_slice(b"--");
        self.body.extend_from_slice(self.boundary.as_bytes());
        self.body.extend_from_slice(b"\r\nContent-Disposition: form-data; ");
        self.body.extend_from_slice(disposition.as_bytes());
        self.body.extend_from_slice(b"\r\n");
        if let Some(ct) = content_type {
            self.body.extend_from_slice(b"Content-Type: ");
            self.body.extend_from_slice(quoted(ct).as_bytes());
            self.body.extend_from_slice(b"\r\n");
        }
        self.body.extend_from_slice(b"\r\n");
    }

    /// Add a text field.
    pub fn text(&mut self, name: &str, value: &str) -> &mut Self {
        self.head(&format!("name=\"{}\"", quoted(name)), None);
        self.body.extend_from_slice(value.as_bytes());
        self.body.extend_from_slice(b"\r\n");
        self
    }

    /// Add a file.
    pub fn file(&mut self, name: &str, filename: &str, content_type: Option<&str>, data: &[u8]) -> &mut Self {
        let disposition = format!("name=\"{}\"; filename=\"{}\"", quoted(name), quoted(filename));
        self.head(&disposition, Some(content_type.unwrap_or("application/octet-stream")));
        self.body.extend_from_slice(data);
        self.body.extend_from_slice(b"\r\n");
        self
    }

    /// The `Content-Type` header value and the encoded body.
    pub fn finish(mut self) -> (String, Vec<u8>) {
        self.body.extend_from_slice(b"--");
        self.body.extend_from_slice(self.boundary.as_bytes());
        self.body.extend_from_slice(b"--\r\n");
        (format!("multipart/form-data; boundary={}", self.boundary), self.body)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encodes_fields_and_files() {
        let mut m = Multipart::with_boundary("XYZ");
        m.text("model", "whisper-1").file("file", "a\"b.wav", Some("audio/wav"), b"RIFF").text("language", "en");
        let (ct, body) = m.finish();
        assert_eq!(ct, "multipart/form-data; boundary=XYZ");
        let expected = "--XYZ\r\nContent-Disposition: form-data; name=\"model\"\r\n\r\nwhisper-1\r\n\
            --XYZ\r\nContent-Disposition: form-data; name=\"file\"; filename=\"a%22b.wav\"\r\nContent-Type: audio/wav\r\n\r\nRIFF\r\n\
            --XYZ\r\nContent-Disposition: form-data; name=\"language\"\r\n\r\nen\r\n\
            --XYZ--\r\n";
        assert_eq!(String::from_utf8(body).unwrap(), expected);
    }

    #[test]
    fn boundaries_are_unique() {
        assert_ne!(Multipart::new().boundary, Multipart::new().boundary);
    }
}
