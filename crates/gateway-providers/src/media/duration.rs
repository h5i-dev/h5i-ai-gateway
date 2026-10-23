//! How long an uploaded audio file plays, from its container header, without
//! decoding it.
//!
//! The gateway reserves a transcription's cost before the call, so it needs
//! an upper bound of the duration the provider will bill:
//!
//! | Format | Estimate | Bound |
//! |---|---|---|
//! | WAV | data bytes / byte rate | same |
//! | FLAC | STREAMINFO total samples / sample rate | same |
//! | MP4 / M4A | `mvhd` duration / timescale | same |
//! | Ogg (Opus, Vorbis) | last page's granule position / sample rate | same |
//! | MP3 with a Xing/Info/VBRI header | frames x samples per frame / sample rate | same |
//! | MP3 without one | bytes / first frame's bitrate | bytes / the format's lowest bitrate (32 kbps for MPEG-1, 8 kbps for MPEG-2/2.5) |
//! | anything else (WebM, …) | none | bytes / 6 kbps (below any codec OpenAI accepts) |
//!
//! Header-declared durations are what decoders use, so they are what the
//! provider bills; a file whose container lies about its length is charged
//! the duration the provider reports, in full.

/// The lowest bitrate assumed for a file whose format is not recognised.
pub const MIN_BITRATE_BPS: f64 = 6_000.0;

/// What an audio file's header says about its length, in seconds.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct AudioDuration {
    /// `wav`, `flac`, `mp4`, `ogg`, `mp3`, or `None` if not recognised.
    pub format: Option<&'static str>,
    /// The best estimate, if the header gives one.
    pub estimate: Option<f64>,
    /// An upper bound, at least `estimate`.
    pub bound: f64,
}

/// The duration of `data`, an uploaded audio file.
pub fn audio_duration(data: &[u8]) -> AudioDuration {
    let fallback = data.len() as f64 * 8.0 / MIN_BITRATE_BPS;
    let body = skip_id3(data);
    let found = if let Some(d) = wav(data) {
        Some(("wav", d, d))
    } else if let Some(d) = flac(body) {
        Some(("flac", d, d))
    } else if let Some(d) = mp4(data) {
        Some(("mp4", d, d))
    } else if let Some(d) = ogg(data) {
        Some(("ogg", d, d))
    } else {
        mp3(body).map(|(e, b)| ("mp3", e, b))
    };
    match found {
        Some((format, estimate, bound)) if estimate.is_finite() && estimate >= 0.0 => {
            AudioDuration { format: Some(format), estimate: Some(estimate), bound: bound.max(estimate) }
        }
        _ => AudioDuration { format: None, estimate: None, bound: fallback },
    }
}

fn u16le(d: &[u8], at: usize) -> Option<u64> {
    Some(u16::from_le_bytes(d.get(at..at + 2)?.try_into().ok()?).into())
}

fn u32le(d: &[u8], at: usize) -> Option<u64> {
    Some(u32::from_le_bytes(d.get(at..at + 4)?.try_into().ok()?).into())
}

fn u32be(d: &[u8], at: usize) -> Option<u64> {
    Some(u32::from_be_bytes(d.get(at..at + 4)?.try_into().ok()?).into())
}

fn u64be(d: &[u8], at: usize) -> Option<u64> {
    Some(u64::from_be_bytes(d.get(at..at + 8)?.try_into().ok()?))
}

fn u64le(d: &[u8], at: usize) -> Option<u64> {
    Some(u64::from_le_bytes(d.get(at..at + 8)?.try_into().ok()?))
}

/// Skip an ID3v2 tag (MP3s and some FLACs start with one).
fn skip_id3(d: &[u8]) -> &[u8] {
    if d.len() < 10 || &d[..3] != b"ID3" {
        return d;
    }
    let size = d[6..10].iter().fold(0usize, |acc, b| (acc << 7) | usize::from(b & 0x7f));
    let footer = if d[5] & 0x10 != 0 { 10 } else { 0 };
    d.get(10 + size + footer..).unwrap_or(&[])
}

fn wav(d: &[u8]) -> Option<f64> {
    if d.get(..4)? != b"RIFF" || d.get(8..12)? != b"WAVE" {
        return None;
    }
    let mut pos = 12usize;
    let mut byte_rate = None;
    while let (Some(id), Some(size)) = (d.get(pos..pos + 4), u32le(d, pos + 4)) {
        let body = pos + 8;
        if id == b"fmt " {
            byte_rate = u32le(d, body + 8).filter(|r| *r > 0);
        }
        if id == b"data" {
            let available = (d.len() - body) as u64;
            // Streamed WAVs declare 0 or 0xFFFFFFFF.
            let len = if size == 0 || size == u64::from(u32::MAX) { available } else { size.min(available) };
            return Some(len as f64 / byte_rate? as f64);
        }
        pos = body.checked_add(usize::try_from(size + (size & 1)).ok()?)?;
    }
    None
}

fn flac(d: &[u8]) -> Option<f64> {
    if d.get(..4)? != b"fLaC" || d.get(4)? & 0x7f != 0 {
        return None;
    }
    let s = d.get(18..26)?;
    let rate = (u64::from(s[0]) << 12) | (u64::from(s[1]) << 4) | (u64::from(s[2]) >> 4);
    let total = (u64::from(s[3] & 0x0f) << 32) | u32be(s, 4)?;
    (rate > 0 && total > 0).then(|| total as f64 / rate as f64)
}

/// The body of the first box of `kind` among the boxes in `d`.
fn find_box<'a>(d: &'a [u8], kind: &[u8; 4]) -> Option<&'a [u8]> {
    let mut pos = 0usize;
    while pos + 8 <= d.len() {
        let size = u32be(d, pos)?;
        let (header, size) = match size {
            0 => (8, (d.len() - pos) as u64),
            1 => (16, u64be(d, pos + 8)?),
            s => (8, s),
        };
        if size < header {
            return None;
        }
        let end = pos.saturating_add(usize::try_from(size).unwrap_or(usize::MAX)).min(d.len());
        if &d[pos + 4..pos + 8] == kind {
            return d.get(pos + header as usize..end);
        }
        pos = end;
    }
    None
}

fn mp4(d: &[u8]) -> Option<f64> {
    if d.get(4..8)? != b"ftyp" {
        return None;
    }
    let mvhd = find_box(find_box(d, b"moov")?, b"mvhd")?;
    let (timescale, duration) = match mvhd.first()? {
        0 => (u32be(mvhd, 12)?, u32be(mvhd, 16).filter(|d| *d != u64::from(u32::MAX))?),
        1 => (u32be(mvhd, 20)?, u64be(mvhd, 24).filter(|d| *d != u64::MAX)?),
        _ => return None,
    };
    // Fragmented MP4s leave the duration at 0.
    (timescale > 0 && duration > 0).then(|| duration as f64 / timescale as f64)
}

fn ogg(d: &[u8]) -> Option<f64> {
    if d.get(..4)? != b"OggS" {
        return None;
    }
    let packet = d.get(27 + usize::from(*d.get(26)?)..)?;
    let (rate, pre_skip) = if packet.starts_with(b"OpusHead") {
        (48_000, u16le(packet, 10)?)
    } else if packet.starts_with(b"\x01vorbis") {
        (u32le(packet, 12)?, 0)
    } else {
        return None;
    };
    let last = d.windows(4).rposition(|w| w == b"OggS")?;
    let granule = u64le(d, last + 6).filter(|g| *g != u64::MAX)?;
    (rate > 0).then(|| granule.saturating_sub(pre_skip) as f64 / rate as f64)
}

const MPEG1_L3_KBPS: [u64; 15] = [0, 32, 40, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320];
const MPEG2_L3_KBPS: [u64; 15] = [0, 8, 16, 24, 32, 40, 48, 56, 64, 80, 96, 112, 128, 144, 160];

/// An MPEG layer III frame header.
#[derive(Clone, Copy, PartialEq)]
struct Frame {
    /// 0: MPEG-2.5, 2: MPEG-2, 3: MPEG-1.
    version: u8,
    kbps: u64,
    rate: u64,
    mono: bool,
    len: usize,
}

fn frame_at(d: &[u8], i: usize) -> Option<Frame> {
    let h = d.get(i..i + 4)?;
    if h[0] != 0xff || h[1] & 0xe0 != 0xe0 || (h[1] >> 1) & 3 != 1 {
        return None;
    }
    let version = (h[1] >> 3) & 3;
    let bitrate = usize::from(h[2] >> 4);
    let rate_index = usize::from((h[2] >> 2) & 3);
    if version == 1 || bitrate == 0 || bitrate == 15 || rate_index == 3 {
        return None;
    }
    let (kbps, rates, coefficient) = match version {
        3 => (MPEG1_L3_KBPS[bitrate], [44_100, 48_000, 32_000], 144),
        2 => (MPEG2_L3_KBPS[bitrate], [22_050, 24_000, 16_000], 72),
        _ => (MPEG2_L3_KBPS[bitrate], [11_025, 12_000, 8_000], 72),
    };
    let rate: u64 = rates[rate_index];
    let padding = u64::from((h[2] >> 1) & 1);
    let len = usize::try_from(coefficient * kbps * 1000 / rate + padding).ok()?;
    Some(Frame { version, kbps, rate, mono: h[3] >> 6 == 3, len })
}

/// `(estimate, bound)` for an MPEG layer III stream.
fn mp3(d: &[u8]) -> Option<(f64, f64)> {
    // The first frame header within the first 64 KiB that is followed by
    // another of the same stream (or by the end of the file).
    let limit = d.len().min(64 * 1024);
    let (pos, frame) = (0..limit).find_map(|i| {
        let f = frame_at(d, i)?;
        let next = i + f.len;
        let ok = next == d.len() || frame_at(d, next).is_some_and(|g| g.version == f.version && g.rate == f.rate);
        ok.then_some((i, f))
    })?;
    let Frame { version, kbps, rate, mono, .. } = frame;
    let mpeg1 = version == 3;
    let samples_per_frame = if mpeg1 { 1152 } else { 576 };
    let side_info = match (mpeg1, mono) {
        (true, true) => 17,
        (true, false) => 32,
        (false, true) => 9,
        (false, false) => 17,
    };
    let xing = pos + 4 + side_info;
    let frames = match d.get(xing..xing + 4) {
        Some(b"Xing" | b"Info") if u32be(d, xing + 4)? & 1 != 0 => u32be(d, xing + 8),
        _ if d.get(pos + 36..pos + 40) == Some(b"VBRI") => u32be(d, pos + 36 + 14),
        _ => None,
    };
    if let Some(frames) = frames.filter(|f| *f > 0) {
        let exact = (frames * samples_per_frame) as f64 / rate as f64;
        return Some((exact, exact));
    }
    let bits = (d.len() - pos) as f64 * 8.0;
    let lowest = if mpeg1 { 32_000.0 } else { 8_000.0 };
    Some((bits / (kbps * 1000) as f64, bits / lowest))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn wav_bytes(rate: u32, channels: u16, seconds: f64) -> Vec<u8> {
        let byte_rate = rate * u32::from(channels) * 2;
        let data_len = (byte_rate as f64 * seconds) as u32;
        let mut b = b"RIFF".to_vec();
        b.extend((36 + data_len).to_le_bytes());
        b.extend(b"WAVEfmt ");
        b.extend(16u32.to_le_bytes());
        b.extend(1u16.to_le_bytes());
        b.extend(channels.to_le_bytes());
        b.extend(rate.to_le_bytes());
        b.extend(byte_rate.to_le_bytes());
        b.extend((channels * 2).to_le_bytes());
        b.extend(16u16.to_le_bytes());
        // An odd-sized chunk before the data, padded.
        b.extend(b"LIST");
        b.extend(3u32.to_le_bytes());
        b.extend(b"abc\0");
        b.extend(b"data");
        b.extend(data_len.to_le_bytes());
        b.resize(b.len() + data_len as usize, 0);
        b
    }

    #[test]
    fn wav_duration() {
        let d = audio_duration(&wav_bytes(16_000, 1, 2.5));
        assert_eq!(d.format, Some("wav"));
        assert_eq!(d.estimate, Some(2.5));
        assert_eq!(d.bound, 2.5);
        // A truncated file counts what is there.
        let mut short = wav_bytes(8_000, 2, 1.0);
        short.truncate(short.len() - 16_000);
        assert_eq!(audio_duration(&short).estimate, Some(0.5));
    }

    #[test]
    fn flac_duration() {
        let mut b = b"fLaC".to_vec();
        b.extend([0x80, 0, 0, 34]); // last block, STREAMINFO, 34 bytes
        let mut info = vec![0u8; 34];
        // 44100 Hz = 0xAC44 in 20 bits; 441000 samples = 10 s.
        info[10] = 0x0a;
        info[11] = 0xc4;
        info[12] = 0x40 | 0x02;
        info[13] = 0xf0;
        info[14..18].copy_from_slice(&441_000u32.to_be_bytes());
        b.extend(info);
        let d = audio_duration(&b);
        assert_eq!(d.format, Some("flac"));
        assert_eq!(d.estimate, Some(10.0));
    }

    fn mp4_box(kind: &[u8; 4], body: &[u8]) -> Vec<u8> {
        let mut b = ((body.len() + 8) as u32).to_be_bytes().to_vec();
        b.extend(kind);
        b.extend(body);
        b
    }

    #[test]
    fn mp4_duration() {
        let mut mvhd = vec![0u8; 100];
        mvhd[12..16].copy_from_slice(&1000u32.to_be_bytes());
        mvhd[16..20].copy_from_slice(&61_500u32.to_be_bytes());
        let mut file = mp4_box(b"ftyp", b"M4A \0\0\0\0");
        file.extend(mp4_box(b"mdat", &[0u8; 64]));
        file.extend(mp4_box(b"moov", &mp4_box(b"mvhd", &mvhd)));
        let d = audio_duration(&file);
        assert_eq!(d.format, Some("mp4"));
        assert_eq!(d.estimate, Some(61.5));
    }

    fn ogg_page(granule: u64, packet: &[u8]) -> Vec<u8> {
        let mut p = b"OggS\0\0".to_vec();
        p.extend(granule.to_le_bytes());
        p.extend([0u8; 12]); // serial, sequence, checksum
        p.push(1);
        p.push(packet.len() as u8);
        p.extend(packet);
        p
    }

    #[test]
    fn ogg_opus_duration() {
        let mut head = b"OpusHead\x01\x01".to_vec();
        head.extend(312u16.to_le_bytes());
        head.extend(48_000u32.to_le_bytes());
        let mut file = ogg_page(0, &head);
        file.extend(ogg_page(0, b"OpusTags"));
        file.extend(ogg_page(48_000 * 3 + 312, &[0u8; 50]));
        let d = audio_duration(&file);
        assert_eq!(d.format, Some("ogg"));
        assert_eq!(d.estimate, Some(3.0));
    }

    fn mp3_frame(xing_frames: Option<u32>) -> Vec<u8> {
        // MPEG-1 layer III, 128 kbps, 44.1 kHz, stereo.
        let mut f = vec![0xff, 0xfb, 0x90, 0x00];
        f.resize(4 + 32, 0);
        if let Some(n) = xing_frames {
            f.extend(b"Xing");
            f.extend(1u32.to_be_bytes());
            f.extend(n.to_be_bytes());
        }
        f.resize(417, 0);
        f
    }

    #[test]
    fn mp3_duration() {
        // CBR: 100 frames of 417 bytes at 128 kbps, after an ID3 tag.
        let mut file = b"ID3\x04\0\0\0\0\0\x0a".to_vec();
        file.extend([0u8; 10]);
        for _ in 0..100 {
            file.extend(mp3_frame(None));
        }
        let d = audio_duration(&file);
        assert_eq!(d.format, Some("mp3"));
        let e = d.estimate.unwrap();
        assert!((e - 41_700.0 * 8.0 / 128_000.0).abs() < 1e-9, "{e}");
        assert!((d.bound - 4.0 * e).abs() < 1e-9);
        // A Xing header counts frames exactly: 1000 x 1152 / 44100.
        let d = audio_duration(&mp3_frame(Some(1000)));
        assert!((d.estimate.unwrap() - 1000.0 * 1152.0 / 44_100.0).abs() < 1e-9);
        assert_eq!(d.bound, d.estimate.unwrap());
    }

    #[test]
    fn unknown_formats_use_the_lowest_bitrate() {
        let d = audio_duration(&[0x1a, 0x45, 0xdf, 0xa3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(d.format, None);
        assert_eq!(d.estimate, None);
        assert_eq!(d.bound, 15.0 * 8.0 / MIN_BITRATE_BPS);
        assert_eq!(audio_duration(&[]).bound, 0.0);
        // Garbage that looks like a header does not panic.
        for junk in [&b"RIFF\xff\xff\xff\xffWAVEdata\xff\xff\xff\xff"[..], b"fLaC\0", b"\0\0\0\x01ftyp", b"OggS", b"\xff\xfb"] {
            let _ = audio_duration(junk);
        }
    }
}
