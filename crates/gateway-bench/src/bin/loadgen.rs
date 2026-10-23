//! An HTTP/1.1 load generator for OpenAI-compatible endpoints.
//!
//! Closed loop (`--concurrency N`): N workers, each with its own keep-alive
//! connection, send back-to-back requests. Open loop (`--rate R`): requests
//! are scheduled every 1/R s and handed to up to `--concurrency` connections;
//! latency is measured from the scheduled time, so queueing behind a slow
//! server counts (no coordinated omission).
//!
//! Only requests that complete inside the measurement window (after
//! `--warmup`) are recorded. Latency and time to first body byte (streams)
//! go into HDR histograms (1 us resolution, 3 significant digits).
//!
//! `--watch NAME=PID` (repeatable) samples the CPU time (utime+stime) of PID and all its
//! descendants at the start and end of the window and their resident memory
//! every 100 ms, from /proc.

use bytes::Bytes;
use gateway_bench::{Args, runtime};
use hdrhistogram::Histogram;
use http_body_util::{BodyExt, Full};
use hyper::Request;
use hyper::client::conn::http1::SendRequest;
use hyper_util::rt::TokioIo;
use serde_json::{Value, json};
use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const USAGE: &str = "usage: loadgen --url http://127.0.0.1:4000/v1/chat/completions
  [--scenario chat|stream|embeddings] [--model NAME] [--body-file FILE] [--stream]
  [--key SK] [--header 'Name: value']...
  [--concurrency 16] [--rate RPS] [--duration 10] [--warmup 5] [--threads 0]
  [--watch NAME=PID]... [--label TEXT] [--out result.json] [--max-errors-logged 3]";

const SYSTEM: &str = "You are a helpful assistant that answers questions about software \
architecture concisely and accurately. Prefer short paragraphs and concrete examples.";
const USER: &str = "Our service sends every LLM call through a proxy that checks a virtual \
key, enforces per-key budgets and rate limits, picks a deployment and records the spend. \
What are the main sources of latency such a proxy adds, and how would you measure them?";
const EMBED_INPUT: &str = "A gateway authenticates the caller, checks its budget and rate \
limits, routes the request to a deployment and records what it cost.";

fn default_body(scenario: &str, model: Option<&str>) -> Value {
    match scenario {
        "embeddings" => json!({
            "model": model.unwrap_or("text-embedding-3-small"),
            "input": EMBED_INPUT,
        }),
        _ => {
            let mut b = json!({
                "model": model.unwrap_or("gpt-4o-mini"),
                "messages": [
                    {"role": "system", "content": SYSTEM},
                    {"role": "user", "content": USER}
                ],
                "max_tokens": 256,
                "temperature": 0.2,
            });
            if scenario == "stream" {
                b["stream"] = json!(true);
                b["stream_options"] = json!({"include_usage": true});
            }
            b
        }
    }
}

struct Target {
    host_port: String,
    authority: String,
    path: String,
    headers: Vec<(String, String)>,
    body: Bytes,
    stream: bool,
}

#[derive(Default)]
struct Stats {
    latency: Option<Histogram<u64>>,
    ttfb: Option<Histogram<u64>>,
    ok: u64,
    bytes: u64,
    errors: BTreeMap<String, u64>,
    samples: Vec<String>,
}

impl Stats {
    fn new() -> Stats {
        Stats {
            latency: Some(Histogram::new_with_bounds(1, 120_000_000, 3).expect("histogram")),
            ttfb: Some(Histogram::new_with_bounds(1, 120_000_000, 3).expect("histogram")),
            ..Default::default()
        }
    }
    fn merge(&mut self, o: Stats) {
        self.latency
            .as_mut()
            .unwrap()
            .add(o.latency.unwrap())
            .expect("merge");
        self.ttfb
            .as_mut()
            .unwrap()
            .add(o.ttfb.unwrap())
            .expect("merge");
        self.ok += o.ok;
        self.bytes += o.bytes;
        for (k, v) in o.errors {
            *self.errors.entry(k).or_default() += v;
        }
        self.samples.extend(o.samples);
    }
}

struct Window {
    start: Instant,
    measure_from: Instant,
    end: Instant,
}

impl Window {
    fn records(&self, done: Instant) -> bool {
        done >= self.measure_from && done <= self.end
    }
}

fn parse_url(url: &str) -> Result<(String, String), String> {
    let rest = url
        .strip_prefix("http://")
        .ok_or("only http:// URLs are supported")?;
    let (authority, path) = match rest.find('/') {
        Some(i) => (&rest[..i], &rest[i..]),
        None => (rest, "/"),
    };
    Ok((authority.to_string(), path.to_string()))
}

async fn connect(t: &Target) -> Result<SendRequest<Full<Bytes>>, String> {
    let tcp = tokio::net::TcpStream::connect(&t.host_port)
        .await
        .map_err(|e| format!("connect: {e}"))?;
    let _ = tcp.set_nodelay(true);
    let (sender, conn) = hyper::client::conn::http1::handshake(TokioIo::new(tcp))
        .await
        .map_err(|e| format!("handshake: {e}"))?;
    tokio::spawn(async move {
        let _ = conn.await;
    });
    Ok(sender)
}

/// One request on `sender`. Returns (status, first-body-byte instant, bytes,
/// complete) or a transport error.
async fn one(
    t: &Target,
    sender: &mut SendRequest<Full<Bytes>>,
) -> Result<(u16, Option<Instant>, u64, bool), String> {
    let mut req = Request::post(t.path.as_str())
        .header("host", t.authority.as_str())
        .header("content-type", "application/json")
        .header(
            "accept",
            if t.stream {
                "text/event-stream"
            } else {
                "application/json"
            },
        );
    for (k, v) in &t.headers {
        req = req.header(k.as_str(), v.as_str());
    }
    let req = req
        .body(Full::new(t.body.clone()))
        .map_err(|e| format!("request: {e}"))?;
    sender.ready().await.map_err(|e| format!("ready: {e}"))?;
    let resp = sender
        .send_request(req)
        .await
        .map_err(|e| format!("send: {e}"))?;
    let status = resp.status().as_u16();
    let mut body = resp.into_body();
    let mut first = None;
    let mut n = 0u64;
    let mut tail: Vec<u8> = Vec::new();
    while let Some(frame) = body.frame().await {
        let frame = frame.map_err(|e| format!("body: {e}"))?;
        if let Some(data) = frame.data_ref() {
            if data.is_empty() {
                continue;
            }
            if first.is_none() {
                first = Some(Instant::now());
            }
            n += data.len() as u64;
            tail.extend_from_slice(&data[data.len().saturating_sub(32)..]);
            if tail.len() > 64 {
                tail.drain(..tail.len() - 32);
            }
        }
    }
    let tail = String::from_utf8_lossy(&tail);
    let complete = if t.stream {
        tail.contains("[DONE]")
    } else {
        tail.trim_end().ends_with('}')
    };
    Ok((status, first, n, complete))
}

fn status_key(status: u16) -> String {
    format!("http_{status}")
}

async fn worker(
    t: Arc<Target>,
    w: Arc<Window>,
    rate: Option<f64>,
    next: Arc<AtomicU64>,
    max_samples: usize,
) -> Stats {
    let mut s = Stats::new();
    let mut sender: Option<SendRequest<Full<Bytes>>> = None;
    loop {
        // Closed loop: start now. Open loop: take the next slot of the schedule.
        let scheduled = match rate {
            None => Instant::now(),
            Some(r) => {
                let i = next.fetch_add(1, Ordering::Relaxed);
                let at = w.start + Duration::from_secs_f64(i as f64 / r);
                if at >= w.end {
                    break;
                }
                tokio::time::sleep_until(at.into()).await;
                at
            }
        };
        if scheduled >= w.end {
            break;
        }
        if sender.is_none() {
            match connect(&t).await {
                Ok(c) => sender = Some(c),
                Err(e) => {
                    if w.records(Instant::now()) {
                        *s.errors.entry("connect".into()).or_default() += 1;
                        if s.samples.len() < max_samples {
                            s.samples.push(e);
                        }
                    }
                    tokio::time::sleep(Duration::from_millis(10)).await;
                    continue;
                }
            }
        }
        let res = one(&t, sender.as_mut().unwrap()).await;
        let done = Instant::now();
        let recorded = w.records(done);
        match res {
            Ok((200, first, n, true)) => {
                if recorded {
                    s.ok += 1;
                    s.bytes += n;
                    let us = (done - scheduled).as_micros().max(1) as u64;
                    s.latency.as_mut().unwrap().saturating_record(us);
                    if let Some(f) = first {
                        let us = (f - scheduled).as_micros().max(1) as u64;
                        s.ttfb.as_mut().unwrap().saturating_record(us);
                    }
                }
            }
            Ok((status, _, _, complete)) => {
                if recorded {
                    let k = if status == 200 && !complete {
                        "incomplete".into()
                    } else {
                        status_key(status)
                    };
                    *s.errors.entry(k).or_default() += 1;
                }
            }
            Err(e) => {
                sender = None;
                if recorded {
                    *s.errors.entry("transport".into()).or_default() += 1;
                    if s.samples.len() < max_samples {
                        s.samples.push(e);
                    }
                }
            }
        }
        if sender.as_ref().is_some_and(|c| c.is_closed()) {
            sender = None;
        }
    }
    s
}

/// Process-tree sampling from /proc.
mod procfs {
    use std::collections::HashMap;

    pub const CLK_TCK: f64 = 100.0;

    fn stat(pid: u32) -> Option<(u32, u64)> {
        let s = std::fs::read_to_string(format!("/proc/{pid}/stat")).ok()?;
        // Fields after the parenthesised command name.
        let rest = &s[s.rfind(')')? + 2..];
        let f: Vec<&str> = rest.split_whitespace().collect();
        let ppid = f.get(1)?.parse().ok()?;
        let utime: u64 = f.get(11)?.parse().ok()?;
        let stime: u64 = f.get(12)?.parse().ok()?;
        Some((ppid, utime + stime))
    }

    /// `root` and all its descendants.
    pub fn tree(root: u32) -> Vec<u32> {
        let mut parent: HashMap<u32, u32> = HashMap::new();
        if let Ok(dir) = std::fs::read_dir("/proc") {
            for e in dir.flatten() {
                if let Some(pid) = e.file_name().to_str().and_then(|n| n.parse::<u32>().ok())
                    && let Some((ppid, _)) = stat(pid)
                {
                    parent.insert(pid, ppid);
                }
            }
        }
        let mut out = vec![root];
        let mut i = 0;
        while i < out.len() {
            let p = out[i];
            out.extend(parent.iter().filter(|&(_, &pp)| pp == p).map(|(&c, _)| c));
            i += 1;
        }
        out
    }

    /// CPU ticks per pid.
    pub fn cpu(pids: &[u32]) -> HashMap<u32, u64> {
        pids.iter()
            .filter_map(|&p| stat(p).map(|(_, t)| (p, t)))
            .collect()
    }

    fn status_kb(pid: u32, field: &str) -> u64 {
        std::fs::read_to_string(format!("/proc/{pid}/status"))
            .ok()
            .and_then(|s| {
                s.lines()
                    .find(|l| l.starts_with(field))
                    .and_then(|l| l.split_whitespace().nth(1))
                    .and_then(|v| v.parse().ok())
            })
            .unwrap_or(0)
    }

    pub fn rss_kb(pids: &[u32]) -> u64 {
        pids.iter().map(|&p| status_kb(p, "VmRSS:")).sum()
    }

    pub fn hwm_kb(pids: &[u32]) -> u64 {
        pids.iter().map(|&p| status_kb(p, "VmHWM:")).sum()
    }

    /// Proportional set size (shared pages split between sharers).
    pub fn pss_kb(pids: &[u32]) -> u64 {
        pids.iter()
            .map(|&p| {
                std::fs::read_to_string(format!("/proc/{p}/smaps_rollup"))
                    .ok()
                    .and_then(|s| {
                        s.lines()
                            .find(|l| l.starts_with("Pss:"))
                            .and_then(|l| l.split_whitespace().nth(1))
                            .and_then(|v| v.parse().ok())
                    })
                    .unwrap_or(0)
            })
            .sum()
    }
}

struct Usage {
    cpu_seconds: f64,
    elapsed: f64,
    rss_peak_kb: u64,
    hwm_kb: u64,
    pss_kb: u64,
    processes: usize,
}

/// CPU time of `pid`'s process tree over the measurement window, and its
/// memory (peak of the summed RSS sampled every 100 ms; summed VmHWM and PSS
/// at the end).
///
/// Runs on its own OS thread: reading /proc is blocking and scanning it for
/// descendants takes milliseconds, which would stall requests on a Tokio
/// worker. The process tree is rescanned once a second.
fn sample(pid: u32, w: &Window, stop: &AtomicBool) -> Usage {
    std::thread::sleep(w.measure_from.saturating_duration_since(Instant::now()));
    let mut pids = procfs::tree(pid);
    let cpu0 = procfs::cpu(&pids);
    let t0 = Instant::now();
    let mut rss_peak_kb = 0u64;
    let mut rescanned = Instant::now();
    while !stop.load(Ordering::Relaxed) && Instant::now() < w.end {
        if rescanned.elapsed() >= Duration::from_secs(1) {
            pids = procfs::tree(pid);
            rescanned = Instant::now();
        }
        rss_peak_kb = rss_peak_kb.max(procfs::rss_kb(&pids));
        std::thread::sleep(Duration::from_millis(100));
    }
    let pids = procfs::tree(pid);
    let cpu1 = procfs::cpu(&pids);
    let elapsed = t0.elapsed().as_secs_f64();
    let ticks: u64 = cpu1
        .iter()
        .map(|(p, t)| t.saturating_sub(*cpu0.get(p).unwrap_or(&0)))
        .sum();
    Usage {
        cpu_seconds: ticks as f64 / procfs::CLK_TCK,
        elapsed,
        rss_peak_kb: rss_peak_kb.max(procfs::rss_kb(&pids)),
        hwm_kb: procfs::hwm_kb(&pids),
        pss_kb: procfs::pss_kb(&pids),
        processes: pids.len(),
    }
}

fn percentiles(h: &Histogram<u64>) -> Value {
    if h.is_empty() {
        return Value::Null;
    }
    let ms = |us: u64| (us as f64 / 1000.0 * 1000.0).round() / 1000.0;
    json!({
        "p50": ms(h.value_at_quantile(0.50)),
        "p90": ms(h.value_at_quantile(0.90)),
        "p99": ms(h.value_at_quantile(0.99)),
        "p999": ms(h.value_at_quantile(0.999)),
        "max": ms(h.max()),
        "mean": (h.mean() / 1000.0 * 1000.0).round() / 1000.0,
    })
}

fn main() {
    let a = Args::parse(USAGE, &["stream"]);
    let Some(url) = a.opt("url") else {
        eprintln!("--url is required\n{USAGE}");
        std::process::exit(2)
    };
    let (authority, path) = parse_url(&url).unwrap_or_else(|e| {
        eprintln!("{e}");
        std::process::exit(2)
    });
    let scenario: String = a.get("scenario", "chat".to_string());
    let body = match a.opt("body-file") {
        Some(f) => std::fs::read(&f).unwrap_or_else(|e| {
            eprintln!("{f}: {e}");
            std::process::exit(2)
        }),
        None => default_body(&scenario, a.opt("model").as_deref())
            .to_string()
            .into_bytes(),
    };
    let stream = a.flag("stream")
        || serde_json::from_slice::<Value>(&body)
            .ok()
            .and_then(|v| v.get("stream").and_then(Value::as_bool))
            .unwrap_or(false);
    let mut headers: Vec<(String, String)> = a
        .all("header")
        .iter()
        .filter_map(|h| {
            h.split_once(':')
                .map(|(k, v)| (k.trim().to_string(), v.trim().to_string()))
        })
        .collect();
    if let Some(k) = a.opt("key") {
        headers.push(("authorization".into(), format!("Bearer {k}")));
    }
    let concurrency: usize = a.get::<usize>("concurrency", 16).max(1);
    let rate: Option<f64> = a.opt("rate").map(|r| r.parse().expect("--rate"));
    let duration: f64 = a.get("duration", 10.0);
    let warmup: f64 = a.get("warmup", 5.0);
    let watch: Vec<(String, u32)> = a
        .all("watch")
        .iter()
        .map(|w| {
            let (name, pid) = w.split_once('=').unwrap_or(("process", w));
            (name.to_string(), pid.parse().expect("--watch NAME=PID"))
        })
        .collect();
    let max_samples: usize = a.get("max-errors-logged", 3);
    let target = Arc::new(Target {
        host_port: authority.clone(),
        authority,
        path,
        headers,
        body: Bytes::from(body),
        stream,
    });

    let rt = runtime(a.get("threads", 0));
    let result = rt.block_on(async move {
        let start = Instant::now() + Duration::from_millis(50);
        let w = Arc::new(Window {
            start,
            measure_from: start + Duration::from_secs_f64(warmup),
            end: start + Duration::from_secs_f64(warmup + duration),
        });
        let next = Arc::new(AtomicU64::new(0));
        let tasks: Vec<_> = (0..concurrency)
            .map(|_| {
                tokio::spawn(worker(
                    target.clone(),
                    w.clone(),
                    rate,
                    next.clone(),
                    max_samples,
                ))
            })
            .collect();

        // Process sampling.
        let stop = Arc::new(AtomicBool::new(false));
        let samplers: Vec<_> = watch
            .into_iter()
            .map(|(name, pid)| {
                let (w, stop) = (w.clone(), stop.clone());
                std::thread::spawn(move || (name, pid, sample(pid, &w, &stop)))
            })
            .collect();

        let mut total = Stats::new();
        for t in tasks {
            total.merge(t.await.expect("worker"));
        }
        stop.store(true, Ordering::Relaxed);
        let mut proc = Vec::new();
        for s in samplers {
            proc.push(s.join().expect("sampler"));
        }
        (total, proc)
    });
    let (stats, proc) = result;

    let lat = stats.latency.as_ref().unwrap();
    let ttfb = stats.ttfb.as_ref().unwrap();
    let throughput = stats.ok as f64 / duration;
    let errors: u64 = stats.errors.values().sum();
    let mut out = json!({
        "label": a.opt("label"),
        "url": url,
        "scenario": scenario,
        "stream": stream,
        "mode": if rate.is_some() { "open" } else { "closed" },
        "concurrency": concurrency,
        "rate": rate,
        "duration_s": duration,
        "warmup_s": warmup,
        "requests_ok": stats.ok,
        "errors_total": errors,
        "errors": stats.errors,
        "error_samples": stats.samples,
        "throughput_rps": (throughput * 10.0).round() / 10.0,
        "bytes_received": stats.bytes,
        "latency_ms": percentiles(lat),
        "ttfb_ms": if stream { percentiles(ttfb) } else { Value::Null },
        "timestamp": SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0),
    });
    let mut procs = serde_json::Map::new();
    for (name, pid, u) in &proc {
        let per_req = if stats.ok > 0 {
            u.cpu_seconds / stats.ok as f64 * 1e6
        } else {
            0.0
        };
        let mb = |kb: u64| (kb as f64 / 1024.0).round();
        procs.insert(
            name.clone(),
            json!({
                "pid": pid,
                "processes": u.processes,
                "cpu_seconds": (u.cpu_seconds * 100.0).round() / 100.0,
                "cpu_cores": (u.cpu_seconds / u.elapsed * 100.0).round() / 100.0,
                "cpu_us_per_request": per_req.round(),
                "rss_peak_mb": mb(u.rss_peak_kb),
                "hwm_sum_mb": mb(u.hwm_kb),
                "pss_end_mb": mb(u.pss_kb),
            }),
        );
    }
    out["processes"] = Value::Object(procs);
    let text = serde_json::to_string_pretty(&out).expect("json");
    match a.opt("out") {
        Some(f) => std::fs::write(&f, &text).unwrap_or_else(|e| eprintln!("{f}: {e}")),
        None => println!("{text}"),
    }
    let p = |v: &Value, k: &str| v.get(k).and_then(Value::as_f64).unwrap_or(f64::NAN);
    let l = &out["latency_ms"];
    let mut line = format!(
        "{} c={} rps={:.0} p50={:.2}ms p99={:.2}ms max={:.2}ms ok={} err={}",
        a.opt("label").unwrap_or_default(),
        concurrency,
        throughput,
        p(l, "p50"),
        p(l, "p99"),
        p(l, "max"),
        stats.ok,
        errors
    );
    if stream {
        line += &format!(" ttfb_p50={:.2}ms", p(&out["ttfb_ms"], "p50"));
    }
    for (name, pr) in out["processes"].as_object().into_iter().flatten() {
        line += &format!(
            " {name}:cpu={:.2}cores,rss={}MB",
            p(pr, "cpu_cores"),
            p(pr, "rss_peak_mb")
        );
    }
    if errors > 0 {
        let counts: HashMap<_, _> = stats.errors.iter().collect();
        line += &format!(" errors={counts:?} {:?}", stats.samples.first());
    }
    eprintln!("{line}");
}
