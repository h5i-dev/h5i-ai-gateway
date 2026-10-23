//! Benchmark tools for h5i-ai-gateway (see `bench/README.md`).
//!
//! - `mock-upstream`: an OpenAI-compatible upstream with configurable latency
//!   and streaming cadence.
//! - `loadgen`: a closed- or open-loop HTTP/1.1 load generator recording HDR
//!   latency histograms and the CPU time and memory of the process under test.

use std::collections::HashMap;
use std::str::FromStr;

/// `--flag value` / `--switch` command-line arguments.
pub struct Args {
    values: HashMap<String, Vec<String>>,
    usage: &'static str,
}

impl Args {
    /// Parses `std::env::args()`. `switches` take no value.
    pub fn parse(usage: &'static str, switches: &[&str]) -> Args {
        Self::from_iter(usage, switches, std::env::args().skip(1)).unwrap_or_else(|e| {
            eprintln!("{e}\n{usage}");
            std::process::exit(2)
        })
    }

    pub fn from_iter(
        usage: &'static str,
        switches: &[&str],
        args: impl IntoIterator<Item = String>,
    ) -> Result<Args, String> {
        let mut values: HashMap<String, Vec<String>> = HashMap::new();
        let mut it = args.into_iter();
        while let Some(flag) = it.next() {
            if flag == "--help" || flag == "-h" {
                println!("{usage}");
                std::process::exit(0);
            }
            let Some(name) = flag.strip_prefix("--") else {
                return Err(format!("unexpected argument {flag}"));
            };
            let (name, value) = match name.split_once('=') {
                Some((n, v)) => (n.to_string(), v.to_string()),
                None if switches.contains(&name) => (name.to_string(), "true".to_string()),
                None => {
                    let v = it.next().ok_or_else(|| format!("--{name} needs a value"))?;
                    (name.to_string(), v)
                }
            };
            values.entry(name).or_default().push(value);
        }
        Ok(Args { values, usage })
    }

    /// The last value of `--name`, parsed, or `default`.
    pub fn get<T: FromStr>(&self, name: &str, default: T) -> T {
        match self.values.get(name).and_then(|v| v.last()) {
            None => default,
            Some(v) => v.parse().unwrap_or_else(|_| {
                eprintln!("invalid value {v:?} for --{name}\n{}", self.usage);
                std::process::exit(2)
            }),
        }
    }

    pub fn opt(&self, name: &str) -> Option<String> {
        self.values.get(name).and_then(|v| v.last()).cloned()
    }

    pub fn all(&self, name: &str) -> Vec<String> {
        self.values.get(name).cloned().unwrap_or_default()
    }

    pub fn flag(&self, name: &str) -> bool {
        self.values.contains_key(name)
    }
}

/// A Tokio multi-threaded runtime with `threads` workers (0 = one per CPU
/// this process may run on, which honours `taskset`).
pub fn runtime(threads: usize) -> tokio::runtime::Runtime {
    let mut b = tokio::runtime::Builder::new_multi_thread();
    if threads > 0 {
        b.worker_threads(threads);
    }
    b.enable_all().build().expect("tokio runtime")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_flags_switches_and_equals() {
        let a = Args::from_iter(
            "",
            &["stream"],
            [
                "--port",
                "9",
                "--stream",
                "--header=a: b",
                "--header",
                "c: d",
            ]
            .map(String::from),
        )
        .unwrap();
        assert_eq!(a.get("port", 0u16), 9);
        assert!(a.flag("stream"));
        assert_eq!(a.all("header"), vec!["a: b", "c: d"]);
        assert_eq!(a.get("missing", 3u32), 3);
        assert!(Args::from_iter("", &[], ["--port".to_string()]).is_err());
    }
}
