//! HTTP server for /api, plus static serving of frontend/ at /.
//!
//! Wire format for /api follows the spec (spec/Interface.agda
//! `to-request`): whatever comes after the blank line of the HTTP
//! request is a list of newline-separated argument lines, in the order
//! the spec gives them. Token lines that the spec leaves out
//! (`get-tweet`/`timeline` without login) arrive as an empty line.

mod response;
mod state;

use std::collections::VecDeque;
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use response::Response;
use state::ServerState;

const FRONTEND_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../frontend");

/// The request log keeps the most recent LOG_CAP entries.
const LOG_CAP: usize = 1000;

struct Request {
    method: String,
    path: String,
    body: String,
    accept: String,
}

impl Request {
    fn path_without_query(&self) -> &str {
        self.path.split('?').next().unwrap_or(&self.path)
    }

    /// Browser requests advertise HTML; curl-style tools do not.
    fn wants_html(&self) -> bool {
        self.accept.contains("text/html")
    }
}

fn read_request(stream: &mut TcpStream) -> std::io::Result<Request> {
    let mut buf: Vec<u8> = Vec::new();
    let mut chunk = [0u8; 4096];
    let header_end = loop {
        if let Some(pos) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
            break pos;
        }
        let n = stream.read(&mut chunk)?;
        if n == 0 {
            // Connection closed; if we never saw headers, fail.
            return Err(std::io::Error::new(
                std::io::ErrorKind::UnexpectedEof,
                "client closed before headers",
            ));
        }
        buf.extend_from_slice(&chunk[..n]);
    };

    let header_text = String::from_utf8_lossy(&buf[..header_end]).into_owned();
    let mut lines = header_text.split("\r\n");
    let request_line = lines.next().unwrap_or("");
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("").to_uppercase();
    let path = parts.next().unwrap_or("/").to_string();

    let mut content_length = 0usize;
    let mut accept = String::new();
    for line in lines {
        let Some((name, value)) = line.split_once(':') else {
            continue;
        };
        let (name, value) = (name.trim(), value.trim());
        if name.eq_ignore_ascii_case("content-length") {
            content_length = value.parse().unwrap_or(0);
        } else if name.eq_ignore_ascii_case("accept") {
            accept = value.to_string();
        }
    }

    let mut body: Vec<u8> = buf[header_end + 4..].to_vec();
    while body.len() < content_length {
        let n = stream.read(&mut chunk)?;
        if n == 0 {
            break;
        }
        body.extend_from_slice(&chunk[..n]);
    }

    Ok(Request {
        method,
        path,
        body: String::from_utf8_lossy(&body).into_owned(),
        accept,
    })
}

/// Split the spec-style argument block into lines. The block is
/// `unlines`-encoded, so it ends with exactly one newline (which we
/// strip); embedded newlines in a field would be indistinguishable,
/// the spec's encoding has the same limitation.
fn split_args(body: &str) -> Vec<String> {
    let trimmed = body.strip_suffix('\n').unwrap_or(body);
    trimmed
        .split('\n')
        .map(|l| l.strip_suffix('\r').unwrap_or(l).to_string())
        .collect()
}

/// Tokens are naturals; an empty line is an absent token
/// (`to-request ... nothing` omits it), anything else that does not
/// parse is treated the same as absent.
fn parse_token(line: &str) -> Option<u64> {
    line.parse().ok()
}

fn parse_nat(line: &str) -> Option<u64> {
    line.parse().ok()
}

fn api(req: &Request, state: &Mutex<ServerState>) -> Response {
    let endpoint = req.path_without_query().trim_start_matches("/api/");
    let args = split_args(&req.body);
    let arg = |i: usize| args.get(i).map(|s| s.as_str()).unwrap_or("");

    let expected_method = matches!(
        endpoint,
        "post-tweet" | "login" | "signup" | "get-tweet" | "timeline"
    );
    if !expected_method {
        return Response::PermissionError;
    }

    match endpoint {
        "post-tweet" => {
            if req.method != "POST" {
                return Response::PermissionError;
            }
            state
                .lock()
                .unwrap()
                .post_tweet(parse_token(arg(0)), args.get(1..).unwrap_or(&[]).join("\n"))
        }
        "get-tweet" => {
            if req.method != "GET" {
                return Response::PermissionError;
            }
            // Shape 1: [tweetId] (no login), shape 2: [token, tweetId]
            let (token, id) = if args.len() >= 2 {
                (parse_token(arg(0)), arg(1))
            } else {
                (None, arg(0))
            };
            let s = state.lock().unwrap();
            match parse_nat(id) {
                Some(id) => s.get_tweet(token, id),
                None => Response::PermissionError,
            }        }
        "timeline" => {
            if req.method != "GET" {
                return Response::PermissionError;
            }
            // Shape 1: [len] (no login), shape 2: [token, len]
            let (token, len) = if args.len() >= 2 {
                (parse_token(arg(0)), arg(1))
            } else {
                (None, arg(0))
            };
            match parse_nat(len) {
                Some(len) => state.lock().unwrap().timeline(token, len),
                None => state.lock().unwrap().timeline(token, 0),
            }
        }
        "login" => {
            if req.method != "POST" {
                return Response::PermissionError;
            }
            state
                .lock()
                .unwrap()
                .login(arg(0), &args.get(1..).unwrap_or(&[]).join("\n"))
        }
        "signup" => {
            if req.method != "POST" {
                return Response::PermissionError;
            }
            state
                .lock()
                .unwrap()
                .signup(arg(0), &args.get(1..).unwrap_or(&[]).join("\n"))
        }
        _ => unreachable!("endpoint set checked above"),
    }
}

fn escape_html(s: &str) -> String {
    s.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;")
}

/// Debug dump of the whole server state, plaintext; wrapped in
/// <pre> for browser-style (Accept: text/html) requests so it
/// survives the markup.
fn raw_state(req: &Request, state: &Mutex<ServerState>) -> String {
    let dump = format!("{:#?}", state.lock().unwrap());
    let (content_type, body) = if req.wants_html() {
        (
            "text/html; charset=utf-8",
            format!("<pre>{}</pre>\n", escape_html(&dump)),
        )
    } else {
        ("text/plain; charset=utf-8", format!("{dump}\n"))
    };
    response::render("200 OK", Some(content_type), &body)
}

/// One recorded request. `path` is the raw request target, query
/// string included.
struct LogEntry {
    time: String,
    method: String,
    path: String,
    status: u16,
}

type RequestLog = Arc<Mutex<VecDeque<LogEntry>>>;

// Timestamps in ISO 8601 / RFC 3339 UTC, computed without crates:
// Howard Hinnant's civil_from_days algorithm for the date part.
fn civil_from_days(days_since_epoch: i64) -> (i64, u32, u32) {
    let z = days_since_epoch + 719468;
    let era = (if z >= 0 { z } else { z - 146096 }) / 146097;
    let doe = (z - era * 146097) as u64; // [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365; // [0, 399]
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // [0, 365]
    let mp = (5 * doy + 2) / 153; // [0, 11]
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32; // [1, 31]
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32; // [1, 12]
    (y + (m <= 2) as i64, m, d)
}

fn iso8601_now() -> String {
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    let secs = now.as_secs();
    let millis = now.subsec_millis();
    let (y, m, d) = civil_from_days((secs / 86400) as i64);
    let tod = secs % 86400;
    format!(
        "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}.{:03}Z",
        y,
        m,
        d,
        tod / 3600,
        (tod % 3600) / 60,
        tod % 60,
        millis
    )
}

fn record_request(log: &RequestLog, req: &Request, out: &[u8]) {
    // The status code is the only part of the response we need.
    let status = out
        .get(9..12)
        .and_then(|b| std::str::from_utf8(b).ok())
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let entry = LogEntry {
        time: iso8601_now(),
        method: req.method.clone(),
        path: req.path.clone(),
        status,
    };
    let mut lg = log.lock().unwrap();
    lg.push_back(entry);
    while lg.len() > LOG_CAP {
        lg.pop_front();
    }
}

/// Access log as plaintext; <pre> for browser-style requests.
fn log_view(req: &Request, log: &RequestLog) -> String {
    let text = log
        .lock()
        .unwrap()
        .iter()
        .map(|e| format!("{}  {:<5}  {}  {}\n", e.time, e.method, e.path, e.status))
        .collect::<String>();
    let (content_type, body) = if req.wants_html() {
        (
            "text/html; charset=utf-8",
            format!("<pre>{}</pre>\n", escape_html(&text)),
        )
    } else {
        ("text/plain; charset=utf-8", text.clone())
    };
    response::render("200 OK", Some(content_type), &body)
}

fn content_type_for(path: &Path) -> &'static str {    match path.extension().and_then(|e| e.to_str()) {
        Some("html") => "text/html; charset=utf-8",
        Some("js") => "text/javascript; charset=utf-8",
        Some("css") => "text/css; charset=utf-8",
        Some("json") => "application/json",
        Some("png") => "image/png",
        Some("jpg" | "jpeg") => "image/jpeg",
        Some("svg") => "image/svg+xml",
        Some("ico") => "image/x-icon",
        _ => "application/octet-stream",
    }
}

fn serve_static(req: &Request, root: &Path) -> Vec<u8> {
    let path_no_query = req.path_without_query().trim_start_matches('/');
    if req.method != "GET" {
        return response::not_found().into_bytes();
    }
    // No path traversal; also reject empty components ("//") outright.
    // The root path ("/") maps to index.html before this check.
    let rel = if path_no_query.is_empty() {
        "index.html"
    } else {
        path_no_query
    };
    if rel.split('/').any(|c| c == ".." || c.is_empty()) {
        return response::not_found().into_bytes();
    }
    let mut target = root.to_path_buf();
    for c in rel.split('/') {
        target.push(c);
    }
    // Directories get their index.html.
    if target.is_dir() {
        target.push("index.html");
    }
    match std::fs::read(&target) {
        Ok(bytes) => {
            let mut headers = String::new();
            headers.push_str("HTTP/1.1 200 OK\r\n");
            headers.push_str("Content-Type: ");
            headers.push_str(content_type_for(&target));
            headers.push_str("\r\n");
            headers.push_str("Content-Length: ");
            headers.push_str(&bytes.len().to_string());
            headers.push_str("\r\n");
            headers.push_str("Connection: close\r\n\r\n");
            // Binary-safe: headers as text, then the raw file bytes.
            let mut full = headers.into_bytes();
            full.extend_from_slice(&bytes);
            full
        }
        Err(_) => response::not_found().into_bytes(),
    }
}

fn handle_conn(
    stream: &mut TcpStream,
    state: &Arc<Mutex<ServerState>>,
    log: &RequestLog,
    frontend_root: &Path,
) {
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .ok();
    stream
        .set_write_timeout(Some(Duration::from_secs(10)))
        .ok();
    let req = match read_request(stream) {
        Ok(req) => req,
        Err(_) => return,
    };
    let out: Vec<u8> = if req.path_without_query().starts_with("/api/") {
        api(&req, state).to_http().into_bytes()
    } else if req.path_without_query() == "/raw" {
        raw_state(&req, state).into_bytes()
    } else if req.path_without_query() == "/log" {
        log_view(&req, log).into_bytes()
    } else {
        serve_static(&req, frontend_root)
    };
    record_request(log, &req, &out);
    let _ = stream.write_all(&out);
    let _ = stream.flush();
    let _ = stream.shutdown(std::net::Shutdown::Both);
}

fn main() {
    let port: u16 = std::env::var("PORT")
        .ok()
        .and_then(|p| p.parse().ok())
        .unwrap_or(8080);
    let root = {
        let default = PathBuf::from(FRONTEND_DIR);
        if default.exists() {
            default
        } else {
            std::env::current_exe()
                .ok()
                .and_then(|bin| bin.parent().and_then(|dir| dir.parent()).map(Path::to_path_buf))
                .map(|out| out.join("frontend"))
                .unwrap_or(default)
        }
    };
    let addr = format!("0.0.0.0:{}", port);
    let listener = match TcpListener::bind(&addr) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("could not bind {}: {}", addr, e);
            std::process::exit(1);
        }
    };
    println!("formal-twitter backend listening on {}", addr);
    let state = Arc::new(Mutex::new(ServerState::new()));
    let log: RequestLog = Arc::new(Mutex::new(VecDeque::new()));
    for stream in listener.incoming() {
        let Ok(mut stream) = stream else { continue };
        let state = Arc::clone(&state);
        let log = Arc::clone(&log);
        let root = root.clone();
        thread::spawn(move || handle_conn(&mut stream, &state, &log, &root));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn args_splitting() {
        assert_eq!(split_args("a\nb\n"), vec!["a", "b"]);
        assert_eq!(split_args("a\nb"), vec!["a", "b"]);
        assert_eq!(split_args(""), vec![""]);
        assert_eq!(split_args("\n"), vec![""]);
        assert_eq!(split_args("token\n").len(), 1);
        assert_eq!(split_args("t\r\nw\r\n"), vec!["t", "w"]);
    }

    #[test]
    fn token_parsing() {
        assert_eq!(parse_token(""), None);
        assert_eq!(parse_token("3"), Some(3));
        assert_eq!(parse_token("x"), None);
        assert_eq!(parse_token("-1"), None);
        assert_eq!(parse_nat("123"), Some(123));
        assert_eq!(parse_nat(""), None);
    }

    #[test]
    fn api_rejects_unknown_endpoint() {
        let state = Mutex::new(ServerState::new());
        let req = Request {
            method: "GET".into(),
            path: "/api/nope".into(),
            body: String::new(),
            accept: String::new(),
        };
        let resp = api(&req, &state).to_http();
        assert!(resp.starts_with("HTTP/1.1 403"));
    }

    #[test]
    fn login_signup_over_the_wire() {
        let state = Mutex::new(ServerState::new());
        let req = |path: &str, body: &str| Request {
            method: "POST".into(),
            path: path.into(),
            body: body.into(),
            accept: String::new(),
        };
        let resp = api(&req("/api/signup", "alice\npw\n"), &state).to_http();
        assert!(resp.contains("{'session_token': '0'}"), "{resp}");

        let resp = api(&req("/api/other", "alice\npw\n"), &state).to_http();
        assert!(resp.starts_with("HTTP/1.1 403"), "{resp}");

        let resp = api(&req("/api/login", "alice\nbad\n"), &state).to_http();
        assert!(resp.starts_with("HTTP/1.1 401"), "{resp}");

        let resp = api(&req("/api/login", "alice\npw\n"), &state).to_http();
        assert!(resp.contains("{'session_token': '1'}"), "{resp}");

        let resp = api(&req("/api/post-tweet", "1\nhello world\n"), &state).to_http();
        assert!(resp.contains("{'tweet_id': '0'}"), "{resp}");

        let resp = api(&req("/api/post-tweet", "7\nnope\n"), &state).to_http();
        assert!(resp.contains("{'error': 'session_expired'}"), "{resp}");
    }

    #[test]
    fn get_and_timeline_over_the_wire() {
        let state = Mutex::new(ServerState::new());
        let req = |method: &str, path: &str, body: &str| Request {
            method: method.into(),
            path: path.into(),
            body: body.into(),
            accept: String::new(),
        };
        api(&req("POST", "/api/signup", "alice\npw\n"), &state);
        api(&req("POST", "/api/post-tweet", "0\nfirst\n"), &state);
        api(&req("POST", "/api/post-tweet", "0\nsecond\n"), &state);

        let resp = api(&req("GET", "/api/get-tweet", "0\n"), &state).to_http();
        assert!(
            resp.contains("'username': 'alice'") && resp.contains("'text': 'first'"),
            "{resp}"
        );

        // Logged-in shape: [token, tweetId]
        let resp = api(&req("GET", "/api/get-tweet", "0\n0\n"), &state).to_http();
        assert!(resp.contains("'text': 'first'"), "{resp}");

        let resp = api(
            &req("GET", "/api/get-tweet", "0\n99\n"),
            &state,
        )
        .to_http();
        assert!(resp.contains("{'error': 'access_denied'}"), "{resp}");

        let resp = api(&req("GET", "/api/timeline", "10\n"), &state).to_http();
        assert!(resp.contains("{'timeline': [0, 1]}"), "{resp}");

        let resp = api(&req("GET", "/api/timeline", "0\n1\n"), &state).to_http();
        assert!(resp.contains("{'timeline': [0]}"), "{resp}");

        // Two-line shape with an unknown token: outdated-login-token
        let resp = api(&req("GET", "/api/timeline", "999\n5\n"), &state).to_http();
        assert!(resp.contains("{'error': 'session_expired'}"), "{resp}");
    }

    #[test]
    fn raw_is_plaintext_debug_and_html_wrapped_for_browsers() {
        let state = Mutex::new(ServerState::new());
        let req = |accept: &str| Request {
            method: "GET".into(),
            path: "/raw".into(),
            body: String::new(),
            accept: accept.into(),
        };

        let resp = raw_state(&req(""), &state);
        assert!(resp.starts_with("HTTP/1.1 200 OK"), "{resp}");
        assert!(resp.contains("text/plain"), "{resp}");
        let body: String = resp.split("\r\n\r\n").nth(1).unwrap().into();
        assert!(body.contains("ServerState {"), "{body}");
        assert!(!body.contains("<pre>"), "{body}");

        let resp = raw_state(&req("text/html,application/xhtml+xml"), &state);
        assert!(resp.contains("text/html"), "{resp}");
        let body: String = resp.split("\r\n\r\n").nth(1).unwrap().into();
        assert!(body.starts_with("<pre>") && body.trim_end().ends_with("</pre>"), "{body}");
        assert!(body.contains("ServerState {"), "{body}");

        // Sensitive-ish HTML in data would be escaped
        let mut s = state.lock().unwrap();
        let _ = s.signup("a&lt;b", "pw");
        drop(s);
        let resp = raw_state(&req("text/html"), &state);
        let body: String = resp.split("\r\n\r\n").nth(1).unwrap().into();
        assert!(body.contains("&amp;lt;"), "{body}");
    }

    #[test]
    fn civil_from_days_known_dates() {
        // Day 0 is 1970-01-01; spot checks across epochs and leap years.
        assert_eq!(civil_from_days(0), (1970, 1, 1));
        assert_eq!(civil_from_days(1), (1970, 1, 2));
        assert_eq!(civil_from_days(31), (1970, 2, 1));
        assert_eq!(civil_from_days(59), (1970, 3, 1));
        assert_eq!(civil_from_days(365), (1971, 1, 1));
        assert_eq!(civil_from_days(789), (1972, 2, 29)); // leap day
        assert_eq!(civil_from_days(790), (1972, 3, 1));
        assert_eq!(civil_from_days(20748), (2026, 10, 22));
        assert_eq!(civil_from_days(10957), (2000, 1, 1));
    }

    #[test]
    fn iso8601_shape() {
        let t = iso8601_now();
        assert_eq!(t.len(), 24, "{t}");
        for i in [4, 7] {
            assert_eq!(t.get(i..i + 1), Some("-"), "{t}");
        }
        assert_eq!(t.get(10..11), Some("T"), "{t}");
        for i in [13, 16] {
            assert_eq!(t.get(i..i + 1), Some(":"), "{t}");
        }
        assert!(t.ends_with('Z'), "{t}");
        // Only shape-check the live timestamp; exact dates live in the
        // civil_from_days test above.
        assert!(t.starts_with("20"), "{t}");
    }

    #[test]
    fn log_view_and_record_request() {
        let log: RequestLog =
            Arc::new(Mutex::new(VecDeque::new()));
        let req = |path: &str, accept: &str| Request {
            method: "GET".into(),
            path: path.into(),
            body: String::new(),
            accept: accept.into(),
        };

        let resp_bytes = response::render(
            "200 OK",
            Some("application/json"),
            "{'ok': 1}\n",
        )
        .into_bytes();
        record_request(&log, &req("/api/get-tweet", ""), &resp_bytes);
        record_request(&log, &req("/nope.js", ""), b"HTTP/1.1 404 Not Found\r\n\r\n");

        let plain = log_view(&req("/log", ""), &log);
        let body: String = plain.split("\r\n\r\n").nth(1).unwrap().into();
        assert!(body.contains("/api/get-tweet  200"), "{body}");
        assert!(body.contains("/nope.js  404"), "{body}");
        assert!(body.contains('T'), "{body}");

        let html = log_view(&req("/log", "text/html"), &log);
        let body: String = html.split("\r\n\r\n").nth(1).unwrap().into();
        assert!(body.starts_with("<pre>"), "{body}");

        // Cap: flood and see it trimmed
        for _ in 0..(LOG_CAP + 25) {
            record_request(&log, &req("/flood", ""), &resp_bytes);
        }
        let log_len = log.lock().unwrap().len();
        assert_eq!(log_len, LOG_CAP);
        let plain = log_view(&req("/log", ""), &log);
        let body: String = plain.split("\r\n\r\n").nth(1).unwrap().into();
        assert!(!body.contains("/api/get-tweet"), "{body}");
        assert!(body.contains("/flood"), "{body}");
    }

    #[test]
    fn static_serving_serves_index() {
        let req = Request {
            method: "GET".into(),
            path: "/".into(),
            body: String::new(),
            accept: String::new(),
        };
        let resp = String::from_utf8_lossy(&serve_static(&req, Path::new(FRONTEND_DIR))).into_owned();
        assert!(resp.starts_with("HTTP/1.1 200 OK"), "{resp}");
        assert!(resp.contains("text/html"), "{resp}");
        let body: String = resp.split("\r\n\r\n").nth(1).unwrap().into();
        assert!(body.contains("<!DOCTYPE html>") || body.contains("<html"), "{body}");
    }

    #[test]
    fn static_serving_blocks_traversal() {
        let req = Request {
            method: "GET".into(),
            path: "/../Cargo.toml".into(),
            body: String::new(),
            accept: String::new(),
        };
        let resp = String::from_utf8_lossy(&serve_static(&req, Path::new(FRONTEND_DIR))).into_owned();
        assert!(resp.starts_with("HTTP/1.1 404"), "{resp}");
    }
}
