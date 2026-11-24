// Realistic performance benchmark: drives the RELEASE server binary over real TCP.
// Plain cargo test prints a skip and passes; FT_BENCH=run executes tier B once.
// The test never invokes cargo (the outer cargo test holds the target-dir lock):
// without a prebuilt release binary it prints the build instruction and returns.

/// Bench server port: the smoke ports 8011-8027 stay clear of this.
const PORT_BENCH: u16 = 8091;

/// Fresh sqlite file for the tier: the world starts empty in every scenario.
const DB_BENCH: &str = "/tmp/ft-bench-b.sqlite";

/// Release binary candidate: the crate-root target, built by the coordinator.
const BIN_RELEASE: &str = "target/release/formal-twitter";

/// Server lifetime under the timeout wrapper: a backstop, the harness pkills sooner.
const SECS_BENCH: u32 = 600;

/// Octet cap on one response slurp: big timelines get truncated, good enough here.
const READ_CAP: usize = 4096;

/// True when the release binary is already on disk: the gate for running tiers.
fn path_exists(p: String) -> bool {
	std::fs::exists(p).unwrap_or_default()
}

/// Launches the release binary under the timeout wrapper (same spelling as smoke.rs).
fn spawn_server(port: u16, db: &str, secs: u32) {
	_ = std::process::Command::new("timeout")
		.env("FT_DB", db)
		.env("ROCKET_PORT", port.to_string())
		.arg(secs.to_string())
		.arg(BIN_RELEASE)
		.spawn();
}

/// Deletes a DB file from an earlier run so the server starts from an empty world.
fn fresh_db(db: &str) {
	_ = std::fs::remove_file(db);
}

/// Waits until something answers on the port; false when the server never starts.
fn wait_ready(port: u16) -> bool {
	let mut tries: usize = 0;
	while tries < 50 {
		if std::net::TcpStream::connect(("127.0.0.1", port)).is_ok() {
			return true;
		}
		std::thread::sleep(std::time::Duration::from_millis(100));
		tries += 1;
	}
	false
}

/// Stops the scenario server: matches only the release path, never debug servers.
fn kill_server() {
	_ = std::process::Command::new("pkill")
		.arg("-f")
		.arg("release/formal-twitter")
		.spawn();
}
/// True once the CRLF CRLF that closes the response headers has been read.
fn headers_done(xs: &[u8]) -> bool {
	header_end(xs) != 0
}

/// The octet count of the header block, blank line included; zero while unseen.
fn header_end(xs: &[u8]) -> usize {
	let mut i: usize = 0;
	while i + 3 < xs.len() {
		if xs[i] == 13 && xs[i + 1] == 10 && xs[i + 2] == 13 && xs[i + 3] == 10 {
			return i + 4;
		}
		i += 1;
	}
	0
}

/// The number whose digits start at i and the index just after them; (0, i) when absent.
fn digits_at(bs: &[u8], i: usize) -> (u64, usize) {
	let mut n: u64 = 0;
	let mut j: usize = i;
	while j < bs.len() && bs[j] >= 48 && bs[j] <= 57 {
		n = n * 10 + (bs[j] - 48) as u64;
		j += 1;
	}
	(n, j)
}

/// The first number in the text at or after a byte index; zero when absent.
fn number_after(text: &str, start: usize) -> u64 {
	let bs = text.as_bytes();
	let mut i: usize = start;
	while i < bs.len() {
		let scanned: (u64, usize) = digits_at(bs, i);
		if scanned.1 != i {
			return scanned.0;
		}
		i += 1;
	}
	0
}

/// The first number that follows a label in the text; zero when the label is absent.
fn label_number(text: &str, label: &str) -> u64 {
	match text.find(label) {
		None => 0,
		Some(p) => number_after(text, p + label.len()),
	}
}

/// The Content-Length the server declared; zero while the header is unseen.
fn content_length(xs: &[u8]) -> usize {
	match String::from_utf8(xs.to_vec()) {
		Err(_) => 0,
		Ok(text) => label_number(&text, "content-length") as usize,
	}
}
/// The octets of one POST request: the frontend headers and the CRLF body.
fn request_bytes(path: String, body: String) -> Vec<u8> {
	let mut out = "POST ".to_owned();
	out += &path;
	out += " HTTP/1.1\r\nHost: 127.0.0.1\r\nAccept: application/json\r\n";
	out += "Content-Type: text/plain; charset=utf-8\r\n";
	out += "Content-Length: ";
	out += &body.len().to_string();
	out += "\r\n\r\n";
	out += &body;
	out.as_bytes().to_vec()
}

/// Sends one request's octets and returns every octet the server answered with.
fn send_and_read(port: u16, wire: Vec<u8>) -> String {
	let mut sock = match std::net::TcpStream::connect(("127.0.0.1", port)) {
		Err(_) => panic!("cannot reach the server"),
		Ok(s) => s,
	};
	_ = std::io::Write::write_all(&mut sock, &wire);
	let mut got: Vec<u8> = vec![];
	let mut one: [u8; 1] = [0];
	while !headers_done(&got) && got.len() < READ_CAP {
		_ = std::io::Read::read_exact(&mut sock, &mut one);
		got.push(one[0]);
	}
	let want: usize = header_end(&got) + content_length(&got);
	while got.len() < want {
		_ = std::io::Read::read_exact(&mut sock, &mut one);
		got.push(one[0]);
	}
	match String::from_utf8(got) {
		Err(_) => "".to_string(),
		Ok(text) => text,
	}
}

/// Sends one POST request and returns every octet the server answered with.
fn req(port: u16, path: String, body: String) -> String {
	send_and_read(port, request_bytes(path, body))
}

/// Advances a xorshift64 RNG: the new state doubles as the roll.
fn next_rand(state: u64) -> u64 {
	let mut x: u64 = state;
	x ^= x << 13;
	x ^= x >> 7;
	x ^= x << 17;
	x
}

/// Whole milliseconds elapsed since the stamp; zero when the clock went backwards.
fn ms_since(start: std::time::SystemTime) -> usize {
	match start.elapsed() {
		Err(_) => 0,
		Ok(d) => d.as_millis() as usize,
	}
}
/// Tier B lite: 20 accounts, 100 publishes, then the 300-request timed mix.
const B_ACCOUNTS: usize = 20;
const B_POSTS: usize = 100;
const REQ_TOTAL: usize = 300;

/// Seeds the fresh server: signup+login per account, round-robin publishes.
/// Returns account names, their live tokens, and the created tweet ids.
fn seed(port: u16, accounts: usize, posts: usize) -> (Vec<String>, Vec<u64>, Vec<u64>) {
	let mut names: Vec<String> = vec![];
	let mut tokens: Vec<u64> = vec![];
	let mut tweets: Vec<u64> = vec![];
	let mut i: usize = 0;
	while i < accounts {
		let name: String = "u".to_owned() + &i.to_string();
		_ = req(
			port,
			"/api/signup".to_string(),
			name.clone() + "\r\n" + "pw",
		);
		let logged: String = req(port, "/api/login".to_string(), name.clone() + "\r\n" + "pw");
		names.push(name);
		tokens.push(label_number(&logged, "session_token"));
		i += 1;
	}
	let mut p: usize = 0;
	while p < posts {
		let who: usize = p % accounts;
		let posted: String = req(
			port,
			"/api/post-tweet".to_string(),
			tokens[who].to_string() + "\r\ntext" + &p.to_string(),
		);
		let created: u64 = label_number(&posted, "tweet_id");
		if created != 0 {
			tweets.push(created);
		}
		p += 1;
	}
	(names, tokens, tweets)
}
/// The timed mix classes: name, wire path, weight band width (the bench-report mix).
const CLASS_NAMES: [&str; 10] = [
	"post-tweet",
	"global-timeline",
	"login",
	"like-tweet",
	"post-reply",
	"private-timeline",
	"logout",
	"follow-user",
	"signup",
	"get-tweet",
];
const CLASS_PATHS: [&str; 10] = [
	"/api/post-tweet",
	"/api/global-timeline",
	"/api/login",
	"/api/like-tweet",
	"/api/post-reply",
	"/api/private-timeline",
	"/api/logout",
	"/api/follow-user",
	"/api/signup",
	"/api/get-tweet",
];
const CLASS_WEIGHTS: [usize; 10] = [25, 20, 15, 15, 10, 15, 5, 5, 5, 5];
const WEIGHT_SUM: usize = 120;

/// Picks the mix class whose weight band covers the roll in [0, WEIGHT_SUM).
fn pick_class(roll: usize) -> usize {
	let mut acc: usize = 0;
	let mut c: usize = 0;
	while c < CLASS_WEIGHTS.len() {
		acc += CLASS_WEIGHTS[c];
		if roll < acc {
			return c;
		}
		c += 1;
	}
	CLASS_WEIGHTS.len() - 1
}
/// The timed loop: weighted class picks, per-request wall time, per-class tallies.
fn run_mix(
	port: u16,
	total: usize,
	names: Vec<String>,
	tokens: Vec<u64>,
	tweets: Vec<u64>,
) -> ([usize; 10], [usize; 10], [Vec<usize>; 10]) {
	let mut toks: Vec<u64> = tokens;
	let mut alive: Vec<bool> = vec![];
	let mut j: usize = 0;
	while j < toks.len() {
		alive.push(true);
		j += 1;
	}
	let mut counts: [usize; 10] = [0; 10];
	let mut ms: [usize; 10] = [0; 10];
	let mut samples: [Vec<usize>; 10] = [
		vec![],
		vec![],
		vec![],
		vec![],
		vec![],
		vec![],
		vec![],
		vec![],
		vec![],
		vec![],
	];
	let mut rng: u64 = 0x243F6A8885A308D3;
	let mut extra: usize = 0;
	let mut n: usize = 0;
	while n < total {
		rng = next_rand(rng);
		let c: usize = pick_class((rng % WEIGHT_SUM as u64) as usize);
		rng = next_rand(rng);
		let who: usize = (rng % names.len() as u64) as usize;
		let tw: usize = if !tweets.is_empty() {
			(rng % tweets.len() as u64) as usize
		} else {
			0
		};
		let tw_id: u64 = if !tweets.is_empty() { tweets[tw] } else { 1 };
		// a logged-out account re-logs in first: the login is timed in the login class
		if (c == 0 || c == 3 || c == 4 || c == 5 || c == 6 || c == 7) && !alive[who] {
			let back: std::time::SystemTime = std::time::SystemTime::now();
			let revived: String = req(
				port,
				CLASS_PATHS[2].to_string(),
				names[who].clone() + "\r\npw",
			);
			counts[2] += 1;
			ms[2] += ms_since(back);
			samples[2].push(ms_since(back));
			alive[who] = true;
			toks[who] = label_number(&revived, "session_token");
		}
		let body: String = match c {
			0 => toks[who].to_string() + "\r\ntext" + &n.to_string(),
			1 => "10".to_string(),
			2 => names[who].clone() + "\r\npw",
			3 => toks[who].to_string() + "\r\n" + &tw_id.to_string(),
			4 => toks[who].to_string() + "\r\nreply" + &n.to_string() + "\r\n" + &tw_id.to_string(),
			5 => toks[who].to_string() + "\r\n10",
			6 => toks[who].to_string(),
			7 => toks[who].to_string() + "\r\n" + &names[(who + 1) % names.len()],
			8 => "bx".to_owned() + &extra.to_string() + "\r\npw",
			_ => tw_id.to_string(),
		};
		let stamp: std::time::SystemTime = std::time::SystemTime::now();
		let answered: String = req(port, CLASS_PATHS[c].to_string(), body);
		let took: usize = ms_since(stamp);
		counts[c] += 1;
		ms[c] += took;
		samples[c].push(took);
		if c == 2 {
			alive[who] = true;
			toks[who] = label_number(&answered, "session_token");
		}
		if c == 6 {
			alive[who] = false;
		}
		if c == 8 {
			extra += 1;
		}
		n += 1;
	}
	(counts, ms, samples)
}
/// Prints one tier report: a line per class with median, p99, and req/s rates.
fn report(
	port: u16,
	seed_ms: usize,
	mix_ms: usize,
	counts: [usize; 10],
	ms: [usize; 10],
	samples: [Vec<usize>; 10],
) {
	let mut c: usize = 0;
	while c < 10 {
		let mut v: Vec<usize> = samples[c].clone();
		v.sort();
		let n: usize = v.len();
		let med: usize = if n > 0 { v[n / 2] } else { 0 };
		let p99i: usize = if n > 0 { (n * 99) / 100 } else { 0 };
		let p99: usize = if n > 0 {
			if p99i >= n { v[n - 1] } else { v[p99i] }
		} else {
			0
		};
		let rate: usize = if ms[c] > 0 {
			counts[c] * 1000 / ms[c]
		} else {
			0
		};
		let line: String = CLASS_NAMES[c].to_string()
			+ ": " + &counts[c].to_string()
			+ " reqs, med "
			+ &med.to_string()
			+ " ms, p99 "
			+ &p99.to_string()
			+ " ms, " + &rate.to_string()
			+ " req/s";
		println!("{}", line);
		c += 1;
	}
	let total_reqs: usize = counts[0]
		+ counts[1]
		+ counts[2]
		+ counts[3]
		+ counts[4]
		+ counts[5]
		+ counts[6]
		+ counts[7]
		+ counts[8]
		+ counts[9];
	let rate_all: usize = if mix_ms > 0 {
		total_reqs * 1000 / mix_ms
	} else {
		0
	};
	let tail: String = "tier port ".to_owned()
		+ &port.to_string()
		+ ": seed "
		+ &seed_ms.to_string()
		+ " ms, mix "
		+ &total_reqs.to_string()
		+ " reqs in "
		+ &mix_ms.to_string()
		+ " ms = "
		+ &rate_all.to_string()
		+ " req/s";
	println!("{}", tail);
}
/// Runs the lite tier B scenario end to end; true when the numbers were measured.
fn run_tier() -> bool {
	spawn_server(PORT_BENCH, DB_BENCH, SECS_BENCH);
	if !wait_ready(PORT_BENCH) {
		kill_server();
		return false;
	}
	let seed_stamp: std::time::SystemTime = std::time::SystemTime::now();
	let seeded: (Vec<String>, Vec<u64>, Vec<u64>) = seed(PORT_BENCH, B_ACCOUNTS, B_POSTS);
	let seed_ms: usize = ms_since(seed_stamp);
	let mix_stamp: std::time::SystemTime = std::time::SystemTime::now();
	let tallied: ([usize; 10], [usize; 10], [Vec<usize>; 10]) =
		run_mix(PORT_BENCH, REQ_TOTAL, seeded.0, seeded.1, seeded.2);
	let mix_ms: usize = ms_since(mix_stamp);
	kill_server();
	fresh_db(DB_BENCH);
	report(PORT_BENCH, seed_ms, mix_ms, tallied.0, tallied.1, tallied.2);
	true
}

/// The one bench test: skip unless FT_BENCH is exactly run; never calls cargo itself.
#[test]
fn bench_run_when_set() {
	let mode: String = match std::env::var("FT_BENCH") {
		Err(_) => "".to_string(),
		Ok(v) => v,
	};
	if mode != "run" {
		println!("skipping bench: run with FT_BENCH=run after cargo build --release");
		return;
	}
	if !path_exists(BIN_RELEASE.to_string()) {
		println!(
			"bench skipped: no target/release/formal-twitter, build it with cargo build --release"
		);
		return;
	}
	_ = run_tier();
}
