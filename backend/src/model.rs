//! Pure model mirroring spec/Twitter.agda: World, Command, Result, Step.

use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq)]
pub enum Visibility {
	Everyone,
	FollowersOnly,
}

/// PostStatus; Other is the spec's live.
#[derive(Clone, Debug, PartialEq)]
pub enum PostStatus {
	Other,
	Deleted,
}

#[derive(Clone, Debug, PartialEq)]
pub enum SessionStatus {
	Unused,
	Active(String),
	Revoked,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Account {
	pub password: String,
	/// Account.default-visibility
	pub default_visibility: Visibility,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Post {
	pub author: String,
	pub text: String,
	pub visibility: Visibility,
	/// Post.status
	pub status: PostStatus,
	/// Post.likes: unique user names
	pub likes: Vec<String>,
	/// Post.replies: unique child pids
	pub replies: Vec<u64>,
	/// Post.parent
	pub parent: Option<u64>,
}

/// World: every map is stored as an association list; absence means nothing, unused or false.
#[derive(Clone, Debug, PartialEq)]
pub struct World {
	/// World.account-at
	pub accounts: Vec<(String, Account)>,
	/// World.session-at
	pub sessions: Vec<(u64, SessionStatus)>,
	/// World.post-at
	pub posts: Vec<(u64, Post)>,
	/// World.follows: exactly the true (follower, followee) pairs
	pub follows: Vec<(String, String)>,
	/// World.newest-first: the head is the newest post
	pub newest_first: Vec<u64>,
	/// World.used-post-ids
	pub used_post_ids: Vec<u64>,
	/// World.used-session-ids
	pub used_session_ids: Vec<u64>,
}

/// O(1) side-index over the World maps: first-occurrence positions per key, mirroring the Vec scans.
#[derive(Clone, Debug, PartialEq)]
pub struct WorldIndex {
	/// first position of each username in World.accounts
	pub accounts_ix: HashMap<String, usize>,
	/// first position of each session id in World.sessions
	pub sessions_ix: HashMap<u64, usize>,
	/// first position of each post id in World.posts
	pub posts_ix: HashMap<u64, usize>,
	/// the true (follower, followee) pairs of World.follows
	pub follows_ix: HashSet<(String, String)>,
}

/// Build the side-index for a World; first occurrence of each key wins, matching the Vec scans.
pub fn build_index(w: &World) -> WorldIndex {
	// keep the first position per key, like the scan's first match
	let mut accounts_ix: HashMap<String, usize> = HashMap::new();
	for (i, (name, _)) in w.accounts.iter().enumerate() {
		if !accounts_ix.contains_key(name) {
			accounts_ix.insert(name.clone(), i);
		}
	}
	let mut sessions_ix: HashMap<u64, usize> = HashMap::new();
	for (i, (sid, _)) in w.sessions.iter().enumerate() {
		if !sessions_ix.contains_key(sid) {
			sessions_ix.insert(*sid, i);
		}
	}
	let mut posts_ix: HashMap<u64, usize> = HashMap::new();
	for (i, (pid, _)) in w.posts.iter().enumerate() {
		if !posts_ix.contains_key(pid) {
			posts_ix.insert(*pid, i);
		}
	}
	// follows pairs are deduplicated by the set
	let follows_ix: HashSet<(String, String)> = w.follows.iter().cloned().collect();
	WorldIndex {
		accounts_ix,
		sessions_ix,
		posts_ix,
		follows_ix,
	}
}

/// Command mirrors the Command data type of spec/Twitter.agda.
#[derive(Clone, Debug, PartialEq)]
pub enum Command {
	Publish(u64, String, Option<u64>),
	Delete(u64, u64),
	ReadPost(Option<u64>, u64),
	ReadPersonalTimeline(u64, u64),
	ReadGlobalTimeline(Option<u64>, u64),
	Authenticate(String, String),
	RevokeToken(u64),
	Register(String, String),
	Follow(u64, String),
	Unfollow(u64, String),
	Like(u64, u64),
	Unlike(u64, u64),
	TimePasses,
}

/// Result mirrors the Result data type of spec/Twitter.agda.
#[derive(Clone, Debug, PartialEq)]
pub enum Result {
	Success,
	Denied,
	Expired,
	LoginFailed,
	SignupFailed,
	ReturnedTimeline(Vec<u64>),
	IssuedSession(u64),
	CreatedPost(u64),
	ReturnedPost(String, String, u64, Vec<u64>),
}
/// Delta: one Command's effect as a payload only: step_d builds it directly in the branch, patch_world applies it to an owned World.
#[derive(Clone, Debug, PartialEq)]
pub enum Delta {
	None_,
	Publish(u64, String, String, Visibility, Option<u64>),
	Delete(u64),
	Authenticate(u64, String),
	RevokeToken(u64),
	Register(String, Account),
	Follow(String, String),
	Unfollow(String, String),
	Like(u64, String),
	Unlike(u64, String),
	TimePasses(Vec<u64>),
}

/// Spec helper: list membership (Agda's ∈).
pub fn member<T: Eq>(xs: &[T], x: T) -> bool {
	// membership via std's contains on the borrowed slice: same first-hit semantics
	// (the bound widens Eq, which every use-site type satisfies)
	(xs).contains(&x)
}

/// Spec helper: no-duplicates on a list.
pub fn unique<T: PartialEq>(xs: &[T]) -> bool {
	// quadratic; worlds are small
	for (i, x) in xs.iter().enumerate() {
		for y in &xs[(i + 1)..] {
			if *x == *y {
				return false;
			}
		}
	}
	// distinct
	true
}

/// List length as u64 without lossy casts.
pub fn len_u64<T>(xs: &[T]) -> u64 {
	// the Vec length widened; same value for every in-range length
	xs.len() as u64
}

/// World.account-at; absence means nothing.
pub fn account_at(w: &World, user: &str) -> Option<Account> {
	for (name, acc) in w.accounts.iter() {
		if *name == user {
			return Some(acc.clone());
		}
	}
	None
}

/// Borrowing World.account-at for read-only callers; no Account clone.
pub fn account_at_ref<'a>(w: &'a World, user: &str) -> Option<&'a Account> {
	for (name, acc) in w.accounts.iter() {
		if *name == user {
			return Some(acc);
		}
	}
	None
}

/// Index-backed World.account-at; same first-occurrence result as the scan.
pub fn account_at_ix(w: &World, ix: &WorldIndex, user: &str) -> Option<Account> {
	// one hash lookup, then the same Vec cell the scan would hit
	ix.accounts_ix.get(user).map(|i| w.accounts[*i].1.clone())
}

/// World.session-at; absence means Unused.
pub fn session_at(w: &World, sid: u64) -> SessionStatus {
	for (s, st) in w.sessions.iter() {
		if *s == sid {
			return st.clone();
		}
	}
	SessionStatus::Unused
}

/// Index-backed World.session-at; absence means Unused.
pub fn session_at_ix(w: &World, ix: &WorldIndex, sid: u64) -> SessionStatus {
	// same cell as the scan: first position for sid
	match ix.sessions_ix.get(&sid) {
		None => SessionStatus::Unused,
		Some(i) => w.sessions[*i].1.clone(),
	}
}

/// World.post-at; absence means nothing.
pub fn post_at(w: &World, pid: u64) -> Option<Post> {
	for (p, post) in w.posts.iter() {
		if *p == pid {
			return Some(post.clone());
		}
	}
	None
}

/// Borrowing World.post-at for read-only callers; no Post clone.
pub fn post_at_ref(w: &World, pid: u64) -> Option<&Post> {
	for (p, post) in w.posts.iter() {
		if *p == pid {
			return Some(post);
		}
	}
	None
}

/// Index-backed World.post-at; absence means nothing.
pub fn post_at_ix(w: &World, ix: &WorldIndex, pid: u64) -> Option<Post> {
	// one hash lookup, then the same Vec cell the scan would hit
	ix.posts_ix.get(&pid).map(|i| w.posts[*i].1.clone())
}

/// World.follows; absence means false.
pub fn follows(w: &World, follower: &str, followee: &str) -> bool {
	for (f, g) in w.follows.iter() {
		if *f == follower && *g == followee {
			return true;
		}
	}
	false
}

/// Index-backed World.follows; absence in the set means false.
pub fn follows_ix(_w: &World, ix: &WorldIndex, follower: &str, followee: &str) -> bool {
	// the pair is either present as a true edge or absent
	ix.follows_ix
		.contains(&(follower.to_string(), followee.to_string()))
}

/// World.used-post-ids membership.
pub fn used_pid(w: &World, pid: u64) -> bool {
	member(&w.used_post_ids, pid)
}

/// World.used-session-ids membership.
pub fn used_sid(w: &World, sid: u64) -> bool {
	member(&w.used_session_ids, sid)
}

/// The username of an active session, if any.
pub fn active_user(w: &World, sid: u64) -> Option<String> {
	match session_at(w, sid) {
		SessionStatus::Active(user) => Some(user.clone()),
		_ => None,
	}
}

/// Borrowing the username of an active session for read-only callers; no String clone.
pub fn active_user_ref(w: &World, sid: u64) -> Option<&String> {
	for (s, st) in w.sessions.iter() {
		if *s == sid {
			match st {
				SessionStatus::Active(user) => return Some(user),
				_ => return None,
			}
		}
	}
	None
}

/// Index-backed active session username; absence means no session.
pub fn active_user_ix(w: &World, ix: &WorldIndex, sid: u64) -> Option<String> {
	// status from the indexed cell; only Active yields a name
	match session_at_ix(w, ix, sid) {
		SessionStatus::Active(user) => Some(user.clone()),
		_ => None,
	}
}

/// Spec can-have-valid-session: sid is active for a user with an account.
pub fn valid_session(w: &World, sid: u64) -> bool {
	match active_user(w, sid) {
		None => false,
		Some(user) => account_at(w, &user).is_some(),
	}
}

/// Index-backed can-have-valid-session.
pub fn valid_session_ix(w: &World, ix: &WorldIndex, sid: u64) -> bool {
	// active username must exist and own an account
	match active_user_ix(w, ix, sid) {
		None => false,
		Some(user) => account_at_ix(w, ix, &user).is_some(),
	}
}

/// Spec extract-sid: the session a command acts through.
pub fn extract_sid(cmd: Command) -> Option<u64> {
	match cmd {
		Command::Publish(sid, _, _) => Some(sid),
		Command::Delete(sid, _) => Some(sid),
		Command::ReadPost(msid, _) => msid,
		Command::ReadPersonalTimeline(sid, _) => Some(sid),
		Command::ReadGlobalTimeline(msid, _) => msid,
		Command::Authenticate(_, _) => None,
		Command::RevokeToken(sid) => Some(sid),
		Command::Register(_, _) => None,
		Command::Follow(sid, _) => Some(sid),
		Command::Unfollow(sid, _) => Some(sid),
		Command::Like(sid, _) => Some(sid),
		Command::Unlike(sid, _) => Some(sid),
		Command::TimePasses => None,
	}
}

/// Whether a command passes the failed-access check.
pub fn access_ok(w: &World, cmd: Command) -> bool {
	match extract_sid(cmd.clone()) {
		None => true,
		Some(sid) => valid_session(w, sid),
	}
}

/// Index-backed failed-access check.
pub fn access_ok_ix(w: &World, ix: &WorldIndex, cmd: Command) -> bool {
	// same command extraction; session validity answered from the index
	match extract_sid(cmd.clone()) {
		None => true,
		Some(sid) => valid_session_ix(w, ix, sid),
	}
}

/// Spec can-read-post w sid pid.
pub fn can_read(w: &World, sid: u64, pid: u64) -> bool {
	match active_user_ref(w, sid) {
		None => false,
		Some(user) => {
			account_at_ref(w, user).is_some()
				&& match post_at_ref(w, pid) {
					None => false,
					Some(post) => {
						post.status == PostStatus::Other
							&& (post.visibility == Visibility::Everyone
								|| (post.visibility == Visibility::FollowersOnly
									&& follows(w, user, &post.author)))
					}
				}
		}
	}
}

/// Index-backed can-read-post; borrows the cells, no SessionStatus/Account/Post clone.
pub fn can_read_ix(w: &World, ix: &WorldIndex, sid: u64, pid: u64) -> bool {
	// same chain: active name, account exists, post live and visible; all answered by borrowing
	match ix.sessions_ix.get(&sid) {
		None => false,
		Some(i) => match &w.sessions[*i].1 {
			SessionStatus::Active(user) => {
				ix.accounts_ix.contains_key(user)
					&& match ix.posts_ix.get(&pid) {
						None => false,
						Some(j) => {
							let post = &w.posts[*j].1;
							post.status == PostStatus::Other
								&& (post.visibility == Visibility::Everyone
									|| (post.visibility == Visibility::FollowersOnly
										&& follows_ix(w, ix, user, &post.author)))
						}
					}
			}
			_ => false,
		},
	}
}

/// Spec is-post-public: exists with Everyone visibility and live status.
pub fn is_post_public(w: &World, pid: u64) -> bool {
	match post_at_ref(w, pid) {
		None => false,
		Some(post) => post.visibility == Visibility::Everyone && post.status == PostStatus::Other,
	}
}

/// Index-backed is-post-public; borrows the post cell, no Post clone.
pub fn is_post_public_ix(w: &World, ix: &WorldIndex, pid: u64) -> bool {
	// same predicate: Everyone visibility and live status, answered from the indexed cell
	match ix.posts_ix.get(&pid) {
		None => false,
		Some(i) => {
			let post = &w.posts[*i].1;
			post.visibility == Visibility::Everyone && post.status == PostStatus::Other
		}
	}
}

/// Spec follows-post-author: user follows the author of pid.
/// Test-only: referenced by #[cfg(test)] props/baselines, not by the runtime wire path.
pub fn follows_author(w: &World, user: &str, pid: u64) -> bool {
	match post_at_ref(w, pid) {
		None => false,
		Some(post) => follows(w, user, &post.author),
	}
}

/// Data.List.take on Vec.
/// Test-only: used by #[cfg(test)] baselines/QC, not by the runtime wire path.
pub fn take_n(xs: Vec<u64>, n: u64) -> Vec<u64> {
	// take stops at the iterator end, so n beyond the length yields all, as before
	// (usize is 64-bit here, so the n cast is exact)
	(xs.iter()).take(n as usize).copied().collect()
}

/// Borrowing helpers for the index-backed hot paths: O(1) position lookup, borrowed cell.
fn active_user_bx<'w>(w: &'w World, ix: &WorldIndex, sid: u64) -> Option<&'w String> {
	// status borrowed from the indexed cell; only Active yields a name
	match ix.sessions_ix.get(&sid) {
		None => None,
		Some(i) => match &w.sessions[*i].1 {
			SessionStatus::Active(user) => Some(user),
			_ => None,
		},
	}
}

/// Borrowing World.account-at via the side-index; no Account clone.
fn account_at_bx<'w>(w: &'w World, ix: &WorldIndex, user: &str) -> Option<&'w Account> {
	// one hash lookup, then borrow the same Vec cell the scan would hit
	ix.accounts_ix.get(user).map(|i| &w.accounts[*i].1)
}

/// Borrowing World.post-at via the side-index; no Post clone.
fn post_at_bx<'w>(w: &'w World, ix: &WorldIndex, pid: u64) -> Option<&'w Post> {
	// one hash lookup, then borrow the same Vec cell the scan would hit
	ix.posts_ix.get(&pid).map(|i| &w.posts[*i].1)
}

/// Test-only pure-Vec reference for the _ix equivalence props.
/// get-personal-timeline: newest-first, keep readable posts by followed authors.
pub fn personal_timeline_ref(w: &World, sid: u64, n: u64) -> Vec<u64> {
	// Hoist: username and account presence are loop-invariant for the newest_first scan;
	// their absence makes can-read false for every pid, i.e. the old code yielded [].
	match active_user_ref(w, sid) {
		None => vec![],
		Some(user) => {
			if account_at_ref(w, user).is_none() {
				return vec![];
			}
			if n == 0 {
				return vec![];
			}
			let mut acc = vec![];
			for pid in &w.newest_first {
				// Early-stop: collect at most n matches, then stop; the prefix equals take_n of
				// the old full-filter output. Fused test shares ONE borrowing post lookup:
				// can-read && follows-author == live, author followed, visibility in the enum.
				let readable: bool = match post_at_ref(w, *pid) {
					None => false,
					Some(post) => {
						post.status == PostStatus::Other
							&& follows(w, user, &post.author)
							&& (post.visibility == Visibility::Everyone
								|| post.visibility == Visibility::FollowersOnly)
					}
				};
				if readable {
					acc.push(*pid);
					if acc.len() as u64 >= n {
						break;
					}
				}
			}
			acc
		}
	}
}

/// get-personal-timeline through the side-index; hot path borrows per candidate.
pub fn personal_timeline_ix(w: &World, ix: &WorldIndex, sid: u64, n: u64) -> Vec<u64> {
	// same hoisting/early-stop as the reference; every probe goes through the index
	match active_user_bx(w, ix, sid) {
		None => vec![],
		Some(user) => {
			if account_at_bx(w, ix, user).is_none() {
				return vec![];
			}
			if n == 0 {
				return vec![];
			}
			let mut acc = vec![];
			for pid in &w.newest_first {
				// same fused borrow: one indexed post lookup per candidate
				let readable: bool = match post_at_bx(w, ix, *pid) {
					None => false,
					Some(post) => {
						post.status == PostStatus::Other
							&& follows_ix(w, ix, user, &post.author)
							&& (post.visibility == Visibility::Everyone
								|| post.visibility == Visibility::FollowersOnly)
					}
				};
				if readable {
					acc.push(*pid);
					if acc.len() as u64 >= n {
						break;
					}
				}
			}
			acc
		}
	}
}

/// get-personal-timeline: build the side-index once, then answer through it.
pub fn personal_timeline(w: &World, sid: u64, n: u64) -> Vec<u64> {
	// fresh side-index; every lookup then goes through the map instead of a scan
	let ix: WorldIndex = build_index(w);
	personal_timeline_ix(w, &ix, sid, n)
}

/// Test-only pure-Vec reference for the _ix equivalence props.
/// get-private-global: newest-first readable posts.
pub fn global_timeline_ref(w: &World, sid: u64, n: u64) -> Vec<u64> {
	// Same hoisting/early-stop shape as personal_timeline: the session username and account
	// presence are loop-invariant; absence made can-read false for every pid (old result []).
	match active_user_ref(w, sid) {
		None => vec![],
		Some(user) => {
			if account_at_ref(w, user).is_none() {
				return vec![];
			}
			if n == 0 {
				return vec![];
			}
			let mut acc = vec![];
			for pid in &w.newest_first {
				// can-read for the hoisted user, one borrowing post lookup per candidate.
				let readable: bool = match post_at_ref(w, *pid) {
					None => false,
					Some(post) => {
						post.status == PostStatus::Other
							&& (post.visibility == Visibility::Everyone
								|| (post.visibility == Visibility::FollowersOnly
									&& follows(w, user, &post.author)))
					}
				};
				if readable {
					acc.push(*pid);
					if acc.len() as u64 >= n {
						break;
					}
				}
			}
			acc
		}
	}
}

/// get-private-global through the side-index; hot path borrows per candidate.
pub fn global_timeline_ix(w: &World, ix: &WorldIndex, sid: u64, n: u64) -> Vec<u64> {
	// same hoisting/early-stop as the reference; every probe goes through the index
	match active_user_bx(w, ix, sid) {
		None => vec![],
		Some(user) => {
			if account_at_bx(w, ix, user).is_none() {
				return vec![];
			}
			if n == 0 {
				return vec![];
			}
			let mut acc = vec![];
			for pid in &w.newest_first {
				// can-read for the hoisted user via one indexed borrow per candidate
				let readable: bool = match post_at_bx(w, ix, *pid) {
					None => false,
					Some(post) => {
						post.status == PostStatus::Other
							&& (post.visibility == Visibility::Everyone
								|| (post.visibility == Visibility::FollowersOnly
									&& follows_ix(w, ix, user, &post.author)))
					}
				};
				if readable {
					acc.push(*pid);
					if acc.len() as u64 >= n {
						break;
					}
				}
			}
			acc
		}
	}
}

/// get-private-global: build the side-index once, then answer through it.
pub fn global_timeline(w: &World, sid: u64, n: u64) -> Vec<u64> {
	// fresh side-index; every lookup then goes through the map instead of a scan
	let ix: WorldIndex = build_index(w);
	global_timeline_ix(w, &ix, sid, n)
}

/// Test-only pure-Vec reference for the _ix equivalence props.
/// get-public-global: newest-first public posts.
pub fn public_timeline_ref(w: &World, n: u64) -> Vec<u64> {
	// Early-stop: stop scanning once n public posts are collected; the prefix equals
	// take_n of the old full-filter output. n == 0 yields [] without scanning at all.
	if n == 0 {
		return vec![];
	}
	let mut acc = vec![];
	for pid in &w.newest_first {
		if is_post_public(w, *pid) {
			acc.push(*pid);
			if acc.len() as u64 >= n {
				break;
			}
		}
	}
	acc
}

/// get-public-global through the side-index; borrows the post cell per candidate.
pub fn public_timeline_ix(w: &World, ix: &WorldIndex, n: u64) -> Vec<u64> {
	// same early-stop as the reference; is_post_public_ix answers from the index without a clone
	if n == 0 {
		return vec![];
	}
	let mut acc = vec![];
	for pid in &w.newest_first {
		if is_post_public_ix(w, ix, *pid) {
			acc.push(*pid);
			if acc.len() as u64 >= n {
				break;
			}
		}
	}
	acc
}

/// get-public-global: build the side-index once, then answer through it.
pub fn public_timeline(w: &World, n: u64) -> Vec<u64> {
	// fresh side-index; every lookup then goes through the map instead of a scan
	let ix: WorldIndex = build_index(w);
	public_timeline_ix(w, &ix, n)
}

/// Spec empty-world.
pub fn empty_world() -> World {
	World {
		accounts: vec![],
		sessions: vec![],
		posts: vec![],
		follows: vec![],
		newest_first: vec![],
		used_post_ids: vec![],
		used_session_ids: vec![],
	}
}

/// Spec WellFormed invariants.
/// Not enforced at runtime: kept for the D1 proof work, never called on the wire path.
pub fn well_formed(w: &World) -> bool {
	for (pid, post) in &w.posts {
		if !member(&w.used_post_ids, *pid) {
			return false;
		}
		if !unique(&post.likes) || !unique(&post.replies) {
			return false;
		}
		for child in &post.replies {
			if *child == *pid {
				return false;
			}
			match post_at_ref(w, *child) {
				None => return false,
				Some(cp) => {
					if cp.parent != Some(*pid) {
						return false;
					}
				}
			}
		}
	}
	for pid in &w.used_post_ids {
		if post_at_ref(w, *pid).is_none() {
			return false;
		}
	}
	for (sid, st) in &w.sessions {
		match st {
			SessionStatus::Active(user) => {
				if account_at_ref(w, user).is_none() {
					return false;
				}
			}
			SessionStatus::Unused => {
				if member(&w.used_session_ids, *sid) {
					return false;
				}
			}
			_ => (),
		}
	}
	for sid in &w.used_session_ids {
		if session_at(w, *sid) == SessionStatus::Unused {
			return false;
		}
	}
	for pid in &w.newest_first {
		if post_at_ref(w, *pid).is_none() {
			return false;
		}
	}
	if !unique(&w.newest_first) {
		return false;
	}
	true
}

/// Index-backed Deterministic Step: same rule as step, every lookup answered through prebuilt ix.
pub fn step_ix(
	w: &World,
	ix: &WorldIndex,
	cmd: Command,
	fresh_pid: u64,
	fresh_sid: u64,
) -> (World, Result) {
	let expired: bool = match extract_sid(cmd.clone()) {
		Some(sid) => !valid_session_ix(w, ix, sid),
		None => false,
	};
	if expired {
		return (w.clone(), Result::Expired);
	}
	match cmd {
		Command::Publish(sid, txt, parent) => {
			if used_pid(w, fresh_pid) {
				return (w.clone(), Result::Denied);
			}
			let user = active_user_ix(w, ix, sid).unwrap();
			let acc = account_at_ix(w, ix, &user);
			let mut vis: Visibility = Visibility::Everyone;
			if let Some(a) = acc {
				vis = a.default_visibility;
			}
			let readable: bool = match parent {
				Some(ppid) => can_read_ix(w, ix, sid, ppid),
				None => true,
			};
			if !readable {
				return (w.clone(), Result::Denied);
			}
			let parent_vis: Option<Visibility> = match parent {
				Some(ppid) => match post_at_ix(w, ix, ppid) {
					Some(ppost) => Some(ppost.visibility),
					None => None,
				},
				None => None,
			};
			if parent_vis == Some(Visibility::FollowersOnly) {
				vis = Visibility::FollowersOnly;
			}
			let post = Post {
				author: user.clone(),
				text: txt.clone(),
				visibility: vis,
				status: PostStatus::Other,
				likes: vec![],
				replies: vec![],
				parent,
			};
			let mut nw = w.clone();
			nw.posts.push((fresh_pid, post));
			nw.newest_first.insert(0, fresh_pid);
			nw.used_post_ids.push(fresh_pid);
			// (RV5) spec successful-reply premise World.post-at after ppid = just ppost' with
			// Post.replies ppost' = pid ∷ Post.replies ppost: the parent post's replies list
			// gains the child pid at the head.  The readable guard above already proved ppid
			// exists and is live, and fresh_pid is unused, so it appears in no replies list:
			// the prepend keeps Post.replies uniq and child.parent = just ppid stays set.
			if let Some(ppid) = parent {
				for e in &mut nw.posts {
					if e.0 == ppid {
						(e.1.replies).insert(0, fresh_pid);
						break;
					}
				}
			}
			(nw, Result::CreatedPost(fresh_pid))
		}
		Command::Delete(sid, pid) => {
			let user = active_user_ix(w, ix, sid).unwrap();
			match post_at_ix(w, ix, pid) {
				None => (w.clone(), Result::Denied),
				Some(post) => {
					if post.author != user {
						(w.clone(), Result::Denied)
					} else {
						let mut nw = w.clone();
						for e in &mut nw.posts {
							if e.0 == pid {
								e.1.status = PostStatus::Deleted;
							}
						}
						(nw, Result::Success)
					}
				}
			}
		}
		Command::ReadPost(msid, pid) => {
			let readable: bool = match msid {
				None => is_post_public_ix(w, ix, pid),
				Some(sid) => can_read_ix(w, ix, sid, pid),
			};
			if !readable {
				return (w.clone(), Result::Denied);
			}
			match post_at_ix(w, ix, pid) {
				None => (w.clone(), Result::Denied),
				Some(post) => (
					w.clone(),
					Result::ReturnedPost(
						post.author,
						post.text,
						len_u64(&post.likes),
						post.replies.clone(),
					),
				),
			}
		}
		Command::ReadPersonalTimeline(sid, n) => (
			w.clone(),
			Result::ReturnedTimeline(personal_timeline_ix(w, ix, sid, n)),
		),
		Command::ReadGlobalTimeline(msid, n) => {
			let ids: Vec<u64> = match msid {
				None => public_timeline_ix(w, ix, n),
				Some(sid) => global_timeline_ix(w, ix, sid, n),
			};
			(w.clone(), Result::ReturnedTimeline(ids))
		}
		Command::Authenticate(user, passwd) => {
			let issued: bool = match account_at_ix(w, ix, &user) {
				None => false,
				Some(acc) => acc.password == passwd && !used_sid(w, fresh_sid),
			};
			if issued {
				let mut nw = w.clone();
				nw.sessions
					.push((fresh_sid, SessionStatus::Active(user.clone())));
				nw.used_session_ids.push(fresh_sid);
				(nw, Result::IssuedSession(fresh_sid))
			} else {
				(w.clone(), Result::LoginFailed)
			}
		}
		Command::RevokeToken(sid) => {
			let mut nw = w.clone();
			for e in &mut nw.sessions {
				if e.0 == sid {
					e.1 = SessionStatus::Revoked;
				}
			}
			(nw, Result::Success)
		}
		Command::Register(user, passwd) => {
			if account_at_ix(w, ix, &user).is_some() {
				(w.clone(), Result::SignupFailed)
			} else {
				let mut nw = w.clone();
				nw.accounts.push((
					user,
					Account {
						password: passwd,
						default_visibility: Visibility::Everyone,
					},
				));
				(nw, Result::Success)
			}
		}
		Command::Follow(sid, followee) => {
			let user = active_user_ix(w, ix, sid).unwrap();
			if follows_ix(w, ix, &user, &followee) {
				(w.clone(), Result::Success)
			} else {
				let mut nw = w.clone();
				nw.follows.push((user, followee));
				(nw, Result::Success)
			}
		}
		Command::Unfollow(sid, followee) => {
			let user = active_user_ix(w, ix, sid).unwrap();
			let mut nw = w.clone();
			// (in-place retain drops the exact pair, no rebuild, no clones)
			nw.follows.retain(|(f, g)| *f != user || *g != followee);
			(nw, Result::Success)
		}
		Command::Like(sid, pid) => {
			if !can_read_ix(w, ix, sid, pid) {
				return (w.clone(), Result::Denied);
			}
			let user = active_user_ix(w, ix, sid).unwrap();
			let mut nw = w.clone();
			for e in &mut nw.posts {
				// (only posts with this pid react; others keep their like lists untouched)
				if e.0 == pid {
					// already liked: no clone and no duplicate, spec-set idempotence
					// (contains borrows the list: no element copied for the check)
					if !(e.1.likes).contains(&user) {
						(e.1.likes).push(user.clone());
					}
				}
			}
			(nw, Result::Success)
		}
		Command::Unlike(sid, pid) => {
			if !can_read_ix(w, ix, sid, pid) {
				return (w.clone(), Result::Denied);
			}
			let user = active_user_ix(w, ix, sid).unwrap();
			let mut nw = w.clone();
			for e in &mut nw.posts {
				if e.0 == pid {
					// (in-place retain drops this user's likes; no clone/rebuild)
					(e.1.likes).retain(|x| *x != user);
				}
			}
			(nw, Result::Success)
		}
		Command::TimePasses => {
			let mut nw = w.clone();
			for e in &mut nw.sessions {
				if matches!(e.1, SessionStatus::Active(_)) {
					e.1 = SessionStatus::Revoked;
				}
			}
			(nw, Result::Success)
		}
	}
}

/// Deterministic Step: (before, cmd, fresh ids) -> (after, result). Failed-access is checked first.
pub fn step(w: &World, cmd: Command, fresh_pid: u64, fresh_sid: u64) -> (World, Result) {
	// fresh side-index per call; step_ix answers every lookup through it
	let ix: WorldIndex = build_index(w);
	step_ix(w, &ix, cmd, fresh_pid, fresh_sid)
}
/// Index-backed Deterministic Step as effect: same guards and orderings as step_ix, each branch returning (Result, Delta) with its payload built directly; no World is cloned.
pub fn step_d(
	w: &World,
	ix: &WorldIndex,
	cmd: Command,
	fresh_pid: u64,
	fresh_sid: u64,
) -> (Result, Delta) {
	let expired: bool = match extract_sid(cmd.clone()) {
		Some(sid) => !valid_session_ix(w, ix, sid),
		None => false,
	};
	if expired {
		return (Result::Expired, Delta::None_);
	}
	match cmd {
		Command::Publish(sid, txt, parent) => {
			if used_pid(w, fresh_pid) {
				return (Result::Denied, Delta::None_);
			}
			let user = active_user_ix(w, ix, sid).unwrap();
			let acc = account_at_ix(w, ix, &user);
			let mut vis: Visibility = Visibility::Everyone;
			if let Some(a) = acc {
				vis = a.default_visibility;
			}
			let readable: bool = match parent {
				Some(ppid) => can_read_ix(w, ix, sid, ppid),
				None => true,
			};
			if !readable {
				return (Result::Denied, Delta::None_);
			}
			let parent_vis: Option<Visibility> = match parent {
				Some(ppid) => match post_at_ix(w, ix, ppid) {
					Some(ppost) => Some(ppost.visibility),
					None => None,
				},
				None => None,
			};
			if parent_vis == Some(Visibility::FollowersOnly) {
				vis = Visibility::FollowersOnly;
			}
			(
				Result::CreatedPost(fresh_pid),
				Delta::Publish(fresh_pid, user, txt, vis, parent),
			)
		}
		Command::Delete(sid, pid) => {
			let user = active_user_ix(w, ix, sid).unwrap();
			match post_at_ix(w, ix, pid) {
				None => (Result::Denied, Delta::None_),
				Some(post) => {
					if post.author != user {
						(Result::Denied, Delta::None_)
					} else {
						(Result::Success, Delta::Delete(pid))
					}
				}
			}
		}
		Command::ReadPost(msid, pid) => {
			let readable: bool = match msid {
				None => is_post_public_ix(w, ix, pid),
				Some(sid) => can_read_ix(w, ix, sid, pid),
			};
			if !readable {
				return (Result::Denied, Delta::None_);
			}
			match post_at_ix(w, ix, pid) {
				None => (Result::Denied, Delta::None_),
				Some(post) => (
					Result::ReturnedPost(
						post.author,
						post.text,
						len_u64(&post.likes),
						post.replies.clone(),
					),
					Delta::None_,
				),
			}
		}
		Command::ReadPersonalTimeline(sid, n) => (
			Result::ReturnedTimeline(personal_timeline_ix(w, ix, sid, n)),
			Delta::None_,
		),
		Command::ReadGlobalTimeline(msid, n) => {
			let ids: Vec<u64> = match msid {
				None => public_timeline_ix(w, ix, n),
				Some(sid) => global_timeline_ix(w, ix, sid, n),
			};
			(Result::ReturnedTimeline(ids), Delta::None_)
		}
		Command::Authenticate(user, passwd) => {
			let issued: bool = match account_at_ix(w, ix, &user) {
				None => false,
				Some(acc) => acc.password == passwd && !used_sid(w, fresh_sid),
			};
			if issued {
				(
					Result::IssuedSession(fresh_sid),
					Delta::Authenticate(fresh_sid, user),
				)
			} else {
				(Result::LoginFailed, Delta::None_)
			}
		}
		Command::RevokeToken(sid) => (Result::Success, Delta::RevokeToken(sid)),
		Command::Register(user, passwd) => {
			if account_at_ix(w, ix, &user).is_some() {
				(Result::SignupFailed, Delta::None_)
			} else {
				(
					Result::Success,
					Delta::Register(
						user,
						Account {
							password: passwd,
							default_visibility: Visibility::Everyone,
						},
					),
				)
			}
		}
		Command::Follow(sid, followee) => {
			let user = active_user_ix(w, ix, sid).unwrap();
			if follows_ix(w, ix, &user, &followee) {
				(Result::Success, Delta::None_)
			} else {
				(Result::Success, Delta::Follow(user, followee))
			}
		}
		Command::Unfollow(sid, followee) => {
			let user = active_user_ix(w, ix, sid).unwrap();
			(Result::Success, Delta::Unfollow(user, followee))
		}
		Command::Like(sid, pid) => {
			if !can_read_ix(w, ix, sid, pid) {
				return (Result::Denied, Delta::None_);
			}
			let user = active_user_ix(w, ix, sid).unwrap();
			(Result::Success, Delta::Like(pid, user))
		}
		Command::Unlike(sid, pid) => {
			if !can_read_ix(w, ix, sid, pid) {
				return (Result::Denied, Delta::None_);
			}
			let user = active_user_ix(w, ix, sid).unwrap();
			(Result::Success, Delta::Unlike(pid, user))
		}
		Command::TimePasses => {
			// every sid whose session is Active: exactly the ones step revokes
			let mut sids: Vec<u64> = vec![];
			for e in &w.sessions {
				if matches!(e.1, SessionStatus::Active(_)) {
					sids.push(e.0);
				}
			}
			(Result::Success, Delta::TimePasses(sids))
		}
	}
}

/// Apply a Delta to an owned World: reproduces step_ix's field mutations exactly (same push order, insert index, retain, status sets), touching only the delta's targets.
pub fn patch_world(w: World, d: Delta) -> World {
	// the World moves in; targeted in-place mutation, no rebuild and no World clone
	let mut nw: World = w;
	match d {
		Delta::None_ => {}
		Delta::Publish(pid, author, text, visibility, parent) => {
			nw.posts.push((
				pid,
				Post {
					author,
					text,
					visibility,
					status: PostStatus::Other,
					likes: vec![],
					replies: vec![],
					parent,
				},
			));
			nw.newest_first.insert(0, pid);
			nw.used_post_ids.push(pid);
			// (RV5) same successful-reply effect as step_ix, read off the Delta's parent payload:
			// step_d already ships the parent in Publish, so patch prepends the child pid onto
			// the parent's replies list, keeping the RAM cache equal to step's after-world
			// (the DB gains the matching replies row in apply_delta, so reloads agree too).
			// Only prepend when the parent exists; the fresh pid is unused, hence reply-uniq.
			if let Some(ppid) = parent {
				for e in &mut nw.posts {
					if e.0 == ppid {
						(e.1.replies).insert(0, pid);
						break;
					}
				}
			}
		}
		Delta::Delete(pid) => {
			for e in &mut nw.posts {
				if e.0 == pid {
					e.1.status = PostStatus::Deleted;
				}
			}
		}
		Delta::Authenticate(sid, user) => {
			nw.sessions.push((sid, SessionStatus::Active(user)));
			nw.used_session_ids.push(sid);
		}
		Delta::RevokeToken(sid) => {
			for e in &mut nw.sessions {
				if e.0 == sid {
					e.1 = SessionStatus::Revoked;
				}
			}
		}
		Delta::Register(user, acct) => nw.accounts.push((user, acct)),
		Delta::Follow(follower, followee) => nw.follows.push((follower, followee)),
		Delta::Unfollow(follower, followee) => {
			nw.follows.retain(|(f, g)| *f != follower || *g != followee)
		}
		Delta::Like(pid, user) => {
			for e in &mut nw.posts {
				// only posts with this pid react; already-liked keeps the list untouched (idempotence)
				if e.0 == pid && !(e.1.likes).contains(&user) {
					(e.1.likes).push(user.clone());
				}
			}
		}
		Delta::Unlike(pid, user) => {
			for e in &mut nw.posts {
				if e.0 == pid {
					(e.1.likes).retain(|x| *x != user);
				}
			}
		}
		Delta::TimePasses(sids) => {
			for e in &mut nw.sessions {
				// revokes exactly the sids carried in the payload
				if sids.contains(&e.0) {
					e.1 = SessionStatus::Revoked;
				}
			}
		}
	}
	nw
}

#[cfg(test)]
mod qc {
	use super::{
		Account, Command, Delta, Post, PostStatus, Result, SessionStatus, Visibility, World,
		WorldIndex, access_ok, access_ok_ix, account_at, account_at_ix, account_at_ref,
		active_user, active_user_ix, active_user_ref, build_index, can_read, can_read_ix,
		empty_world, extract_sid, follows, follows_author, follows_ix, global_timeline,
		global_timeline_ix, global_timeline_ref, is_post_public, is_post_public_ix, len_u64,
		member, patch_world, personal_timeline, personal_timeline_ix, personal_timeline_ref,
		post_at, post_at_ix, post_at_ref, public_timeline, public_timeline_ix, public_timeline_ref,
		session_at, session_at_ix, step, step_d, step_ix, take_n, unique, used_pid, used_sid,
		valid_session, valid_session_ix, well_formed,
	};
	use quickcheck::{Arbitrary, Gen};
	use quickcheck_macros::quickcheck;

	/// Constant pools: generated worlds and commands share id and user pools so tests interact.
	const SIDS: [u64; 4] = [1, 2, 3, 4];
	const PIDS: [u64; 5] = [1, 2, 3, 4, 5];
	const NS: [u64; 4] = [0, 1, 2, 3];
	const VIS: [Visibility; 2] = [Visibility::Everyone, Visibility::FollowersOnly];
	const STA: [PostStatus; 2] = [PostStatus::Other, PostStatus::Deleted];

	/// Choose an element, falling back to the first if the generator declines.
	fn pick<T: Clone>(g: &mut Gen, xs: &[T]) -> T {
		if let Some(ok) = g.choose(xs) {
			return ok.clone();
		}
		xs[0].clone()
	}

	fn coin(g: &mut Gen) -> bool {
		pick(g, &[true, false])
	}

	fn users_pool() -> [String; 4] {
		[
			"a".to_string(),
			"b".to_string(),
			"c".to_string(),
			"d".to_string(),
		]
	}

	/// Password pool: build_world gives every account "p" (see the Account below), so commands
	/// must mix "p" with a mismatch or prop_login_wrong_password could never fire.
	fn passwd_pool() -> [String; 2] {
		["p".to_string(), "q".to_string()]
	}

	/// Session status after a revoke/time-passes application.
	fn expected_revoke(st: SessionStatus) -> SessionStatus {
		match st {
			SessionStatus::Active(_) => SessionStatus::Revoked,
			_ => st,
		}
	}

	/// Command destructors for the properties.
	fn as_register(cmd: Command) -> Option<String> {
		match cmd {
			Command::Register(user, _) => Some(user.clone()),
			_ => None,
		}
	}

	fn as_authenticate(cmd: Command) -> Option<(String, String)> {
		match cmd {
			Command::Authenticate(user, passwd) => Some((user.clone(), passwd.clone())),
			_ => None,
		}
	}

	fn as_follow(cmd: Command) -> Option<(u64, String)> {
		match cmd {
			Command::Follow(sid, user) => Some((sid, user.clone())),
			_ => None,
		}
	}

	fn as_like(cmd: Command) -> Option<(u64, u64)> {
		match cmd {
			Command::Like(sid, pid) => Some((sid, pid)),
			_ => None,
		}
	}

	fn as_delete(cmd: Command) -> Option<(u64, u64)> {
		match cmd {
			Command::Delete(sid, pid) => Some((sid, pid)),
			_ => None,
		}
	}

	fn as_revoke(cmd: Command) -> Option<u64> {
		match cmd {
			Command::RevokeToken(sid) => Some(sid),
			_ => None,
		}
	}

	fn as_read(cmd: Command) -> Option<(Option<u64>, u64)> {
		match cmd {
			Command::ReadPost(msid, pid) => Some((msid, pid)),
			_ => None,
		}
	}

	fn as_publish(cmd: Command) -> Option<(u64, String, Option<u64>)> {
		match cmd {
			Command::Publish(sid, txt, parent) => Some((sid, txt.clone(), parent)),
			_ => None,
		}
	}

	/// Fresh post/session ids handed to step.
	#[derive(Clone, Debug)]
	struct StepArgs {
		/// pid: fresh post id candidate
		pid: u64,
		/// sid: fresh session id candidate
		sid: u64,
	}

	/// Build a world that is well-formed by construction: accounts first, then sessions whose users have accounts, then posts with reply parents pointing back, then ids.
	fn build_world(g: &mut Gen) -> World {
		let mut w: World = empty_world();
		for u in users_pool() {
			if coin(g) {
				w.accounts.push((
					u.clone(),
					Account {
						password: "p".to_string(),
						default_visibility: pick(g, &VIS),
					},
				));
			}
		}
		for sid in SIDS {
			if pick(g, &[true, false, false]) {
				let mut st: SessionStatus = SessionStatus::Revoked;
				if !w.accounts.is_empty() && coin(g) {
					st = SessionStatus::Active(pick(g, &w.accounts).0);
				}
				w.sessions.push((sid, st));
				w.used_session_ids.push(sid);
			}
		}
		// (RV5) follows pairs, so qc worlds positively exercise follow-gated reads (personal
		// timeline, FollowersOnly can-read via follows, prop_follow with a prior pair present).
		// Followers range over users who HAVE accounts (session users come from accounts); the
		// followee is any other pool user. One shot per ordered pair, so the pairs stay uniq.
		// A copy kept in follows_pool drives the author bias below.
		let us_all: [String; 4] = users_pool();
		let mut follows_pool: Vec<(String, String)> = vec![];
		for (follower, _) in &w.accounts {
			for followee in &us_all {
				if *followee != *follower && pick(g, &[true, false, false]) {
					w.follows.push((follower.clone(), followee.clone()));
					follows_pool.push((follower.clone(), followee.clone()));
				}
			}
		}
		// at least one pair whenever any account exists, so follow-gated positives fire often
		if follows_pool.is_empty() && !w.accounts.is_empty() {
			let (follower, _acct) = pick(g, &w.accounts);
			let mut cands: Vec<String> = vec![];
			for u in &us_all {
				if *u != follower {
					cands.push(u.clone());
				}
			}
			let pair: (String, String) = (follower.clone(), pick(g, &cands));
			w.follows.push(pair.clone());
			follows_pool.push(pair);
		}
		// (RV5) reply bookkeeping: parents records (pid, parent) for the reply-backlink pass;
		// readable_parents tracks live+Everyone pids so reply posts pick a READABLE parent
		// (a qc Publish with that parent then passes the can_read guard, not only failed-reply).
		let mut parents: Vec<(u64, Option<u64>)> = vec![];
		let mut readable_parents: Vec<u64> = vec![];
		for pid in PIDS {
			if pick(g, &[true, true, false]) {
				let us: [String; 4] = users_pool();
				// (RV5) author bias: with prob 2/3 the author is a followed user, so worlds
				// positively exercise follow-gated reads (personal timeline, FO can-read via follows)
				// and private posts by followed authors occur (VIS already mixes both).
				let author: String = if !follows_pool.is_empty() && pick(g, &[true, true, false]) {
					pick(g, &follows_pool).1
				} else {
					pick(g, &us)
				};
				let vis: Visibility = pick(g, &VIS);
				let status: PostStatus = pick(g, &STA);
				// (RV5) reply parent preference: 2/3 of replies point at a live+Everyone post,
				// i.e. a parent any valid session can READ, so qc reply-publish hits the
				// successful-reply rule (not only failed-reply); the rest keep the old,
				// arbitrary-parent behaviour including deleted/FO parents.
				let parent: Option<u64> =
					if !readable_parents.is_empty() && pick(g, &[true, true, false]) {
						Some(pick(g, &readable_parents))
					} else if parents.is_empty() || !coin(g) {
						None
					} else {
						Some(pick(g, &parents).0)
					};
				let mut likes: Vec<String> = vec![];
				for u in users_pool() {
					if coin(g) {
						likes.push(u.clone());
					}
				}
				parents.push((pid, parent));
				// (RV5) candidate for readable reply-parents: live (status Other) AND public
				// (Everyone) so a later reply pointing at it passes can_read with any valid sid.
				if status == PostStatus::Other && vis == Visibility::Everyone {
					readable_parents.push(pid);
				}
				w.posts.push((
					pid,
					Post {
						author,
						text: "t".to_string(),
						visibility: vis,
						status,
						likes,
						replies: vec![],
						parent,
					},
				));
				w.used_post_ids.push(pid);
				if coin(g) {
					w.newest_first.insert(0, pid);
				} else {
					w.newest_first.push(pid);
				}
			}
		}
		for (pid, parent) in parents {
			if let Some(ppid) = parent {
				for e in &mut w.posts {
					if e.0 == ppid {
						e.1.replies.push(pid);
					}
				}
			}
		}
		w
	}

	impl Arbitrary for World {
		/// Generated worlds are always well-formed; the retry is defensive.
		fn arbitrary(g: &mut Gen) -> Self {
			let mut tries: u64 = 0;
			while tries < 20 {
				tries += 1;
				let w: World = build_world(g);
				if well_formed(&w) {
					return w;
				}
			}
			empty_world()
		}

		/// No shrinking: shrinking could break well-formedness invariants.
		fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
			let empty: Vec<Self> = vec![];
			Box::new(empty.into_iter())
		}
	}

	impl Arbitrary for Command {
		fn arbitrary(g: &mut Gen) -> Self {
			let sid: u64 = pick(g, &SIDS);
			let pid: u64 = pick(g, &PIDS);
			let us: [String; 4] = users_pool();
			let user: String = pick(g, &us);
			let other: String = pick(g, &us);
			let n: u64 = pick(g, &NS);
			let msid: Option<u64> = if coin(g) { Some(sid) } else { None };
			match pick(
				g,
				&[
					0u64, 1u64, 2u64, 3u64, 4u64, 5u64, 6u64, 7u64, 8u64, 9u64, 10u64, 11u64, 12u64,
				],
			) {
				0u64 => {
					Command::Publish(sid, "t".to_string(), if coin(g) { Some(pid) } else { None })
				}
				1u64 => Command::Delete(sid, pid),
				2u64 => Command::ReadPost(msid, pid),
				3u64 => Command::ReadPersonalTimeline(sid, n),
				4u64 => Command::ReadGlobalTimeline(msid, n),
				// (RV5) passwords come from passwd_pool, so both the matching (login) and the
				// mismatching (failed-login-2) branches of Authenticate occur in qc worlds.
				5u64 => Command::Authenticate(user, pick(g, &passwd_pool())),
				6u64 => Command::RevokeToken(sid),
				7u64 => Command::Register(other, "p".to_string()),
				8u64 => Command::Follow(sid, other),
				9u64 => Command::Unfollow(sid, other),
				10u64 => Command::Like(sid, pid),
				11u64 => Command::Unlike(sid, pid),
				_ => Command::TimePasses,
			}
		}

		fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
			let empty: Vec<Self> = vec![];
			Box::new(empty.into_iter())
		}
	}

	impl Arbitrary for StepArgs {
		fn arbitrary(g: &mut Gen) -> Self {
			StepArgs {
				pid: pick(g, &PIDS),
				sid: pick(g, &SIDS),
			}
		}

		fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
			let empty: Vec<Self> = vec![];
			Box::new(empty.into_iter())
		}
	}

	/// RV5-3 publish cases: the world and the PUBLISH command are drawn TOGETHER (a plain
	/// World/Command/StepArgs triple hits a publish-with-valid-session-and-fresh-id-and-readable-
	/// parent only about once in 470 cases, so quickcheck's 100 would never reach the three publish
	/// rules).  The command is aimed at the world it was generated with -- session from the world's
	/// valid ones, child id from the world's unused ones, parent readable / blocked / NOTHING -- so
	/// all three spec rules (successful-post, successful-reply, failed-reply) fire often, while the
	/// random fallbacks keep the negative guards reachable.  Still an Arbitrary instance, hence the
	/// props below stay universal tests.
	#[derive(Clone, Debug)]
	struct PublishCase {
		/// the world the publish command is drawn against
		w: World,
		/// a publish command aimed at that world
		cmd: Command,
		/// the fresh post/session ids handed to step
		ids: StepArgs,
	}

	impl Arbitrary for PublishCase {
		fn arbitrary(g: &mut Gen) -> Self {
			let w: World = build_world(g);
			// a session that really has a ValidSession most of the time, so the publish rules'
			// session premise is satisfiable (build_world's session pool is sparse)
			let mut ok_sids: Vec<u64> = vec![];
			for sid in SIDS {
				if valid_session(&w, sid) {
					ok_sids.push(sid);
				}
			}
			let sid: u64 = if !ok_sids.is_empty() && pick(g, &[true, true, false]) {
				pick(g, &ok_sids)
			} else {
				pick(g, &SIDS)
			};
			// a child id the world has NOT used, so step creates instead of refusing on its
			// impl-defined used-post-ids guard
			let mut free_pids: Vec<u64> = vec![];
			for pid in PIDS {
				if !used_pid(&w, pid) {
					free_pids.push(pid);
				}
			}
			let fresh_pid: u64 = if !free_pids.is_empty() && pick(g, &[true, true, false]) {
				pick(g, &free_pids)
			} else {
				pick(g, &PIDS)
			};
			// readable/blocked parents for that session: successful-reply vs failed-reply
			let mut readable: Vec<u64> = vec![];
			let mut blocked: Vec<u64> = vec![];
			for pp in PIDS {
				if can_read(&w, sid, pp) {
					readable.push(pp);
				} else {
					blocked.push(pp);
				}
			}
			// parent choice: NOTHING (successful-post) / a parent the session CAN read (successful-
			// reply) / a parent it cannot (failed-reply, missing posts included)
			let mut parent: Option<u64> = None;
			let choice: u64 = pick(g, &[0u64, 1u64, 2u64, 3u64]);
			if choice == 0u64 {
				// NOTHING parent: the successful-post half of step's Publish arm
				parent = None;
			} else {
				let pool: Vec<u64> = if choice == 1u64 || choice == 2u64 {
					readable
				} else {
					blocked
				};
				if !pool.is_empty() {
					parent = Some(pick(g, &pool));
				} else if pick(g, &[true, false]) {
					// fallback parent so the blocked/missing branch stays reachable in sparse worlds
					parent = Some(pick(g, &PIDS));
				}
			}
			let pc = Command::Publish(sid, "t".to_string(), parent);
			PublishCase {
				w,
				ids: StepArgs {
					pid: fresh_pid,
					sid: pick(g, &SIDS),
				},
				cmd: pc,
			}
		}

		/// No shrinking: shrinking could break the world's well-formedness invariants.
		fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
			let empty: Vec<Self> = vec![];
			Box::new(empty.into_iter())
		}
	}

	/// QC of expired-access: a command run through a session lacking a valid session leaves the world unchanged and yields Expired.
	#[quickcheck]
	fn prop_expired_access(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		let (nw, res) = step(&w, cmd.clone(), ids.pid, ids.sid);
		match extract_sid(cmd) {
			Some(sid) => {
				if !valid_session(&w, sid) {
					res == Result::Expired && nw == w
				} else {
					true
				}
			}
			None => true,
		}
	}

	/// QC of register-new: an unused username gains an account with Everyone visibility.
	#[quickcheck]
	fn prop_register_creates(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if let Some(user) = as_register(cmd.clone())
			&& account_at(&w, &user).is_none()
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			return res == Result::Success
				&& account_at(&nw, &user)
					== Some(Account {
						password: "p".to_string(),
						default_visibility: Visibility::Everyone,
					});
		}
		true
	}

	/// QC of register-taken: an existing username yields SignupFailed and no change.
	#[quickcheck]
	fn prop_register_taken(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if let Some(user) = as_register(cmd.clone())
			&& account_at(&w, &user).is_some()
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			return res == Result::SignupFailed && nw == w;
		}
		true
	}

	/// QC of login-success (spec login, Twitter.agda:490): a matching password plus a FRESH
	/// session id issues exactly that session.  This pins the ACTUAL shape of step's Authenticate
	/// arm: the result is IssuedSession(ids.sid), the sessions section gains sid -> Active(user)
	/// (Rust's session-at representation), the used-session-ids section gains ids.sid, and every
	/// other section is carried untouched (nw == want outright).  Freshness of ids.sid is a
	/// HYPOTHESIS only: step's refusal of an already-used sid (LoginFailed, world unchanged) is
	/// IMPL-DEFINED, not a spec rule -- the spec's login constructor never names World.used-session-ids
	/// (the only-used-sids World field pairs that section with session-at), so no used-sid case is
	/// asserted here.  th-prop-login-issued (ImplProofs.agda) pins the spec-forced half: the
	/// session-at flip to active username plus the constructor's sectionwise rest premise.
	#[quickcheck]
	fn prop_login_success(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if let Some((user, passwd)) = as_authenticate(cmd.clone())
			&& (match account_at_ref(&w, &user) {
				Some(acc) => acc.password == passwd,
				None => false,
			}) && !used_sid(&w, ids.sid)
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			// step pushes exactly one session entry and exactly one used sid, carrying the rest
			let mut want: World = w;
			want.sessions
				.push((ids.sid, SessionStatus::Active(user.clone())));
			want.used_session_ids.push(ids.sid);
			return res == Result::IssuedSession(ids.sid)
				&& session_at(&nw, ids.sid) == SessionStatus::Active(user)
				&& nw == want;
		}
		true
	}

	/// QC of login-unknown-user (spec failed-login-1, Twitter.agda:507): with no account at all
	/// the login fails and the world is untouched.  ANY sid: extract-sid (authenticate _ _) is
	/// nothing, so the failed-access constructor can never fire on this command.
	#[quickcheck]
	fn prop_login_unknown_user(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if let Some((user, _)) = as_authenticate(cmd.clone())
			&& account_at(&w, &user).is_none()
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			return res == Result::LoginFailed && nw == w;
		}
		true
	}

	/// QC of login-wrong-password (spec failed-login-2, Twitter.agda:512): an account whose
	/// password differs, with a FRESH sid, still fails and changes nothing -- the fresh-sid
	/// hypothesis mirrors the spec's session-at before sid ≡ unused premise, and step's used-sid
	/// guard (same LoginFailed, same world) stays impl-defined and unhypothesised.
	#[quickcheck]
	fn prop_login_wrong_password(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if let Some((user, passwd)) = as_authenticate(cmd.clone())
			&& (match account_at_ref(&w, &user) {
				Some(acc) => acc.password != passwd,
				None => false,
			}) && !used_sid(&w, ids.sid)
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			return res == Result::LoginFailed && nw == w;
		}
		true
	}

	/// QC of publish-new (spec successful-post, Twitter.agda:387): a VALID session publishing with a
	/// NOTHING parent and a FRESH post id creates exactly that post -- author = the session's user, text =
	/// the command's txt, visibility = the ACCOUNT's default-visibility (step's Publish arm reads account-at
	/// at model.rs:773-777, the spec's new-post, Twitter.agda:209), status live, likes empty, replies EMPTY,
	/// parent Nothing -- with nw.posts GAINING that entry, newest_first PREPENDED with ids.pid
	/// (nw.newest_first.insert(0, fresh_pid), model.rs:806 -- the spec premise pid ∷ newest-first before ≡
	/// newest-first after) and used_post_ids GAINING ids.pid (model.rs:807), every other section carried
	/// untouched, so nw == want outright.  Freshness of ids.pid is a HYPOTHESIS only: step's refusal of an
	/// already-used id (Denied, world unchanged, model.rs:769-771) is IMPL-DEFINED -- the spec's successful-post
	/// never names World.used-post-ids; its PostIsNew premise only forces World.post-at before pid ≡ nothing.
	/// th-prop-publish-new (ImplProofs.agda) pins the spec-forced half: was-absent + is-present (the new-post
	/// SHAPE) + the newest-first prepend + the constructor's POINTWISE rest, mirrored verbatim.
	#[quickcheck]
	fn prop_publish_new(c: PublishCase) -> bool {
		let w: World = c.w;
		let cmd: Command = c.cmd;
		let ids: StepArgs = c.ids;
		if !well_formed(&w) {
			return true;
		}
		if let Some((sid, txt, parent)) = as_publish(cmd.clone())
			&& parent.is_none()
			&& valid_session(&w, sid)
			&& !used_pid(&w, ids.pid)
			&& let Some(user) = active_user(&w, sid)
			&& let Some(acc) = account_at(&w, &user)
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			// step's Publish arm (model.rs:795-807): the created post, one posts entry, newest-first
			// prepend, used-id gain -- everything else identical
			let fresh: Post = Post {
				author: user.clone(),
				text: txt.clone(),
				visibility: acc.default_visibility,
				status: PostStatus::Other,
				likes: vec![],
				replies: vec![],
				parent,
			};
			// the fresh id was absent beforehand: the spec's PostIsNew was-absent premise, implied here
			// by well_formed (used-post-ids and posts agree) plus the !used_pid hypothesis
			let absent: bool = post_at(&w, ids.pid).is_none();
			let mut want: World = w;
			want.posts.push((ids.pid, fresh.clone()));
			want.newest_first.insert(0, ids.pid);
			want.used_post_ids.push(ids.pid);
			return res == Result::CreatedPost(ids.pid)
				&& absent
				// post-at after pid = just (new-post username txt acc): the spec's is-present premise
				&& post_at(&nw, ids.pid) == Some(fresh)
				&& nw == want;
		}
		true
	}

	/// QC of reply-publish (spec successful-reply, Twitter.agda:401): a VALID session publishing under a
	/// READABLE parent -- can_read (the spec's CanReadPost, Twitter.agda:168-187: live AND (Everyone OR
	/// FollowersOnly-with-follows)) -- with a FRESH child id and child pid != parent pid (the spec's pid ≢ ppid
	/// premise) creates CreatedPost(ids.pid) whose post has parent = just ppid, status live, empty likes/replies,
	/// and VISIBILITY INHERITED from the parent (model.rs:785-794 copies the parent's visibility when it is
	/// FollowersOnly, else the account's default -- exactly the spec's new-reply pair, Twitter.agda:213-217) --
	/// plus the RV5-0 reply bookkeeping: the PARENT post's replies list gains the child pid at the HEAD
	/// (model.rs:813-819, the spec premise World.post-at after ppid ≡ just (post ... (pid ∷ preplies) ...)),
	/// newest_first PREPENDED, used_post_ids GAINED, every other section untouched (nw == want outright).
	/// step's used-pid refusal (model.rs:769-771) is IMPL-DEFINED -- the spec's successful-reply never names
	/// World.used-post-ids -- so freshness stays a hypothesis only.  th-prop-publish-reply pins the spec half.
	#[quickcheck]
	fn prop_reply_publish(c: PublishCase) -> bool {
		let w: World = c.w;
		let cmd: Command = c.cmd;
		let ids: StepArgs = c.ids;
		if !well_formed(&w) {
			return true;
		}
		if let Some((sid, txt, Some(ppid))) = as_publish(cmd.clone())
			&& ids.pid != ppid
			&& valid_session(&w, sid)
			&& can_read(&w, sid, ppid)
			&& !used_pid(&w, ids.pid)
			&& let Some(pparent) = post_at(&w, ppid)
			&& let Some(user) = active_user(&w, sid)
			&& let Some(acc) = account_at(&w, &user)
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			// VISIBILITY INHERITANCE (model.rs:785-794): the parent's FollowersOnly wins, otherwise the
			// account's default-visibility -- the spec new-reply's two clauses on the parent's visibility
			let vis: Visibility = if pparent.visibility == Visibility::FollowersOnly {
				Visibility::FollowersOnly
			} else {
				acc.default_visibility
			};
			let child: Post = Post {
				author: user.clone(),
				text: txt.clone(),
				visibility: vis,
				status: PostStatus::Other,
				likes: vec![],
				replies: vec![],
				// child.parent = just ppid: the spec's new-reply last argument
				parent: Some(ppid),
			};
			// the parent post as it is AFTERWARDS: same author/text/visibility/status/likes, replies PREPENDED
			// with the child pid (RV5-0, model.rs:813-819)
			let mut parent_after: Post = pparent;
			(parent_after.replies).insert(0, ids.pid);
			// step pushes the new post FIRST (model.rs:805) and only then patches the parent entry
			// (model.rs:813-819), so the posts section order is old ++ [child] with the parent rewritten in place
			let mut want: World = w;
			want.posts.push((ids.pid, child.clone()));
			for e in &mut want.posts {
				if e.0 == ppid {
					e.1 = parent_after.clone();
					break;
				}
			}
			// newest-first PREPENDED (model.rs:806, the spec premise pid ∷ newest-first before ≡
			// newest-first after) and used_post_ids GAINED (model.rs:807: no spec constructor names
			// World.used-post-ids, so that gain is witnessed by OUR step, not by the spec relation)
			want.newest_first.insert(0, ids.pid);
			want.used_post_ids.push(ids.pid);
			return res == Result::CreatedPost(ids.pid)
				&& post_at(&nw, ids.pid) == Some(child)
				&& post_at(&nw, ppid) == Some(parent_after)
				&& nw == want;
		}
		true
	}

	/// QC of failed-reply (spec failed-reply, Twitter.agda:424): a VALID session whose JUST parent is NOT
	/// readable -- no CanReadPost constructor fits, i.e. the parent is missing, deleted, or FollowersOnly by an
	/// author the session user does not follow -- is Denied and the world is UNTOUCHED (step's model.rs:782-784,
	/// w.clone() with no section touched).  step's used-pid guard (model.rs:769-771) returns the SAME (w, Denied)
	/// but is IMPL-DEFINED -- the spec's failed-reply never names World.used-post-ids -- so freshness of ids.pid
	/// stays out of the hypotheses; th-prop-publish-denied pins the spec-forced half (Denied forces after ≡ before).
	#[quickcheck]
	fn prop_reply_denied(c: PublishCase) -> bool {
		let w: World = c.w;
		let cmd: Command = c.cmd;
		let ids: StepArgs = c.ids;
		if !well_formed(&w) {
			return true;
		}
		if let Some((sid, _, Some(ppid))) = as_publish(cmd.clone())
			&& valid_session(&w, sid)
			&& !can_read(&w, sid, ppid)
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			return res == Result::Denied && nw == w;
		}
		true
	}

	/// QC of revoke-token: only the named session changes, and only to Revoked.
	/// Theorem-backed half (ImplProofs.agda, th-prop-revoke-*): a SUCCESSFUL logout
	/// flips EXACTLY the session that was active for that token.  th-prop-revoke-logout
	/// pins that flip with inversion (session-at before sid ≡ active user forces
	/// session-at after sid ≡ revoked), and th-prop-revoke-rest pins every other section
	/// put for ANY derivation: all other sessions (sid ≢ other-sid) plus
	/// accounts/posts/follows/newest-first.
	/// The body's nw == want is the full seven-section world identity, and the used-id
	/// pair is IMPL-DEFINED, not spec-forced: the spec's logout Step constructor never
	/// mentions World.used-post-ids or World.used-session-ids in its premises, so those
	/// two sections are unconstrained on logout and their preservation is NOT derivable
	/// from an arbitrary derivation.  It is a property of OUR step (keyed session update,
	/// every other field carried), witnessed existentially by th-prop-revoke-used; see the
	/// matching spec-free caveat comment above that theorem.
	#[quickcheck]
	fn prop_revoke_token(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if let Some(sid) = as_revoke(cmd.clone()) {
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			if !valid_session(&w, sid) {
				return res == Result::Expired && nw == w;
			}
			let mut want: World = w;
			for e in &mut want.sessions {
				if e.0 == sid {
					e.1 = expected_revoke(e.1.clone());
				}
			}
			return res == Result::Success && nw == want;
		}
		true
	}

	/// QC of time-passes: every active session becomes revoked, nothing else changes.
	#[quickcheck]
	fn prop_time_passes(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if cmd == Command::TimePasses {
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			let mut want: World = w;
			for e in &mut want.sessions {
				e.1 = expected_revoke(e.1.clone());
			}
			return res == Result::Success && nw == want;
		}
		true
	}

	/// QC of follow-new: following records the pair for the session user.
	#[quickcheck]
	fn prop_follow(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if let Some((sid, user)) = as_follow(cmd.clone())
			&& let Some(u) = active_user(&w, sid)
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			return res == Result::Success && follows(&nw, &u, &user);
		}
		true
	}

	/// QC of like-denied: an unreadable post rejects likes without change.
	#[quickcheck]
	fn prop_like_denied(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if let Some((sid, pid)) = as_like(cmd.clone())
			&& valid_session(&w, sid)
			&& !can_read(&w, sid, pid)
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			return res == Result::Denied && nw == w;
		}
		true
	}

	/// QC of like-appends: a readable post gains the session user in its likes.
	#[quickcheck]
	fn prop_like_ok(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if let Some((sid, pid)) = as_like(cmd.clone())
			&& let Some(u) = active_user(&w, sid)
			&& can_read(&w, sid, pid)
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			let liked: bool = match post_at(&nw, pid) {
				Some(p) => member(&p.likes, u),
				None => false,
			};
			return res == Result::Success && liked;
		}
		true
	}

	/// QC of delete-author: an author may delete their post, and doing so twice leaves it deleted.
	#[quickcheck]
	fn prop_delete_author(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if let Some((sid, pid)) = as_delete(cmd.clone()) {
			match (active_user(&w, sid), post_at(&w, pid)) {
				(Some(user), Some(post)) => {
					if post.author == user {
						let (nw, res) = step(&w, cmd.clone(), ids.pid, ids.sid);
						let deleted: bool = match post_at(&nw, pid) {
							Some(p) => p.status == PostStatus::Deleted,
							None => false,
						};
						let (nw2, res2) = step(&nw, cmd, ids.pid, ids.sid);
						let still: bool = match post_at(&nw2, pid) {
							Some(p) => p.status == PostStatus::Deleted,
							None => false,
						};
						res == Result::Success && deleted && res2 == Result::Success && still
					} else {
						let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
						res == Result::Denied && nw == w
					}
				}
				_ => true,
			}
		} else {
			true
		}
	}

	/// QC of timeline-ids: timelines return unique, existing post ids of length at most n.
	#[quickcheck]
	fn prop_timeline_valid(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		let (nw, res) = step(&w, cmd.clone(), ids.pid, ids.sid);
		match cmd {
			Command::ReadPersonalTimeline(sid, n) => {
				if valid_session(&w, sid) {
					match res {
						Result::ReturnedTimeline(ts) => {
							ts.iter().all(|p| member(&w.newest_first, *p))
								&& unique(&ts) && len_u64(&ts) <= n
						}
						_ => false,
					}
				} else {
					res == Result::Expired && nw == w
				}
			}
			Command::ReadGlobalTimeline(msid, n) => match msid {
				None => match res {
					Result::ReturnedTimeline(ts) => {
						ts.iter().all(|p| member(&w.newest_first, *p))
							&& unique(&ts) && len_u64(&ts) <= n
							&& nw == w
					}
					_ => false,
				},
				Some(sid) => {
					if valid_session(&w, sid) {
						match res {
							Result::ReturnedTimeline(ts) => {
								ts.iter().all(|p| member(&w.newest_first, *p))
									&& unique(&ts) && len_u64(&ts) <= n
									&& nw == w
							}
							_ => false,
						}
					} else {
						res == Result::Expired && nw == w
					}
				}
			},
			_ => true,
		}
	}

	/// Pre-perf baseline (full filter, then take_n) pinning the hoisted/early-stopped timelines.
	fn old_global_timeline(w: &World, sid: u64, n: u64) -> Vec<u64> {
		let mut acc = vec![];
		for pid in &w.newest_first {
			if can_read(w, sid, *pid) {
				acc.push(*pid);
			}
		}
		take_n(acc, n)
	}

	/// Pre-perf baseline for the anonymous global timeline.
	fn old_public_timeline(w: &World, n: u64) -> Vec<u64> {
		let mut acc = vec![];
		for pid in &w.newest_first {
			if is_post_public(w, *pid) {
				acc.push(*pid);
			}
		}
		take_n(acc, n)
	}

	/// Pre-perf baseline for the personal timeline (owned active_user, per-candidate can_read).
	fn old_personal_timeline(w: &World, sid: u64, n: u64) -> Vec<u64> {
		match active_user(w, sid) {
			None => vec![],
			Some(user) => {
				let mut acc = vec![];
				for pid in &w.newest_first {
					if can_read(w, sid, *pid) && follows_author(w, &user, *pid) {
						acc.push(*pid);
					}
				}
				take_n(acc, n)
			}
		}
	}

	/// QC early-stop equivalence: hoisted global (logged-in + anon) timelines equal take_n of the full filter.
	#[quickcheck]
	fn prop_timeline_global_equiv(w: World, cmd: Command, ids: StepArgs) -> bool {
		// sid and n come from the Command generator pools (SIDS/NS) so the active-session
		// branch is exercised, not only the trivial no-session case.
		let sid: u64 = match extract_sid(cmd.clone()) {
			None => ids.sid,
			Some(s) => s,
		};
		let mut n: u64 = 3;
		if let Command::ReadGlobalTimeline(_, k) = cmd {
			n = k;
		}
		let mut ok: bool = true;
		for nn in &[n, 0, 1, 2, 1000] {
			ok = ok
				&& global_timeline(&w, sid, *nn) == old_global_timeline(&w, sid, *nn)
				&& public_timeline(&w, *nn) == old_public_timeline(&w, *nn);
		}
		ok
	}

	/// QC early-stop equivalence: hoisted personal (follows-based) timeline equals take_n of the full filter.
	#[quickcheck]
	fn prop_timeline_personal_equiv(w: World, cmd: Command, ids: StepArgs) -> bool {
		let sid: u64 = match extract_sid(cmd.clone()) {
			None => ids.sid,
			Some(s) => s,
		};
		let mut n: u64 = 3;
		if let Command::ReadPersonalTimeline(_, k) = cmd {
			n = k;
		}
		personal_timeline(&w, sid, n) == old_personal_timeline(&w, sid, n)
			&& personal_timeline(&w, sid, 0) == old_personal_timeline(&w, sid, 0)
			&& personal_timeline(&w, sid, 1) == old_personal_timeline(&w, sid, 1)
			&& personal_timeline(&w, sid, 2) == old_personal_timeline(&w, sid, 2)
			&& personal_timeline(&w, sid, 1000) == old_personal_timeline(&w, sid, 1000)
	}

	/// QC equivalence: every index-backed lookup agrees with the pure Vec scan, on present and absent keys alike.
	#[quickcheck]
	fn prop_ix_lookups_equiv(w: World, _cmd: Command, _ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		let ix: WorldIndex = build_index(&w);
		// pool keys plus one off-pool key each to exercise the absent branch
		let names: [String; 5] = [
			users_pool()[0].clone(),
			users_pool()[1].clone(),
			users_pool()[2].clone(),
			users_pool()[3].clone(),
			"zz".to_string(),
		];
		let sids: [u64; 5] = [SIDS[0], SIDS[1], SIDS[2], SIDS[3], 99];
		let pids: [u64; 6] = [PIDS[0], PIDS[1], PIDS[2], PIDS[3], PIDS[4], 99];
		let mut ok: bool = true;
		for u in &names {
			ok = ok && account_at(&w, u) == account_at_ix(&w, &ix, u);
		}
		for sid in &sids {
			ok = ok
				&& session_at(&w, *sid) == session_at_ix(&w, &ix, *sid)
				&& active_user(&w, *sid) == active_user_ix(&w, &ix, *sid);
		}
		for pid in &pids {
			ok = ok && post_at(&w, *pid) == post_at_ix(&w, &ix, *pid);
		}
		for f in &names {
			for g in &names {
				ok = ok && follows(&w, f, g) == follows_ix(&w, &ix, f, g);
			}
		}
		ok
	}

	/// QC equivalence: the index-backed predicates agree with the pure ones for in-pool and off-pool ids.
	#[quickcheck]
	fn prop_ix_predicates_equiv(w: World, cmd: Command, _ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		let ix: WorldIndex = build_index(&w);
		let sids: [u64; 5] = [SIDS[0], SIDS[1], SIDS[2], SIDS[3], 99];
		let pids: [u64; 6] = [PIDS[0], PIDS[1], PIDS[2], PIDS[3], PIDS[4], 99];
		let mut ok: bool = access_ok(&w, cmd.clone()) == access_ok_ix(&w, &ix, cmd);
		for sid in &sids {
			ok = ok && valid_session(&w, *sid) == valid_session_ix(&w, &ix, *sid);
		}
		for pid in &pids {
			ok = ok && is_post_public(&w, *pid) == is_post_public_ix(&w, &ix, *pid);
		}
		for sid in &sids {
			for pid in &pids {
				ok = ok && can_read(&w, *sid, *pid) == can_read_ix(&w, &ix, *sid, *pid);
			}
		}
		ok
	}

	/// QC by construction: build_index keeps the first occurrence, pinned by a literal world with a duplicated username.
	#[quickcheck]
	fn prop_ix_build_firstwins(_w: World, _cmd: Command, _ids: StepArgs) -> bool {
		// no well_formed guard: the tiny literal world is fixed and intentionally duplicated
		let mut w2: World = empty_world();
		w2.accounts.push((
			"dupe".to_string(),
			Account {
				password: "first".to_string(),
				default_visibility: Visibility::Everyone,
			},
		));
		w2.accounts.push((
			"dupe".to_string(),
			Account {
				password: "second".to_string(),
				default_visibility: Visibility::FollowersOnly,
			},
		));
		w2.sessions
			.push((7, SessionStatus::Active("dupe".to_string())));
		w2.posts.push((
			11,
			Post {
				author: "dupe".to_string(),
				text: "t".to_string(),
				visibility: Visibility::Everyone,
				status: PostStatus::Other,
				likes: vec![],
				replies: vec![],
				parent: None,
			},
		));
		w2.follows.push(("a".to_string(), "dupe".to_string()));
		w2.newest_first.push(11);
		w2.used_post_ids.push(11);
		w2.used_session_ids.push(7);
		let ix: WorldIndex = build_index(&w2);
		// first occurrence wins, so the first Account is what both the scan and the index yield
		account_at(&w2, "dupe") == account_at_ix(&w2, &ix, "dupe")
			&& post_at(&w2, 11) == post_at_ix(&w2, &ix, 11)
			&& session_at(&w2, 7) == session_at_ix(&w2, &ix, 7)
			&& follows(&w2, "a", "dupe") == follows_ix(&w2, &ix, "a", "dupe")
	}

	/// QC index equivalence: the hot-path global timeline through the side-index equals the pure-Vec reference.
	#[quickcheck]
	fn prop_timeline_global_ix(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		// sid and n come from the Command generator pools (SIDS/NS) so the active-session
		// branch is exercised, not only the trivial no-session case
		let sid: u64 = match extract_sid(cmd.clone()) {
			None => ids.sid,
			Some(s) => s,
		};
		let mut n: u64 = 3;
		if let Command::ReadGlobalTimeline(_, k) = cmd {
			n = k;
		}
		let ix: WorldIndex = build_index(&w);
		let mut ok: bool = true;
		for nn in &[n, 0, 1, 2, 1000] {
			ok = ok && global_timeline_ix(&w, &ix, sid, *nn) == global_timeline_ref(&w, sid, *nn);
		}
		ok
	}

	/// QC index equivalence: the hot-path personal timeline through the side-index equals the pure-Vec reference.
	#[quickcheck]
	fn prop_timeline_personal_ix(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		// same (sid, n) extraction as prop_timeline_personal_equiv
		let sid: u64 = match extract_sid(cmd.clone()) {
			None => ids.sid,
			Some(s) => s,
		};
		let mut n: u64 = 3;
		if let Command::ReadPersonalTimeline(_, k) = cmd {
			n = k;
		}
		let ix: WorldIndex = build_index(&w);
		personal_timeline_ix(&w, &ix, sid, n) == personal_timeline_ref(&w, sid, n)
			&& personal_timeline_ix(&w, &ix, sid, 0) == personal_timeline_ref(&w, sid, 0)
			&& personal_timeline_ix(&w, &ix, sid, 1) == personal_timeline_ref(&w, sid, 1)
			&& personal_timeline_ix(&w, &ix, sid, 2) == personal_timeline_ref(&w, sid, 2)
			&& personal_timeline_ix(&w, &ix, sid, 1000) == personal_timeline_ref(&w, sid, 1000)
	}

	/// QC index equivalence: the hot-path anonymous timeline through the side-index equals the pure-Vec reference.
	#[quickcheck]
	fn prop_timeline_public_ix(w: World, cmd: Command, _ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		let mut n: u64 = 3;
		if let Command::ReadGlobalTimeline(_, k) = cmd {
			n = k;
		}
		let ix: WorldIndex = build_index(&w);
		public_timeline_ix(&w, &ix, n) == public_timeline_ref(&w, n)
			&& public_timeline_ix(&w, &ix, 0) == public_timeline_ref(&w, 0)
			&& public_timeline_ix(&w, &ix, 1) == public_timeline_ref(&w, 1)
			&& public_timeline_ix(&w, &ix, 2) == public_timeline_ref(&w, 2)
			&& public_timeline_ix(&w, &ix, 1000) == public_timeline_ref(&w, 1000)
	}

	/// QC equivalence: step_ix driven with a fresh index agrees exactly with step, world and result alike.
	#[quickcheck]
	fn prop_step_ix_equiv(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		step_ix(&w, &build_index(&w), cmd.clone(), ids.pid, ids.sid)
			== step(&w, cmd, ids.pid, ids.sid)
	}

	// scale test: 800-post deterministic world, the index path must equal the pure-Vec reference
	#[test]
	fn test_timeline_index_scale() {
		let mut w: World = empty_world();
		// 40 accounts, usernames u0..u39
		for i in 0u64..40u64 {
			let name: String = format!("u{}", i);
			w.accounts.push((
				name,
				Account {
					password: "p".to_string(),
					default_visibility: Visibility::Everyone,
				},
			));
		}
		// sessions: sid 7 active for u3, sid 8 active for u11
		w.sessions
			.push((7, SessionStatus::Active("u3".to_string())));
		w.sessions
			.push((8, SessionStatus::Active("u11".to_string())));
		w.used_session_ids.push(7);
		w.used_session_ids.push(8);
		// follows: u3 follows u0..u19, u11 follows u5
		for j in 0u64..20u64 {
			w.follows.push(("u3".to_string(), format!("u{}", j)));
		}
		w.follows.push(("u11".to_string(), "u5".to_string()));
		// 800 posts: authors cycle the 40 usernames, visibility mixed, every 17th deleted
		for k in 0u64..800u64 {
			let pid: u64 = 100 + k;
			let author: String = format!("u{}", k % 40u64);
			let vis: Visibility = if k % 3u64 == 0 {
				Visibility::FollowersOnly
			} else {
				Visibility::Everyone
			};
			let st: PostStatus = if k % 17u64 == 0 {
				PostStatus::Deleted
			} else {
				PostStatus::Other
			};
			w.posts.push((
				pid,
				Post {
					author,
					text: "t".to_string(),
					visibility: vis,
					status: st,
					likes: vec![],
					replies: vec![],
					parent: None,
				},
			));
			w.newest_first.insert(0, pid);
			w.used_post_ids.push(pid);
		}
		let ix: WorldIndex = build_index(&w);
		// global: the delegator and the _ix twin must both equal the pure-Vec reference
		assert!(global_timeline(&w, 7, 50) == global_timeline_ref(&w, 7, 50));
		assert!(global_timeline_ix(&w, &ix, 7, 50) == global_timeline_ref(&w, 7, 50));
		// personal: u3 follows authors u0..u19; n=2000 exceeds the readable total
		assert!(personal_timeline(&w, 7, 5) == personal_timeline_ref(&w, 7, 5));
		assert!(personal_timeline(&w, 7, 2000) == personal_timeline_ref(&w, 7, 2000));
		assert!(personal_timeline_ix(&w, &ix, 7, 5) == personal_timeline_ref(&w, 7, 5));
		assert!(personal_timeline_ix(&w, &ix, 7, 2000) == personal_timeline_ref(&w, 7, 2000));
		// the anonymous session via sid 8 follows only u5
		assert!(personal_timeline(&w, 8, 2000) == personal_timeline_ref(&w, 8, 2000));
		assert!(personal_timeline_ix(&w, &ix, 8, 2000) == personal_timeline_ref(&w, 8, 2000));
		// public (anon global) too
		assert!(public_timeline(&w, 50) == public_timeline_ref(&w, 50));
		assert!(public_timeline_ix(&w, &ix, 50) == public_timeline_ref(&w, 50));
	}
	/// QC of delta-equivalence: step_d's result matches step's and patching step_d's effect payload into the world yields step's after-world.
	#[quickcheck]
	fn prop_delta_equiv(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		let (res, d): (Result, Delta) = step_d(&w, &build_index(&w), cmd.clone(), ids.pid, ids.sid);
		let (ref_after, ref_res): (World, Result) = step(&w, cmd, ids.pid, ids.sid);
		res == ref_res && patch_world(w.clone(), d) == ref_after
	}

	// Pin: Register's payload carries the Account (password + Everyone); patch lands exactly that one new account.
	#[test]
	fn test_delta_register() {
		let mut w: World = empty_world();
		// one existing account so the patched accounts must hold exactly two
		w.accounts.push((
			"b".to_string(),
			Account {
				password: "q".to_string(),
				default_visibility: Visibility::Everyone,
			},
		));
		let cmd: Command = Command::Register("a".to_string(), "s3cret".to_string());
		let (want, want_res) = step(&w, cmd.clone(), 7, 9);
		let (res, d) = step_d(&w, &build_index(&w), cmd.clone(), 7, 9);
		assert!(
			res == Result::Success && res == want_res && patch_world(w.clone(), d.clone()) == want
		);
		// payload pins the password and the default-Everyone visibility outright
		assert!(
			d == Delta::Register(
				"a".to_string(),
				Account {
					password: "s3cret".to_string(),
					default_visibility: Visibility::Everyone
				}
			)
		);
	}

	// Pin: Like's payload is (pid, user) and patch appends to that post's likes only.
	#[test]
	fn test_delta_like() {
		let mut w: World = empty_world();
		w.accounts.push((
			"a".to_string(),
			Account {
				password: "p".to_string(),
				default_visibility: Visibility::Everyone,
			},
		));
		w.sessions.push((1, SessionStatus::Active("a".to_string())));
		w.used_session_ids.push(1);
		w.posts.push((
			3,
			Post {
				author: "a".to_string(),
				text: "t".to_string(),
				visibility: Visibility::Everyone,
				status: PostStatus::Other,
				likes: vec![],
				replies: vec![],
				parent: None,
			},
		));
		w.newest_first.push(3);
		w.used_post_ids.push(3);
		let cmd: Command = Command::Like(1, 3);
		let (want, want_res) = step(&w, cmd.clone(), 7, 9);
		let (res, d) = step_d(&w, &build_index(&w), cmd.clone(), 7, 9);
		assert!(d == Delta::Like(3, "a".to_string()) && res == Result::Success && res == want_res);
		assert!(
			patch_world(w.clone(), d) == want
				&& post_at(&want, 3).unwrap().likes == vec!["a".to_string()]
		);
	}

	/// QC of read-post-logged-in (spec read-post-logged-in, Twitter.agda:540): a VALID session that
	/// passes CanReadPost -- can_read is exactly the spec's two CanReadPost constructors (post live AND
	/// (everyone OR followers-only AND the session user follows the author)) -- returns the STORED post
	/// unchanged: author, text, the like COUNT (len_u64, since Result's returned-post carries a Nat, not
	/// Post.likes) and the replies list verbatim; and the world is carried untouched (step's ReadPost arm
	/// clones w outright, model.rs:842).  th-prop-read-logged-in pins the same two asserts.
	#[quickcheck]
	fn prop_read_logged_in(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if let Some((Some(sid), pid)) = as_read(cmd.clone())
			&& valid_session(&w, sid)
			&& can_read(&w, sid, pid)
			&& let Some(post) = post_at_ref(&w, pid)
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			return res
				== Result::ReturnedPost(
					post.author.clone(),
					post.text.clone(),
					len_u64(&post.likes),
					post.replies.clone(),
				) && nw == w;
		}
		true
	}

	/// QC of read-post-anonymously (spec read-post-anonymously, Twitter.agda:550): with the NOTHING
	/// session token a LIVE Everyone post is returned in the very same ReturnedPost shape (author, text,
	/// like count, replies) and the world is untouched.  NOT asserted: an anonymous read of a private,
	/// deleted or missing post -- Twitter.agda has NO Step rule for it (read-post-anonymously needs
	/// everyone AND live, and there is no read-post nothing denied constructor), so the impl's Denied is
	/// impl-defined.  th-prop-read-public pins the shape plus after before.
	#[quickcheck]
	fn prop_read_public_shape(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if let Some((None, pid)) = as_read(cmd.clone())
			&& is_post_public(&w, pid)
			&& let Some(post) = post_at_ref(&w, pid)
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			return res
				== Result::ReturnedPost(
					post.author.clone(),
					post.text.clone(),
					len_u64(&post.likes),
					post.replies.clone(),
				) && nw == w;
		}
		true
	}

	/// QC of cant-read-post-public (spec name at Twitter.agda:518, the MISSING-post read): a VALID
	/// session reading an id with no post is Denied and the world is untouched.  th-prop-read-denied-missing
	/// pins result denied plus after before.
	#[quickcheck]
	fn prop_read_denied_missing(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if let Some((Some(sid), pid)) = as_read(cmd.clone())
			&& valid_session(&w, sid)
			&& post_at_ref(&w, pid).is_none()
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			return res == Result::Denied && nw == w;
		}
		true
	}

	/// QC of cant-read-post-private (spec Twitter.agda:524): a VALID session, a LIVE followers-only post
	/// whose author the session user does NOT follow -- CanReadPost's followers-only branch fails, so the
	/// read is Denied and the world is untouched.  th-prop-read-denied-private pins the same two asserts.
	#[quickcheck]
	fn prop_read_denied_private(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if let Some((Some(sid), pid)) = as_read(cmd.clone())
			&& valid_session(&w, sid)
			&& let Some(post) = post_at_ref(&w, pid)
			&& let Some(user) = active_user_ref(&w, sid)
			&& post.status == PostStatus::Other
			&& post.visibility == Visibility::FollowersOnly
			&& !follows(&w, user, &post.author)
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			return res == Result::Denied && nw == w;
		}
		true
	}

	/// QC of cant-read-post-private-deleted (spec Twitter.agda:533): a VALID session, a post at pid whose
	/// status is deleted (tombstone) -- no CanReadPost constructor accepts a deleted post, so Denied and
	/// the world is untouched.  th-prop-read-denied-deleted pins the same two asserts.
	#[quickcheck]
	fn prop_read_denied_deleted(w: World, cmd: Command, ids: StepArgs) -> bool {
		if !well_formed(&w) {
			return true;
		}
		if let Some((Some(sid), pid)) = as_read(cmd.clone())
			&& valid_session(&w, sid)
			&& let Some(post) = post_at_ref(&w, pid)
			&& post.status == PostStatus::Deleted
		{
			let (nw, res) = step(&w, cmd, ids.pid, ids.sid);
			return res == Result::Denied && nw == w;
		}
		true
	}
}
