//! Pure model mirroring spec/Twitter.agda: World, Command, Result, Step.

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

/// Spec helper: unique keys in an association list.
pub fn key_unique<K: PartialEq + Clone, V>(xs: &[(K, V)]) -> bool {
	let keys: Vec<K> = (xs.iter()).map(|(key, _)| key.clone()).collect();
	unique(&keys)
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

/// World.session-at; absence means Unused.
pub fn session_at(w: &World, sid: u64) -> SessionStatus {
	for (s, st) in w.sessions.iter() {
		if *s == sid {
			return st.clone();
		}
	}
	SessionStatus::Unused
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

/// World.follows; absence means false.
pub fn follows(w: &World, follower: &str, followee: &str) -> bool {
	for (f, g) in w.follows.iter() {
		if *f == follower && *g == followee {
			return true;
		}
	}
	false
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

/// Spec can-have-valid-session: sid is active for a user with an account.
pub fn valid_session(w: &World, sid: u64) -> bool {
	match active_user(w, sid) {
		None => false,
		Some(user) => account_at(w, &user).is_some(),
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

/// Spec is-post-public: exists with Everyone visibility and live status.
pub fn is_post_public(w: &World, pid: u64) -> bool {
	match post_at_ref(w, pid) {
		None => false,
		Some(post) => post.visibility == Visibility::Everyone && post.status == PostStatus::Other,
	}
}

/// Spec follows-post-author: user follows the author of pid.
pub fn follows_author(w: &World, user: &str, pid: u64) -> bool {
	match post_at_ref(w, pid) {
		None => false,
		Some(post) => follows(w, user, &post.author),
	}
}

/// Data.List.take on Vec.
pub fn take_n(xs: Vec<u64>, n: u64) -> Vec<u64> {
	// take stops at the iterator end, so n beyond the length yields all, as before
	// (usize is 64-bit here, so the n cast is exact)
	(xs.iter()).take(n as usize).copied().collect()
}

/// get-personal-timeline: newest-first, keep readable posts by followed authors.
pub fn personal_timeline(w: &World, sid: u64, n: u64) -> Vec<u64> {
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

/// get-private-global: newest-first readable posts.
pub fn global_timeline(w: &World, sid: u64, n: u64) -> Vec<u64> {
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

/// get-public-global: newest-first public posts.
pub fn public_timeline(w: &World, n: u64) -> Vec<u64> {
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

/// Deterministic Step: (before, cmd, fresh ids) -> (after, result). Failed-access is checked first.
pub fn step(w: &World, cmd: Command, fresh_pid: u64, fresh_sid: u64) -> (World, Result) {
	let expired: bool = match extract_sid(cmd.clone()) {
		Some(sid) => !valid_session(w, sid),
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
			let user = active_user(w, sid).unwrap();
			let acc = account_at(w, &user);
			let mut vis: Visibility = Visibility::Everyone;
			if let Some(a) = acc {
				vis = a.default_visibility;
			}
			let readable: bool = match parent {
				Some(ppid) => can_read(w, sid, ppid),
				None => true,
			};
			if !readable {
				return (w.clone(), Result::Denied);
			}
			let parent_vis: Option<Visibility> = match parent {
				Some(ppid) => match post_at(w, ppid) {
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
			(nw, Result::CreatedPost(fresh_pid))
		}
		Command::Delete(sid, pid) => {
			let user = active_user(w, sid).unwrap();
			match post_at(w, pid) {
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
				None => is_post_public(w, pid),
				Some(sid) => can_read(w, sid, pid),
			};
			if !readable {
				return (w.clone(), Result::Denied);
			}
			match post_at(w, pid) {
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
			Result::ReturnedTimeline(personal_timeline(w, sid, n)),
		),
		Command::ReadGlobalTimeline(msid, n) => {
			let ids: Vec<u64> = match msid {
				None => public_timeline(w, n),
				Some(sid) => global_timeline(w, sid, n),
			};
			(w.clone(), Result::ReturnedTimeline(ids))
		}
		Command::Authenticate(user, passwd) => {
			let issued: bool = match account_at(w, &user) {
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
			if account_at(w, &user).is_some() {
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
			let user = active_user(w, sid).unwrap();
			if follows(w, &user, &followee) {
				(w.clone(), Result::Success)
			} else {
				let mut nw = w.clone();
				nw.follows.push((user, followee));
				(nw, Result::Success)
			}
		}
		Command::Unfollow(sid, followee) => {
			let user = active_user(w, sid).unwrap();
			let mut nw = w.clone();
			// (in-place retain drops the exact pair, no rebuild, no clones)
			nw.follows.retain(|(f, g)| *f != user || *g != followee);
			(nw, Result::Success)
		}
		Command::Like(sid, pid) => {
			if !can_read(w, sid, pid) {
				return (w.clone(), Result::Denied);
			}
			let user = active_user(w, sid).unwrap();
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
			if !can_read(w, sid, pid) {
				return (w.clone(), Result::Denied);
			}
			let user = active_user(w, sid).unwrap();
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
#[cfg(test)]
mod qc {
	use super::{
		Account, Command, Post, PostStatus, Result, SessionStatus, Visibility, World, account_at,
		active_user, can_read, empty_world, extract_sid, follows, follows_author, global_timeline,
		is_post_public, len_u64, member, personal_timeline, post_at, public_timeline, step, take_n,
		unique, valid_session, well_formed,
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
		let mut parents: Vec<(u64, Option<u64>)> = vec![];
		for pid in PIDS {
			if pick(g, &[true, true, false]) {
				let us: [String; 4] = users_pool();
				let author: String = pick(g, &us);
				let vis: Visibility = pick(g, &VIS);
				let status: PostStatus = pick(g, &STA);
				let parent: Option<u64> = if parents.is_empty() || !coin(g) {
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
				5u64 => Command::Authenticate(user, "p".to_string()),
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

	/// QC of revoke-token: only the named session changes, and only to Revoked.
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
}
