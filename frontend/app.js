'use strict';

/* Formal Twitter: browse the timelines, then post, reply, like, follow and
   delete through the thirteen `/api` endpoints of the spec. Every node is
   built with createElement/textContent; no markup is ever parsed from data,
   and URLs only ever carry numeric ids. */

(function () {
	const TOKEN_KEY = 'formal-twitter.session-token';
	const USER_KEY = 'formal-twitter.username';
	const PAGE_SIZE = '20';
	const MAX_IN_FLIGHT = 6;
	const MAX_DETAIL_REPLIES = 20;
	const MAX_LOG_ENTRIES = 50;

	const ERROR_TEXT = {
		access_denied: 'access denied: you may not view that',
		session_expired: 'your session expired, please log in again',
		login_failed: 'wrong username or password',
		signup_failed: 'that username is already taken',
		bad_request: 'the server rejected the request',
		internal: 'the server hit an internal error'
	};

	/* ---------- elements ---------- */

	function byId(id) {
		return document.getElementById(id);
	}

	const authForm = byId('auth-form');
	const usernameField = byId('username');
	const passwordField = byId('password');
	const loginButton = byId('login-button');
	const signupButton = byId('signup-button');
	const signedIn = byId('signed-in');
	const sessionUsername = byId('session-username');
	const logoutButton = byId('logout-button');
	const tabGlobal = byId('tab-global');
	const tabFollowing = byId('tab-following');
	const followingHint = byId('following-hint');
	const banner = byId('banner');
	const timelineView = byId('timeline-view');
	const timelineHeading = byId('timeline-heading');
	const timelineStatus = byId('timeline-status');
	const timelineList = byId('timeline');
	const composerForm = byId('composer');
	const postText = byId('post-text');
	const postButton = byId('post-button');
	const postStatus = byId('post-status');
	const detailView = byId('detail-view');
	const detailBack = byId('detail-back');
	const detailStatus = byId('detail-status');
	const detailTweet = byId('detail-tweet');
	const replyForm = byId('reply-composer');
	const replyText = byId('reply-text');
	const replyButton = byId('reply-button');
	const replyStatus = byId('reply-status');
	const detailReplies = byId('detail-replies');
	const repliesNote = byId('replies-note');
	const logList = byId('log');
	const logCount = byId('log-count');

	/* ---------- session ---------- */

	let token = null;
	let username = null;
	let bannerTimer = 0;
	let routeSeq = 0;
	let lastTimeline = 'global';
	/* Set once a reply has said the session expired, so a batch of in-flight
	   requests reports it exactly once. */
	let sessionExpiring = false;
	/* The API has no "did I like this" or "do I follow this" query, so both
	   are remembered only for actions taken in this tab: they are cleared on
	   login, logout and session expiry, and never claim to be the server's
	   state. */
	const likedIds = new Set();
	const followedUsers = new Set();
	/* One post or reply in flight at a time: the composers disable their
	   button and ignore a second submit until the first answers. */
	let posting = false;
	let replying = false;

	function isNat(value) {
		return typeof value === 'string' && /^[0-9]+$/.test(value);
	}

	function readStorage(key) {
		try {
			return window.localStorage.getItem(key);
		} catch (error) {
			return null;
		}
	}

	function writeStorage(key, value) {
		try {
			if (value === null) {
				window.localStorage.removeItem(key);
			} else {
				window.localStorage.setItem(key, value);
			}
		} catch (error) {
			/* storage unavailable: the in-memory session still works */
		}
	}

	function loadSession() {
		const storedToken = readStorage(TOKEN_KEY);
		const storedUser = readStorage(USER_KEY);
		if (isNat(storedToken) && typeof storedUser === 'string' && storedUser !== '') {
			token = storedToken;
			username = storedUser;
			return;
		}
		/* A token without a username (or the other way round) is not usable. */
		token = null;
		username = null;
		writeStorage(TOKEN_KEY, null);
		writeStorage(USER_KEY, null);
	}

	function setSession(newToken, newUsername) {
		sessionExpiring = false;
		if (isNat(newToken) && typeof newUsername === 'string' && newUsername !== '') {
			token = newToken;
			username = newUsername;
		} else {
			token = null;
			username = null;
		}
		writeStorage(TOKEN_KEY, token);
		writeStorage(USER_KEY, username);
		/* Likes and follows are per-session guesses; a new session starts
		   from nothing rather than from the previous account's clicks. */
		likedIds.clear();
		followedUsers.clear();
		refreshSessionUi();
	}

	function clearSession() {
		token = null;
		username = null;
		writeStorage(TOKEN_KEY, null);
		writeStorage(USER_KEY, null);
		likedIds.clear();
		followedUsers.clear();
		postText.value = '';
		replyText.value = '';
		postStatus.textContent = '';
		replyStatus.textContent = '';
		refreshSessionUi();
	}

	function isLoggedIn() {
		return token !== null && username !== null;
	}

	function refreshSessionUi() {
		const loggedIn = token !== null && username !== null;
		authForm.hidden = loggedIn;
		signedIn.hidden = !loggedIn;
		sessionUsername.textContent = loggedIn ? '@' + username : '@';
		followingHint.hidden = loggedIn;
		composerForm.hidden = !loggedIn;
		replyForm.hidden = !loggedIn;
		if (loggedIn) {
			tabFollowing.removeAttribute('aria-disabled');
			tabFollowing.removeAttribute('tabindex');
		} else {
			/* Disabled here: keep it out of the tab order as well, so keyboard
			   users are not sent to a link that only explains itself. */
			tabFollowing.setAttribute('aria-disabled', 'true');
			tabFollowing.setAttribute('tabindex', '-1');
		}
	}

	/* ---------- activity log and banner ---------- */

	function log(kind, message) {
		const entry = document.createElement('li');
		entry.className = kind;
		entry.textContent = new Date().toLocaleTimeString() + '  ' + message;
		logList.appendChild(entry);
		if (logList.children.length > MAX_LOG_ENTRIES) {
			logList.removeChild(logList.firstChild);
		}
		logCount.textContent = String(logList.children.length);
		logList.scrollTop = logList.scrollHeight;
	}

	function setBanner(text) {
		banner.textContent = text;
		banner.hidden = false;
		if (bannerTimer !== 0) {
			window.clearTimeout(bannerTimer);
		}
		bannerTimer = window.setTimeout(function () {
			banner.hidden = true;
		}, 12000);
	}

	/* ---------- transport ---------- */

	function describe(error) {
		return error instanceof Error ? error.message : String(error);
	}

	function errorName(json) {
		if (json === null || typeof json !== 'object') {
			return null;
		}
		return typeof json.error === 'string' ? json.error : null;
	}

	function errorMessage(name) {
		if (name === null) {
			return 'the request failed';
		}
		if (name === 'session_expired' && token === null) {
			return 'that tweet is not available (missing or deleted)';
		}
		return ERROR_TEXT[name] || 'rejected (' + name + ')';
	}

	function textField(json, key) {
		if (json === null || typeof json !== 'object') {
			return null;
		}
		const value = json[key];
		return typeof value === 'string' || typeof value === 'number' ? String(value) : null;
	}

	async function call(name, fields) {
		let response;
		try {
			response = await fetch('/api/' + name, {
				method: 'POST',
				headers: {
					Accept: 'application/json',
					'Content-Type': 'text/plain; charset=utf-8'
				},
				body: fields.join('\r\n') + '\r\n'
			});
		} catch (error) {
			log('error', name + ': could not reach the server (' + describe(error) + ')');
			return { ok: false, status: 0, error: null, json: null };
		}

		let text = '';
		try {
			text = await response.text();
		} catch (error) {
			text = '';
		}
		let json = null;
		if (text.trim() !== '') {
			try {
				json = JSON.parse(text);
			} catch (error) {
				json = null;
			}
		}

		const error = errorName(json);
		if (error === 'session_expired' && sessionExpiring) {
			/* The rest of an in-flight batch: the banner and the fallback render
			   already happened once, so stay silent. */
			return { ok: false, status: response.status, error: error, json: json };
		}
		if (error === 'session_expired' && token !== null) {
			sessionExpiring = true;
			log('error', name + ': your session expired');
			expireSession();
			return { ok: false, status: response.status, error: error, json: json };
		}
		if (error !== null) {
			log('error', name + ': ' + errorMessage(error) + ' [HTTP ' + response.status + ']');
			return { ok: false, status: response.status, error: error, json: json };
		}
		if (response.status !== 200) {
			const detail = text.trim() === '' ? '' : ' ' + text.trim().slice(0, 200);
			log('error', name + ': HTTP ' + response.status + detail);
			return { ok: false, status: response.status, error: null, json: json };
		}
		return { ok: true, status: response.status, error: null, json: json };
	}

	function withToken(fields) {
		return token === null ? fields : [token].concat(fields);
	}

	/* ---------- routing ---------- */

	function currentRoute() {
		const hash = window.location.hash;
		if (hash === '' || hash === '#' || hash === '#/') {
			return { name: 'global' };
		}
		if (hash === '#/following') {
			return { name: 'following' };
		}
		const match = /^#\/tweet\/([0-9]+)$/.exec(hash);
		if (match !== null) {
			return { name: 'tweet', id: match[1] };
		}
		return { name: 'global', invalid: true };
	}

	function markTabs(kind) {
		const tabs = [[tabGlobal, 'global'], [tabFollowing, 'following']];
		for (let i = 0; i < tabs.length; i += 1) {
			if (tabs[i][1] === kind) {
				tabs[i][0].setAttribute('aria-current', 'page');
			} else {
				tabs[i][0].removeAttribute('aria-current');
			}
		}
	}

	function expireSession() {
		clearSession();
		setBanner('Your session expired, so you were logged out.');
		if (currentRoute().name !== 'global') {
			window.history.replaceState(null, '', '#/');
		}
		renderRoute();
	}

	function renderRoute() {
		const seq = routeSeq + 1;
		routeSeq = seq;
		let route = currentRoute();
		if (route.invalid) {
			window.history.replaceState(null, '', '#/');
			route = { name: 'global' };
		}
		if (route.name === 'following' && token === null) {
			setBanner('Log in to see the following timeline.');
			window.history.replaceState(null, '', '#/');
			route = { name: 'global' };
		}
		if (route.name === 'tweet') {
			showDetail(route.id, seq);
			return;
		}
		lastTimeline = route.name;
		showTimeline(route.name, seq);
	}

	function showTimeline(kind, seq) {
		timelineView.hidden = false;
		detailView.hidden = true;
		timelineHeading.textContent = kind === 'following' ? 'Following' : 'Global';
		markTabs(kind);
		timelineList.replaceChildren();
		detailTweet.replaceChildren();
		detailReplies.replaceChildren();
		detailStatus.textContent = '';
		repliesNote.textContent = '';
		replyStatus.textContent = '';
		/* "Posted tweet #n." belongs to the view it was written in. */
		postStatus.textContent = '';
		timelineStatus.textContent = 'Loading timeline…';
		loadTimeline(kind, seq);
	}

	function showDetail(id, seq) {
		timelineView.hidden = true;
		detailView.hidden = false;
		markTabs(lastTimeline);
		detailBack.href = lastTimeline === 'following' ? '#/following' : '#/';
		detailBack.textContent = '← Back to ' + (lastTimeline === 'following' ? 'Following' : 'Global');
		timelineList.replaceChildren();
		detailTweet.replaceChildren();
		detailReplies.replaceChildren();
		repliesNote.textContent = '';
		replyStatus.textContent = '';
		detailStatus.textContent = 'Loading tweet ' + id + '…';
		loadDetail(id, seq);
	}

	/* ---------- parsing ---------- */

	/* A tweet id as the API writes it: an unquoted Nat. Numeric strings are
	   accepted too, but always normalised to digits without leading zeros. */
	function idOf(raw) {
		if (typeof raw === 'number') {
			return Number.isSafeInteger(raw) && raw >= 0 ? String(raw) : null;
		}
		if (typeof raw === 'string' && /^[0-9]+$/.test(raw)) {
			return raw.replace(/^0+(?=[0-9])/, '');
		}
		return null;
	}

	/* True when `raw` is a JSON number `JSON.parse` had to round: anything above
	   2^53 - 1 is no longer the server's id. The backend draws ids from
	   1..=2^53 - 1, so this only fires if that contract is ever broken. */
	function idOutOfRange(raw) {
		return typeof raw === 'number' && !(Number.isSafeInteger(raw) && raw >= 0);
	}

	/* Ids of a `show-tweets` list, in order. A number the browser cannot hold
	   exactly becomes `null`, which renders as an "unsupported id" placeholder
	   instead of a request for a tweet the server does not have; an entry that
	   is not an id at all makes the whole list `null`. */
	function idsOf(raw) {
		if (!Array.isArray(raw)) {
			return null;
		}
		const ids = [];
		for (let i = 0; i < raw.length; i += 1) {
			const id = idOf(raw[i]);
			if (id === null && !idOutOfRange(raw[i])) {
				return null;
			}
			ids.push(id);
		}
		return ids;
	}

	function parseTweet(json) {
		if (json === null || typeof json !== 'object') {
			return null;
		}
		if (typeof json.username !== 'string' || typeof json.text !== 'string') {
			return null;
		}
		if (!Number.isSafeInteger(json.likes) || json.likes < 0) {
			return null;
		}
		const replies = idsOf(json.replies);
		if (replies === null) {
			return null;
		}
		return { username: json.username, text: json.text, likes: json.likes, replies: replies };
	}

	function timelineIds(json) {
		if (json === null || typeof json !== 'object') {
			return null;
		}
		return idsOf(json.timeline);
	}

	/* ---------- bounded concurrency ---------- */

	/* Resolves with one result per item, never rejecting: a rejected worker
	   promise yields `null` at that position. At most `limit` workers run. */
	function mapLimit(items, limit, worker) {
		return new Promise(function (resolve) {
			const results = new Array(items.length);
			let next = 0;
			let active = 0;
			let finished = 0;
			if (items.length === 0) {
				resolve(results);
				return;
			}
			function settle(index, value) {
				results[index] = value;
				active -= 1;
				finished += 1;
				if (finished === items.length) {
					resolve(results);
					return;
				}
				start();
			}
			function start() {
				while (active < limit && next < items.length) {
					const index = next;
					next += 1;
					active += 1;
					Promise.resolve()
						.then(function () {
							return worker(items[index]);
						})
						.then(
							function (value) {
								settle(index, value);
							},
							function () {
								settle(index, null);
							}
						);
				}
			}
			start();
		});
	}

	async function fetchTweet(id) {
		if (id === null) {
			return { id: null, tweet: null };
		}
		const result = await call('get-tweet', withToken([id]));
		if (!result.ok) {
			return { id: id, tweet: null };
		}
		return { id: id, tweet: parseTweet(result.json) };
	}

	/* ---------- rendering ---------- */

	function metric(text) {
		const node = document.createElement('span');
		node.className = 'metric';
		node.textContent = text;
		return node;
	}

	function likeText(count) {
		return '♥ ' + count + (count === 1 ? ' like' : ' likes');
	}

	function replyCountText(count) {
		return '↩ ' + count + (count === 1 ? ' reply' : ' replies');
	}

	/* ---------- action buttons ---------- */

	/* A card's inline message: a refusal that is not the session ending. The
	   activity log keeps the wire-level detail. */
	function note(card, text) {
		card.note.textContent = text;
		card.note.hidden = text === '';
	}

	function button(label, className) {
		const node = document.createElement('button');
		node.type = 'button';
		node.className = className;
		node.textContent = label;
		return node;
	}

	/* Disabled exactly when the session is gone or the button is mid-request;
	   the title says which while the session is what is missing. */
	function syncAction(node, hint) {
		const busy = node.dataset.busy === '1';
		const loggedIn = isLoggedIn();
		node.disabled = busy || !loggedIn;
		if (loggedIn) {
			node.removeAttribute('title');
		} else {
			node.title = hint;
		}
	}

	function setBusy(node, busy, hint) {
		if (busy) {
			node.dataset.busy = '1';
		} else {
			delete node.dataset.busy;
		}
		syncAction(node, hint);
	}

	/* `aria-pressed` and the visible label both follow the local set; the
	   title states that the set is this tab's memory, not the server's. */
	function paintLike(node, id) {
		const liked = likedIds.has(id);
		node.textContent = liked ? 'Unlike' : 'Like';
		node.setAttribute('aria-pressed', liked ? 'true' : 'false');
		node.setAttribute('aria-label', (liked ? 'Unlike tweet #' : 'Like tweet #') + id);
		syncAction(node, 'log in to like tweets');
		if (isLoggedIn()) {
			node.title = 'Liked here in this tab; the API does not report your likes back';
		}
	}

	function paintFollow(node, name) {
		const following = followedUsers.has(name);
		node.textContent = following ? 'Unfollow' : 'Follow';
		node.setAttribute('aria-pressed', following ? 'true' : 'false');
		node.setAttribute('aria-label', (following ? 'Unfollow @' : 'Follow @') + name);
		syncAction(node, 'log in to follow users');
		if (isLoggedIn()) {
			node.title = 'Followed here in this tab; the API does not report who you follow';
		}
	}

	function buildCard(id, tweet) {
		const card = document.createElement('article');
		card.className = 'tweet-card';

		const head = document.createElement('div');
		head.className = 'tweet-head';
		const author = document.createElement('a');
		author.className = 'tweet-author';
		author.href = '#/tweet/' + id;
		author.textContent = '@' + tweet.username;
		const follow = button('Follow', 'action follow-toggle');
		follow.addEventListener('click', function () {
			toggleFollow(tweet.username, follow, card);
		});
		paintFollow(follow, tweet.username);
		const stamp = document.createElement('span');
		stamp.className = 'tweet-id';
		stamp.textContent = '#' + id;
		head.appendChild(author);
		head.appendChild(follow);
		head.appendChild(stamp);

		const text = document.createElement('p');
		text.className = 'tweet-text';
		text.textContent = tweet.text;

		const meta = document.createElement('div');
		meta.className = 'tweet-meta';
		const like = button('Like', 'action like-toggle');
		const likes = metric(likeText(tweet.likes));
		like.addEventListener('click', function () {
			toggleLike(id, like, likes, card);
		});
		paintLike(like, id);
		const replyCount = tweet.replies.length;
		meta.appendChild(like);
		meta.appendChild(likes);
		meta.appendChild(metric(replyCountText(replyCount)));
		const open = document.createElement('a');
		open.href = '#/tweet/' + id;
		open.textContent = 'Open thread';
		meta.appendChild(open);

		const actions = document.createElement('div');
		actions.className = 'tweet-actions';
		if (username !== null && tweet.username === username) {
			const remove = button('Delete', 'action danger');
			remove.setAttribute('aria-label', 'Delete tweet #' + id);
			remove.addEventListener('click', function () {
				deleteTweet(id, remove, card);
			});
			actions.appendChild(remove);
		}

		const noteNode = document.createElement('p');
		noteNode.className = 'tweet-note';
		noteNode.hidden = true;
		noteNode.setAttribute('role', 'status');
		card.note = noteNode;

		card.appendChild(head);
		card.appendChild(text);
		card.appendChild(meta);
		card.appendChild(actions);
		card.appendChild(noteNode);
		return card;
	}

	function unavailable(text) {
		const node = document.createElement('p');
		node.className = 'tweet-unavailable';
		node.textContent = text;
		return node;
	}

	function listItems(ids, items) {
		const nodes = [];
		let missing = 0;
		let unsupported = 0;
		for (let i = 0; i < ids.length; i += 1) {
			const id = ids[i];
			const listItem = document.createElement('li');
			listItem.className = 'tweet-item';
			if (id === null) {
				unsupported += 1;
				listItem.appendChild(unavailable('unsupported id: this browser cannot hold it exactly'));
				nodes.push(listItem);
				continue;
			}
			listItem.dataset.tweetId = id;
			const item = items[i];
			if (item === null || item === undefined || item.tweet === null) {
				missing += 1;
				listItem.appendChild(unavailable('tweet ' + id + ' unavailable'));
			} else {
				listItem.appendChild(buildCard(id, item.tweet));
			}
			nodes.push(listItem);
		}
		return { nodes: nodes, missing: missing, unsupported: unsupported };
	}

	/* ---------- timelines ---------- */

	async function loadTimeline(kind, seq) {
		const name = kind === 'following' ? 'private-timeline' : 'global-timeline';
		const result = await call(name, withToken([PAGE_SIZE]));
		if (seq !== routeSeq) {
			return;
		}
		if (!result.ok) {
			timelineStatus.textContent = 'Could not load the timeline (HTTP ' + result.status + ').';
			return;
		}
		const ids = timelineIds(result.json);
		if (ids === null) {
			timelineStatus.textContent = 'The server sent an unexpected timeline.';
			return;
		}
		if (ids.length === 0) {
			timelineStatus.textContent = 'No tweets yet.';
			return;
		}
		timelineStatus.textContent = 'Loading ' + ids.length + (ids.length === 1 ? ' tweet…' : ' tweets…');
		const items = await mapLimit(ids, MAX_IN_FLIGHT, fetchTweet);
		if (seq !== routeSeq) {
			return;
		}
		const rendered = listItems(ids, items);
		timelineList.replaceChildren.apply(timelineList, rendered.nodes);
		let summary = ids.length + (ids.length === 1 ? ' tweet' : ' tweets');
		if (rendered.missing > 0) {
			summary += ', ' + rendered.missing + ' unavailable';
		}
		if (rendered.unsupported > 0) {
			summary += ', ' + rendered.unsupported + ' unsupported id' +
				(rendered.unsupported === 1 ? '' : 's');
		}
		timelineStatus.textContent = summary;
	}

	/* The wording under the reply list: how many replies exist, how many are
	   shown, and how many of the shown ones could not be rendered. The
	   truncation notice never swallows the unavailable count. */
	function replySummary(total, shownCount, rendered) {
		let note = total > shownCount
			? 'Showing ' + shownCount + ' of ' + total + ' replies'
			: total + (total === 1 ? ' reply' : ' replies');
		if (rendered.missing > 0) {
			note += ', ' + rendered.missing + ' unavailable';
		}
		if (rendered.unsupported > 0) {
			note += ', ' + rendered.unsupported + ' unsupported id' +
				(rendered.unsupported === 1 ? '' : 's');
		}
		return total > shownCount ? note + '.' : note;
	}

	function detailErrorMessage(result) {
		if (result.status === 403) {
			return 'This tweet is not available: it may have been deleted, or you may not be allowed to view it.';
		}
		if (result.status === 401) {
			return 'This tweet is not available: it may have been deleted.';
		}
		if (result.status === 0) {
			return 'Could not load this tweet: the server is unreachable.';
		}
		return 'Could not load this tweet (HTTP ' + result.status + ').';
	}

	async function loadDetail(id, seq) {
		const result = await call('get-tweet', withToken([id]));
		if (seq !== routeSeq) {
			return;
		}
		if (!result.ok) {
			detailStatus.textContent = detailErrorMessage(result);
			repliesNote.textContent = '';
			return;
		}
		const tweet = parseTweet(result.json);
		if (tweet === null) {
			detailStatus.textContent = 'The server sent an unexpected tweet.';
			return;
		}
		detailStatus.textContent = '';
		detailTweet.replaceChildren(buildCard(id, tweet));

		const total = tweet.replies.length;
		if (total === 0) {
			repliesNote.textContent = 'No replies yet.';
			return;
		}
		const shown = tweet.replies.slice(0, MAX_DETAIL_REPLIES);
		repliesNote.textContent = 'Loading ' + shown.length + (shown.length === 1 ? ' reply…' : ' replies…');
		const items = await mapLimit(shown, MAX_IN_FLIGHT, fetchTweet);
		if (seq !== routeSeq) {
			return;
		}
		const rendered = listItems(shown, items);
		detailReplies.replaceChildren.apply(detailReplies, rendered.nodes);
		repliesNote.textContent = replySummary(total, shown.length, rendered);
	}

	/* ---------- actions ---------- */

	/* The wording of a refusal that is not the session ending (that one has
	   already been handled by `call`). */
	function failureText(result, forbidden) {
		if (result.status === 403) {
			return forbidden;
		}
		if (result.status === 401) {
			return 'Your session ended, so nothing changed.';
		}
		if (result.status === 0) {
			return 'Could not reach the server.';
		}
		return 'The request failed (HTTP ' + result.status + ').';
	}

	/* Like and unlike are one toggle: the local set decides the endpoint, and
	   only the tweet's own like count is fetched again afterwards. A refusal
	   puts the button back; likes are idempotent, so a retry is safe. */
	async function toggleLike(id, node, countNode, card) {
		if (!isLoggedIn() || node.dataset.busy === '1') {
			return;
		}
		const wasLiked = likedIds.has(id);
		const endpoint = wasLiked ? 'unlike-tweet' : 'like-tweet';
		if (wasLiked) {
			likedIds.delete(id);
		} else {
			likedIds.add(id);
		}
		paintLike(node, id);
		setBusy(node, true, 'log in to like tweets');
		try {
			const result = await call(endpoint, [token, id]);
			if (!result.ok) {
				/* Only revert while the session that clicked is still the one
				   in hand: expiry has already dropped the whole set. */
				if (isLoggedIn()) {
					if (wasLiked) {
						likedIds.add(id);
					} else {
						likedIds.delete(id);
					}
					paintLike(node, id);
					note(card, failureText(
						result,
						'You may not ' + (wasLiked ? 'unlike' : 'like') + ' that tweet.'
					));
				}
				return;
			}
			const fresh = await fetchTweet(id);
			if (fresh.tweet !== null) {
				countNode.textContent = likeText(fresh.tweet.likes);
			}
			/* A previous refusal on this card no longer applies. */
			note(card, '');
		} finally {
			setBusy(node, false, 'log in to like tweets');
		}
	}

	/* Follow and unfollow are one toggle as well. A success refreshes the
	   active view: following changes which private posts are readable, so
	   the tweets already on screen may be stale or newly hidden. The refetch
	   is bounded (one page, at most 20 tweets) and the sequence guard there
	   discards a slower earlier render. */
	async function toggleFollow(name, node, card) {
		if (!isLoggedIn() || node.dataset.busy === '1') {
			return;
		}
		const wasFollowing = followedUsers.has(name);
		const endpoint = wasFollowing ? 'unfollow-user' : 'follow-user';
		if (wasFollowing) {
			followedUsers.delete(name);
		} else {
			followedUsers.add(name);
		}
		paintFollow(node, name);
		setBusy(node, true, 'log in to follow users');
		try {
			const result = await call(endpoint, [token, name]);
			if (!result.ok) {
				if (isLoggedIn()) {
					if (wasFollowing) {
						followedUsers.add(name);
					} else {
						followedUsers.delete(name);
					}
					paintFollow(node, name);
					note(card, failureText(
						result,
						'You may not ' + (wasFollowing ? 'unfollow' : 'follow') + ' that user.'
					));
				}
				return;
			}
			log('ok', (wasFollowing ? 'unfollowed @' : 'followed @') + name);
			renderRoute();
		} finally {
			setBusy(node, false, 'log in to follow users');
		}
	}

	/* Delete appears only on the session's own tweets. In a thread it returns
	   to the timeline; in a timeline the view is fetched again without it. */
	async function deleteTweet(id, node, card) {
		if (!isLoggedIn() || node.dataset.busy === '1') {
			return;
		}
		if (!window.confirm('Delete tweet #' + id + '? This cannot be undone.')) {
			return;
		}
		setBusy(node, true, 'log in to delete tweets');
		try {
			const result = await call('delete-tweet', [token, id]);
			if (!result.ok) {
				note(card, failureText(result, 'You can only delete your own tweets.'));
				return;
			}
			likedIds.delete(id);
			log('ok', 'deleted tweet #' + id);
			/* Only the thread's own tweet disappears with the thread; a deleted
			   reply simply leaves the thread to be fetched again. */
			if (currentRoute().name === 'tweet' && currentRoute().id === id) {
				window.location.hash = lastTimeline === 'following' ? '#/following' : '#/';
				/* Without a hashchange event (a stub page) the render is done
				   here instead; in a browser it already happened. */
				if (currentRoute().name === 'tweet') {
					renderRoute();
				}
				return;
			}
			renderRoute();
		} finally {
			setBusy(node, false, 'log in to delete tweets');
		}
	}

	/* ---------- composers ---------- */

	function setComposerBusy(form, busy) {
		const button = form === composerForm ? postButton : replyButton;
		button.disabled = busy;
		if (form === composerForm) {
			posting = busy;
		} else {
			replying = busy;
		}
	}

	/* A tweet and its text: the body is `<token>\r\n<text>\r\n`, so the text
	   must not carry a line break of its own. */
	function singleLine(form, text) {
		if (!/[\r\n]/.test(text)) {
			return true;
		}
		const status = form === composerForm ? postStatus : replyStatus;
		status.textContent = 'Only one line is allowed: the API takes the text as a single field.';
		return false;
	}

	async function submitPost() {
		if (posting || !isLoggedIn()) {
			return;
		}
		const text = postText.value;
		if (!singleLine(composerForm, text)) {
			return;
		}
		setComposerBusy(composerForm, true);
		try {
			const result = await call('post-tweet', [token, text]);
			if (!result.ok) {
				postStatus.textContent = failureText(result, 'You may not post.');
				return;
			}
			const created = idOf(textField(result.json, 'tweet_id'));
			postText.value = '';
			log('ok', created === null ? 'posted a tweet' : 'posted tweet #' + created);
			renderRoute();
			postStatus.textContent = created === null ? 'Posted.' : 'Posted tweet #' + created + '.';
		} finally {
			setComposerBusy(composerForm, false);
		}
	}

	async function submitReply(parentId) {
		if (replying || !isLoggedIn() || !isNat(parentId)) {
			return;
		}
		const text = replyText.value;
		if (!singleLine(replyForm, text)) {
			return;
		}
		setComposerBusy(replyForm, true);
		try {
			const result = await call('post-reply', [token, text, parentId]);
			if (!result.ok) {
				replyStatus.textContent = failureText(result, 'You may not reply to that tweet.');
				return;
			}
			const created = idOf(textField(result.json, 'tweet_id'));
			replyText.value = '';
			log('ok', created === null ? 'posted a reply' : 'replied with tweet #' + created);
			renderRoute();
			replyStatus.textContent = 'Reply posted.';
		} finally {
			setComposerBusy(replyForm, false);
		}
	}

	/* ---------- authentication ---------- */

	function setAuthBusy(busy) {
		loginButton.disabled = busy;
		signupButton.disabled = busy;
	}

	async function authenticate(mode) {
		const user = usernameField.value;
		const password = passwordField.value;
		if (user === '' || password === '') {
			setBanner('Enter a username and a password.');
			return;
		}
		if (/[\r\n]/.test(user) || /[\r\n]/.test(password)) {
			setBanner('Usernames and passwords cannot contain line breaks.');
			return;
		}

		setAuthBusy(true);
		try {
			if (mode === 'signup') {
				const signup = await call('signup', [user, password]);
				if (!signup.ok) {
					setBanner(signup.error === 'signup_failed'
						? 'Sign up failed: that username is already taken.'
						: 'Sign up failed.');
					return;
				}
				log('ok', 'signed up as ' + user);
			}

			const result = await call('login', [user, password]);
			if (!result.ok) {
				setBanner(result.error === 'login_failed'
					? 'Login failed: wrong username or password.'
					: 'Login failed.');
				return;
			}
			const issued = textField(result.json, 'session_token');
			if (!isNat(issued)) {
				setBanner('Login failed: the server sent no session token.');
				log('error', 'login: malformed response');
				return;
			}
			setSession(issued, user);
			passwordField.value = '';
			setBanner('Logged in as @' + user + '.');
			log('ok', 'logged in as ' + user);
			renderRoute();
		} finally {
			setAuthBusy(false);
		}
	}

	async function logOut() {
		const previous = token;
		logoutButton.disabled = true;
		try {
			if (previous !== null) {
				const result = await call('logout', [previous]);
				if (result.ok) {
					log('ok', 'logged out');
				}
			}
		} finally {
			logoutButton.disabled = false;
			clearSession();
			passwordField.value = '';
			setBanner('Logged out.');
			renderRoute();
		}
	}

	/* ---------- wiring ---------- */

	authForm.addEventListener('submit', function (event) {
		event.preventDefault();
		const submitter = event.submitter;
		const signup = submitter !== null && submitter !== undefined && submitter.id === 'signup-button';
		authenticate(signup ? 'signup' : 'login');
	});

	logoutButton.addEventListener('click', logOut);

	composerForm.addEventListener('submit', function (event) {
		event.preventDefault();
		if (currentRoute().name === 'tweet') {
			return;
		}
		submitPost();
	});

	replyForm.addEventListener('submit', function (event) {
		event.preventDefault();
		const route = currentRoute();
		if (route.name !== 'tweet') {
			return;
		}
		submitReply(route.id);
	});

	tabFollowing.addEventListener('click', function (event) {
		if (token === null) {
			event.preventDefault();
			setBanner('Log in to see the following timeline.');
		}
	});

	window.addEventListener('hashchange', renderRoute);

	loadSession();
	refreshSessionUi();
	renderRoute();
}());
