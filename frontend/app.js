'use strict';

/* Formal Twitter, browsing only: no posting, liking, following or deleting.
   Every node is built with createElement/textContent; no markup is ever
   parsed from data, and URLs only ever carry numeric ids. */

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
	const detailView = byId('detail-view');
	const detailBack = byId('detail-back');
	const detailStatus = byId('detail-status');
	const detailTweet = byId('detail-tweet');
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
		if (isNat(newToken) && typeof newUsername === 'string' && newUsername !== '') {
			token = newToken;
			username = newUsername;
		} else {
			token = null;
			username = null;
		}
		writeStorage(TOKEN_KEY, token);
		writeStorage(USER_KEY, username);
		refreshSessionUi();
	}

	function clearSession() {
		token = null;
		username = null;
		writeStorage(TOKEN_KEY, null);
		writeStorage(USER_KEY, null);
		refreshSessionUi();
	}

	function refreshSessionUi() {
		const loggedIn = token !== null && username !== null;
		authForm.hidden = loggedIn;
		signedIn.hidden = !loggedIn;
		sessionUsername.textContent = loggedIn ? '@' + username : '@';
		followingHint.hidden = loggedIn;
		if (loggedIn) {
			tabFollowing.removeAttribute('aria-disabled');
		} else {
			tabFollowing.setAttribute('aria-disabled', 'true');
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
		if (error === 'session_expired' && token !== null) {
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

	function idsOf(raw) {
		if (!Array.isArray(raw)) {
			return null;
		}
		const ids = [];
		for (let i = 0; i < raw.length; i += 1) {
			const id = idOf(raw[i]);
			if (id === null) {
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

	function buildCard(id, tweet) {
		const card = document.createElement('article');
		card.className = 'tweet-card';

		const head = document.createElement('div');
		head.className = 'tweet-head';
		const author = document.createElement('a');
		author.className = 'tweet-author';
		author.href = '#/tweet/' + id;
		author.textContent = '@' + tweet.username;
		const stamp = document.createElement('span');
		stamp.className = 'tweet-id';
		stamp.textContent = '#' + id;
		head.appendChild(author);
		head.appendChild(stamp);

		const text = document.createElement('p');
		text.className = 'tweet-text';
		text.textContent = tweet.text;

		const meta = document.createElement('div');
		meta.className = 'tweet-meta';
		meta.appendChild(metric('♥ ' + tweet.likes + (tweet.likes === 1 ? ' like' : ' likes')));
		const replyCount = tweet.replies.length;
		meta.appendChild(metric('↩ ' + replyCount + (replyCount === 1 ? ' reply' : ' replies')));
		const open = document.createElement('a');
		open.href = '#/tweet/' + id;
		open.textContent = 'Open thread';
		meta.appendChild(open);

		card.appendChild(head);
		card.appendChild(text);
		card.appendChild(meta);
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
		for (let i = 0; i < ids.length; i += 1) {
			const item = items[i];
			const listItem = document.createElement('li');
			listItem.className = 'tweet-item';
			listItem.dataset.tweetId = ids[i];
			if (item === null || item === undefined || item.tweet === null) {
				missing += 1;
				listItem.appendChild(unavailable('tweet ' + ids[i] + ' unavailable'));
			} else {
				listItem.appendChild(buildCard(ids[i], item.tweet));
			}
			nodes.push(listItem);
		}
		return { nodes: nodes, missing: missing };
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
		timelineStatus.textContent = summary;
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
		if (total > shown.length) {
			repliesNote.textContent = 'Showing ' + shown.length + ' of ' + total + ' replies.';
		} else if (rendered.missing > 0) {
			repliesNote.textContent = total + (total === 1 ? ' reply' : ' replies') + ', ' + rendered.missing + ' unavailable';
		} else {
			repliesNote.textContent = total + (total === 1 ? ' reply' : ' replies');
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
