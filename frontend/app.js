'use strict';

(function () {
	const TOKEN_KEY = 'formal-twitter.session-token';

	const ERROR_TEXT = {
		access_denied: 'access denied: you are not allowed to do that',
		session_expired: 'your session has expired, please log in again',
		login_failed: 'login failed: wrong username or password',
		signup_failed: 'signup failed: that username is already taken'
	};

	let token = loadToken();
	const logList = document.getElementById('log');
	const sessionState = document.getElementById('session-state');

	/* ---------- response log ---------- */

	function log(kind, message) {
		const entry = document.createElement('li');
		entry.className = 'entry ' + kind;
		const stamp = document.createElement('span');
		stamp.className = 'stamp';
		stamp.textContent = new Date().toLocaleTimeString();
		const body = document.createElement('span');
		body.className = 'message';
		body.textContent = message;
		entry.appendChild(stamp);
		entry.appendChild(body);
		logList.appendChild(entry);
		logList.scrollTop = logList.scrollHeight;
	}

	function ok(message) {
		log('ok', message);
	}

	function failure(message) {
		log('error', message);
	}

	function info(message) {
		log('info', message);
	}

	/* ---------- session token ---------- */

	function isNat(value) {
		return typeof value === 'string' && /^[0-9]+$/.test(value);
	}

	function loadToken() {
		let stored = null;
		try {
			stored = window.localStorage.getItem(TOKEN_KEY);
		} catch (e) {
			return null;
		}
		return isNat(stored) ? stored : null;
	}

	function setToken(value) {
		token = isNat(value) ? value : null;
		try {
			if (token === null) {
				window.localStorage.removeItem(TOKEN_KEY);
			} else {
				window.localStorage.setItem(TOKEN_KEY, token);
			}
		} catch (e) {
			/* storage unavailable: the in-memory token still works */
		}
		refreshSession();
	}

	function refreshSession() {
		sessionState.textContent = token === null ? 'logged out' : 'logged in, token ' + token;
		const guarded = document.querySelectorAll('[data-needs-token]');
		for (let i = 0; i < guarded.length; i += 1) {
			guarded[i].disabled = token === null;
		}
	}

	/* ---------- transport ---------- */

	async function api(name, fields) {
		const response = await fetch('/api/' + name, {
			method: 'POST',
			headers: { 'Content-Type': 'text/plain; charset=utf-8' },
			body: fields.join('\r\n') + '\r\n'
		});
		const text = await response.text();
		let json = null;
		if (text.trim() !== '') {
			try {
				json = JSON.parse(text);
			} catch (e) {
				json = null;
			}
		}
		return { status: response.status, text: text, json: json };
	}

	function errorNameOf(result) {
		if (result.json === null || typeof result.json !== 'object') {
			return null;
		}
		return typeof result.json.error === 'string' ? result.json.error : null;
	}

	async function call(label, name, fields) {
		let result;
		try {
			result = await api(name, fields);
		} catch (e) {
			failure(label + ' failed: could not reach the server (' + describe(e) + ')');
			return null;
		}
		const problem = errorNameOf(result);
		if (problem !== null) {
			if (problem === 'session_expired') {
				setToken(null);
			}
			const message = ERROR_TEXT[problem] || 'request rejected (' + problem + ')';
			failure(label + ': ' + message + ' [HTTP ' + result.status + ']');
			return null;
		}
		if (result.status !== 200) {
			failure(label + ' failed: HTTP ' + result.status + (result.text === '' ? '' : ': ' + result.text));
			return null;
		}
		return result;
	}

	function describe(e) {
		return e instanceof Error ? e.message : String(e);
	}

	function fieldValue(result, key) {
		if (result.json === null || typeof result.json !== 'object') {
			return null;
		}
		const value = result.json[key];
		return value === undefined || value === null ? null : String(value);
	}

	/* ---------- input validation ---------- */

	function readTweetId(label, fieldId) {
		const raw = String(document.getElementById(fieldId).value).trim();
		if (!/^[0-9]+$/.test(raw)) {
			failure(label + ': "' + raw + '" is not a tweet id (expected a number)');
			return null;
		}
		return raw.replace(/^0+(?=[0-9])/, '');
	}

	function readSingleLine(label, fieldId, what) {
		const value = document.getElementById(fieldId).value;
		if (value === '') {
			failure(label + ': please enter ' + what);
			return null;
		}
		if (/[\r\n]/.test(value)) {
			failure(label + ': ' + what + ' must be one line, line breaks cannot be sent');
			return null;
		}
		return value;
	}

	function haveToken(label) {
		if (token === null) {
			failure(label + ': you are logged out, log in first');
			return false;
		}
		return true;
	}

	/* ---------- wiring ---------- */

	function onSubmit(formId, handler) {
		const form = document.getElementById(formId);
		form.addEventListener('submit', function (event) {
			event.preventDefault();
			handler();
		});
	}

	onSubmit('signup-form', async function () {
		const username = readSingleLine('Signup', 'signup-username', 'a username');
		if (username === null) {
			return;
		}
		const password = readSingleLine('Signup', 'signup-password', 'a password');
		if (password === null) {
			return;
		}
		const result = await call('Signup', 'signup', [username, password]);
		if (result === null) {
			return;
		}
		ok('Signup: account ' + JSON.stringify(username) + ' created, please log in');
		document.getElementById('signup-form').reset();
	});

	onSubmit('login-form', async function () {
		const username = readSingleLine('Login', 'login-username', 'a username');
		if (username === null) {
			return;
		}
		const password = readSingleLine('Login', 'login-password', 'a password');
		if (password === null) {
			return;
		}
		const result = await call('Login', 'login', [username, password]);
		if (result === null) {
			return;
		}
		const issued = fieldValue(result, 'session_token');
		if (!isNat(issued)) {
			failure('Login: the server did not return a session token (' + result.text + ')');
			return;
		}
		setToken(issued);
		ok('Login: logged in as ' + JSON.stringify(username) + ', session token ' + issued);
		document.getElementById('login-form').reset();
	});

	document.getElementById('logout-button').addEventListener('click', async function () {
		if (token === null) {
			failure('Logout: you are already logged out');
			return;
		}
		const result = await call('Logout', 'logout', [token]);
		if (result !== null) {
			setToken(null);
			ok('Logout: session token revoked');
		} else if (token === null) {
			info('Logout: local session token cleared');
		}
	});

	onSubmit('post-tweet-form', async function () {
		if (!haveToken('Post tweet')) {
			return;
		}
		const text = readSingleLine('Post tweet', 'post-text', 'some text');
		if (text === null) {
			return;
		}
		const result = await call('Post tweet', 'post-tweet', [token, text]);
		if (result === null) {
			return;
		}
		const id = fieldValue(result, 'tweet_id');
		ok('Post tweet: stored' + (id === null ? '' : ' as tweet ' + id));
		document.getElementById('post-tweet-form').reset();
	});

	onSubmit('post-reply-form', async function () {
		if (!haveToken('Reply')) {
			return;
		}
		const text = readSingleLine('Reply', 'reply-text', 'some text');
		if (text === null) {
			return;
		}
		const parent = readTweetId('Reply', 'reply-id');
		if (parent === null) {
			return;
		}
		const result = await call('Reply', 'post-reply', [token, text, parent]);
		if (result === null) {
			return;
		}
		const id = fieldValue(result, 'tweet_id');
		ok('Reply: reply to tweet ' + parent + (id === null ? ' stored' : ' stored as tweet ' + id));
		document.getElementById('post-reply-form').reset();
	});

	function idAction(formId, label, endpoint, fieldId) {
		onSubmit(formId, async function () {
			if (!haveToken(label)) {
				return;
			}
			const id = readTweetId(label, fieldId);
			if (id === null) {
				return;
			}
			const result = await call(label, endpoint, [token, id]);
			if (result === null) {
				return;
			}
			ok(label + ': tweet ' + id + ' (ok)');
			document.getElementById(formId).reset();
		});
	}

	idAction('delete-tweet-form', 'Delete tweet', 'delete-tweet', 'delete-id');
	idAction('like-form', 'Like', 'like-tweet', 'like-id');
	idAction('unlike-form', 'Unlike', 'unlike-tweet', 'unlike-id');

	function userAction(formId, label, endpoint, fieldId) {
		onSubmit(formId, async function () {
			if (!haveToken(label)) {
				return;
			}
			const username = readSingleLine(label, fieldId, 'a username');
			if (username === null) {
				return;
			}
			const result = await call(label, endpoint, [token, username]);
			if (result === null) {
				return;
			}
			ok(label + ': ' + JSON.stringify(username) + ' (ok)');
			document.getElementById(formId).reset();
		});
	}

	userAction('follow-form', 'Follow', 'follow-user', 'follow-username');
	userAction('unfollow-form', 'Unfollow', 'unfollow-user', 'unfollow-username');

	function textOf(value) {
		return value === undefined || value === null ? '(unknown)' : String(value);
	}

	function showTweet(id, result) {
		const tweet = result.json;
		if (tweet === null || typeof tweet !== 'object' || Array.isArray(tweet)) {
			info('Get tweet: tweet ' + id + ' returned an unexpected body ' + JSON.stringify(result.text));
			return;
		}
		const replies = Array.isArray(tweet.replies) ? tweet.replies.map(String) : [];
		const lines = [
			'tweet ' + id + ' by ' + textOf(tweet.username),
			textOf(tweet.text),
			'likes: ' + textOf(tweet.likes),
			'replies: ' + (replies.length === 0 ? '(none)' : replies.join(', '))
		];
		ok('Get tweet:\n' + lines.join('\n'));
	}

	onSubmit('get-tweet-form', async function () {
		const id = readTweetId('Get tweet', 'get-id');
		if (id === null) {
			return;
		}
		const fields = token === null ? [id] : [token, id];
		const result = await call('Get tweet', 'get-tweet', fields);
		if (result === null) {
			return;
		}
		showTweet(id, result);
	});

	document.getElementById('clear-log').addEventListener('click', function () {
		while (logList.firstChild !== null) {
			logList.removeChild(logList.firstChild);
		}
	});

	refreshSession();
	info('Ready. Nothing is loaded automatically, every request is listed here.');
})();
