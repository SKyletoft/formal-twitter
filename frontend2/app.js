'use strict';

// frontend2: the row-level controls (Like, author follow toggle) are per-tweet
// buttons inside each timeline row.
//
// NOTE: no wire endpoint can read follow state back — the protocol only has the
// write-side follow-user / unfollow-user commands. So the checkmark beside an
// author name is a client-side cache (Map username -> bool) that mirrors the
// database; the same goes for the liked-set deciding like-tweet vs unlike-tweet.

const TOKEN_KEY = 'formal-twitter-token';
const USER_KEY = 'formal-twitter-user';
const TIMELINE_LEN = 20;
const ENDPOINTS = [
  'login',
  'signup',
  'logout',
  'post-tweet',
  'global-timeline',
  'private-timeline',
  'get-tweet',
  'like-tweet',
  'unlike-tweet',
  'follow-user',
  'unfollow-user'
];

// Client-side caches of write-only state (see note above).
const likedIds = new Set();
const followState = new Map();

const el = (id) => document.getElementById(id);

function currentToken() {
  return localStorage.getItem(TOKEN_KEY);
}

function currentUser() {
  return localStorage.getItem(USER_KEY);
}

function setSession(token, user) {
  localStorage.setItem(TOKEN_KEY, token);
  localStorage.setItem(USER_KEY, user);
}

function clearSession() {
  localStorage.removeItem(TOKEN_KEY);
  localStorage.removeItem(USER_KEY);
}

let pending = null;

function parseResponse(text) {
  const s = String(text == null ? '' : text);
  try {
    return JSON.parse(s);
  } catch (e) {
    return byRegex(s);
  }
}

// Fallback for hand-written / single-quoted bodies: pull the fields by regex.
function byRegex(s) {
  const grab = (re) => {
    const m = s.match(re);
    return m ? m[1] : undefined;
  };
  const idList = (re) => {
    const raw = grab(re);
    return raw
      ? raw
        .split(',')
        .map((x) => parseInt(x.trim(), 10))
        .filter((n) => Number.isInteger(n) && n >= 0)
      : [];
  };
  const obj = {};
  const assign = (key, value) => {
    if (value !== undefined) obj[key] = value;
  };
  assign('username', grab(/["']username["']\s*:\s*["']([^"']*)["']/));
  assign('text', grab(/["']text["']\s*:\s*["']([\s\S]*?)["']\s*,\s*["']likes/));
  assign('likes', grab(/["']likes["']\s*:\s*(-?\d+)/));
  assign('session_token', grab(/["']session_token["']\s*:\s*["']?([^"',\s}]*)/));
  assign('tweet_id', grab(/["']tweet_id["']\s*:\s*["']?([^"',\s}]*)/));
  assign('error', grab(/["']error["']\s*:\s*["']([^"']*)["']/));
  obj.timeline = idList(/["']timeline["']\s*:\s*\[([^\[\]]*)\]/);
  obj.replies = idList(/["']replies["']\s*:\s*\[([^\[\]]*)\]/);
  return obj;
}

function cleanText(s) {
  return String(s == null ? '' : s).replace(/[\r\n]/g, '');
}

// to-request of spec/Interface.agda: token first, CRLF between lines, no
// trailing newline. Anonymous get-tweet / global-timeline send a single line.
function buildLines(kind, args, token) {
  if (kind === 'login' || kind === 'signup') {
    return [args.username, args.password];
  }
  if (kind === 'post-tweet') {
    return [token || '', cleanText(args.text)];
  }
  if (kind === 'like-tweet' || kind === 'unlike-tweet') {
    return [token || '', String(args.id)];
  }
  if (kind === 'follow-user' || kind === 'unfollow-user') {
    return [token || '', args.username];
  }
  if (kind === 'logout') {
    return [token || ''];
  }
  if (kind === 'get-tweet') {
    return token ? [token, String(args.id)] : [String(args.id)];
  }
  if (kind === 'global-timeline') {
    return token ? [token, String(args.len)] : [String(args.len)];
  }
  if (kind === 'private-timeline') {
    return [token || '', String(args.len)];
  }
  return [];
}

function wireBody(kind, args, token) {
  return buildLines(kind, args, token).join('\r\n');
}

async function performAction(kind, args, opts) {
  if (!ENDPOINTS.includes(kind)) {
    return { error: 'network-error', message: 'Unknown action' };
  }
  const authAction = kind === 'login' || kind === 'signup';
  const token = authAction ? null : currentToken();
  let response;
  try {
    response = await fetch('/api/' + kind, {
      method: 'POST',
      headers: { 'Content-Type': 'text/plain' },
      body: wireBody(kind, args, token)
    });
  } catch (e) {
    return { error: 'network-error', message: 'Could not reach the server' };
  }
  const text = await response.text();
  const data = parseResponse(text);
  if (response.status === 401) {
    if (authAction) {
      return {
        error: 'auth-failed',
        message: kind === 'login' ? 'Wrong username or password' : 'That username is already taken'
      };
    }
    if (opts.replaying) {
      return { error: 'session-expired', message: 'Session expired again \u2014 please log in' };
    }
    clearSession();
    if (opts.via) {
      pending = { kind: kind, args: args, opts: opts, via: opts.via };
    }
    showAuth('Your session has expired \u2014 please log in again.');
    return { error: 'session-expired', handled: true };
  }
  if (response.status !== 200) {
    const name = data && data.error ? data.error : response.statusText;
    return {
      error: 'request-failed',
      status: response.status,
      message: kind === 'signup' && response.status === 400
        ? 'That username is already taken'
        : kind === 'get-tweet' && response.status === 403 ? 'Not allowed to view this post' : (name || 'Unexpected response')
    };
  }
  return { status: 200, data: data || {} };
}

function showAuth(noticeText) {
  el('auth-panel').hidden = false;
  el('app-panel').hidden = true;
  el('logout-btn').hidden = true;
  el('session-status').textContent = 'Logged out';
  el('auth-notice').textContent = noticeText || '';
  loadPublicTimeline();
}

function showApp() {
  el('auth-panel').hidden = true;
  el('app-panel').hidden = false;
  el('logout-btn').hidden = false;
  el('session-status').textContent =
    'Logged in as ' + currentUser() + ' (token #' + currentToken() + ')';
  refreshTimelines();
}

async function afterAuthVisitor() {
  showApp();
  const p = pending;
  pending = null;
  if (p && typeof p.via === 'function' && !p.replayed) {
    p.replayed = true;
    const result = await performAction(p.kind, p.args, Object.assign({}, p.opts, { replaying: true }));
    p.via(result);
  }
}

function renderTimeline(listId, errorId, result) {
  const listEl = el(listId);
  const errEl = el(errorId);
  if (result.error) {
    listEl.textContent = '';
    errEl.textContent = result.message;
    return;
  }
  errEl.textContent = '';
  renderTweetRows(listEl, result.data.timeline);
}

async function loadPublicTimeline() {
  const result = await performAction('global-timeline', { len: TIMELINE_LEN }, {});
  renderTimeline('public-list', 'public-error', result);
}

// Both timelines are fetched in parallel and re-rendered together, so private
// and global panels stay side by side after login/post/like/follow actions.
async function refreshTimelines() {
  if (!currentToken()) {
    return loadPublicTimeline();
  }
  const priv = performAction('private-timeline', { len: TIMELINE_LEN }, {});
  const glob = performAction('global-timeline', { len: TIMELINE_LEN }, {});
  const both = await Promise.all([priv, glob]);
  renderTimeline('private-list', 'private-error', both[0]);
  renderTimeline('global-list', 'global-error', both[1]);
}

function renderTweetRows(listEl, ids) {
  listEl.textContent = '';
  const items = Array.isArray(ids) ? ids : [];
  if (!items.length) {
    const empty = document.createElement('li');
    empty.className = 'muted';
    empty.textContent = 'Nothing here yet.';
    listEl.appendChild(empty);
    return;
  }
  for (const id of items) {
    appendTweetRow(listEl, id);
  }
}

// One row: [#id open] [Like] [@author ✓?] [text snippet] [likes].
function appendTweetRow(listEl, id) {
  const li = document.createElement('li');

  const openBtn = document.createElement('button');
  openBtn.type = 'button';
  openBtn.className = 'row-open';
  openBtn.textContent = '#' + id;
  openBtn.addEventListener('click', () => hydrateRow(id, (data) => fillRow(li, authorBtn, rowName, data), null));

  const likeBtn = document.createElement('button');
  likeBtn.type = 'button';
  likeBtn.className = likedIds.has(id) ? 'row-like liked' : 'row-like';
  likeBtn.textContent = 'Like';
  likeBtn.addEventListener('click', async () => {
    if (!currentToken()) return;
    const wasLiked = likedIds.has(id);
    const kind = wasLiked ? 'unlike-tweet' : 'like-tweet';
    const result = await performAction(kind, { id: id }, {});
    if (result.handled || result.error) return;
    if (wasLiked) {
      likedIds.delete(id);
      likeBtn.classList.remove('liked');
    } else {
      likedIds.add(id);
      likeBtn.classList.add('liked');
    }
    refreshTimelines();
  });

  const rowName = { name: null };
  const authorBtn = document.createElement('button');
  authorBtn.type = 'button';
  authorBtn.className = 'row-author';
  authorBtn.textContent = '@ ?';
  authorBtn.addEventListener('click', async () => {
    if (!rowName.name || !currentToken()) return;
    const followed = followState.get(rowName.name) === true;
    const kind = followed ? 'unfollow-user' : 'follow-user';
    const result = await performAction(kind, { username: authorName }, {});
    if (result.handled || result.error) return;
    followState.set(rowName.name, !followed);
    authorBtn.textContent = '@' + rowName.name + (followed ? '' : ' \u2713');
    refreshTimelines();
  });

  const textSpan = document.createElement('span');
  textSpan.className = 'row-text';
  textSpan.textContent = '\u2026';

  const likesSpan = document.createElement('span');
  likesSpan.className = 'row-likes';

  li.appendChild(openBtn);
  li.appendChild(likeBtn);
  li.appendChild(authorBtn);
  li.appendChild(textSpan);
  li.appendChild(likesSpan);
  listEl.appendChild(li);

  hydrateRow(id, (data) => fillRow(li, authorBtn, rowName, data), () => {
    li.classList.add('muted');
    textSpan.textContent = '';
    likesSpan.textContent = '';
  });
}

function hydrateRow(id, onOk, onBad) {
  performAction('get-tweet', { id: id }, {}).then((result) => {
    if (result.handled) return;
    if (result.error) {
      if (onBad) onBad();
      return;
    }
    onOk(result.data || {});
  });
}

// Hydrate from the database: author name, text preview, like count.
function fillRow(li, authorBtn, rowName, data) {
  const name = data.username == null ? '?' : String(data.username);
  rowName.name = name;
  authorBtn.textContent = '@' + name + (followState.get(name) === true ? ' \u2713' : '');
  const text = String(data.text == null ? '' : data.text).replace(/\s+/g, ' ');
  const snippet = text.length > 80 ? text.slice(0, 80) + '\u2026' : text;
  const first = li.querySelector('span.row-text');
  if (first) first.textContent = snippet;
  const likes = parseInt(String(data.likes == null ? '0' : data.likes), 10) || 0;
  const likesEl = li.querySelector('span.row-likes');
  if (likesEl) likesEl.textContent = likes + (likes === 1 ? ' like' : ' likes');
  li.classList.remove('muted');
}

el('login-form').addEventListener('submit', async (ev) => {
  ev.preventDefault();
  const username = el('login-username').value.trim();
  const password = el('login-password').value;
  el('login-error').textContent = '';
  const result = await performAction('login', { username: username, password: password }, {});
  if (result.status === 200 && result.data && result.data.session_token != null) {
    setSession(String(result.data.session_token), username);
    await afterAuthVisitor();
  } else {
    el('login-error').textContent = result.message || 'Unexpected response';
  }
});

el('signup-form').addEventListener('submit', async (ev) => {
  ev.preventDefault();
  const username = el('signup-username').value.trim();
  const password = el('signup-password').value;
  el('signup-error').textContent = '';
  const result = await performAction('signup', { username: username, password: password }, {});
  if (result.status === 200 && result.data && result.data.session_token != null) {
    setSession(String(result.data.session_token), username);
    await afterAuthVisitor();
  } else {
    // 400 signup_failed: friendly wording, per spec the server only says signup_failed.
    el('signup-error').textContent = result.message || 'That username is already taken';
  }
});

el('compose-text').addEventListener('keydown', (ev) => {
  if (ev.key === 'Enter' && (ev.ctrlKey || ev.metaKey)) {
    ev.preventDefault();
    el('compose-form').requestSubmit();
  }
});

// ok is an empty 200 body, so the pinned confirmation comes from tweet_id.
el('compose-form').addEventListener('submit', async (ev) => {
  ev.preventDefault();
  const text = el('compose-text').value;
  el('compose-error').textContent = '';
  el('compose-ok').textContent = '';
  const via = (result) => {
    if (result.handled) return;
    if (result.error) {
      el('compose-error').textContent = result.message;
      return;
    }
    if (result.data && result.data.tweet_id != null) {
      el('compose-ok').textContent = 'Posted as #' + result.data.tweet_id;
      el('compose-text').value = '';
      refreshTimelines();
      return;
    }
    el('compose-error').textContent = 'Unexpected response';
  };
  const result = await performAction('post-tweet', { text: text }, { via: via });
  via(result);
});

el('logout-btn').addEventListener('click', async () => {
  await performAction('logout', {}, {});
  clearSession();
  pending = null;
  likedIds.clear();
  followState.clear();
  showAuth('');
});

function start() {
  if (currentToken()) {
    showApp();
  } else {
    clearSession();
    showAuth('');
  }
}

start();
