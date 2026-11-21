'use strict';

/*
 * frontend4/app.js — broadsheet (two-column newspaper) client.
 *
 * Fixed wire protocol, one shape only:
 *   POST /api/<name>, Content-Type: text/plain,
 *   body = CRLF-joined lines, the token FIRST, NO trailing newline.
 *     login / signup      [username, password]
 *     logout              [token]
 *     post-tweet          [token, text]
 *     global-timeline     anon = [len]            authed = [token, len]
 *     private-timeline    [token, len]
 *     get-tweet           anon = [id]             authed = [token, id]
 *     like-tweet/unlike-tweet      [token, id]
 *     follow-user/unfollow-user    [token, username]
 *   Responses: 200 with an EMPTY body (Content-Length: 0) is the ok verdict;
 *   200 otherwise carries {"tweet_id":"N"} / {"session_token":"N"} /
 *   {"timeline":[...]}; 403 access_denied, 401 session_expired/login_failed,
 *   400 signup_failed.
 *
 * NOTE: the wire has NO read-endpoint for follow state (follow-user and
 * unfollow-user only write, nothing queries "who do I follow"), so the
 * ' ✓' suffix on an author button is a client-side Map name -> bool held in
 * this tab.  It caches a decision we made, never a fact read back from the
 * DB, and it is dropped on logout.  The liked set is client-side for the same
 * reason: there is no "is this liked by me" read either.
 */

const TOKEN_KEY = 'formal-twitter-token';
const USER_KEY = 'formal-twitter-user';
const TIMELINE_LEN = 12;
const LINE_SEP = '\r\n';
const CHECK = ' \u2713';
const DASH = ' \u2014 ';

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

const el = (id) => document.getElementById(id);

function currentToken() {
  return localStorage.getItem(TOKEN_KEY);
}

function currentUser() {
  return localStorage.getItem(USER_KEY);
}

function setSession(token, user) {
  localStorage.setItem(TOKEN_KEY, String(token));
  localStorage.setItem(USER_KEY, String(user));
}

function clearSession() {
  localStorage.removeItem(TOKEN_KEY);
  localStorage.removeItem(USER_KEY);
}

function signedIn() {
  const t = currentToken();
  return t !== null && t !== '';
}

/* Follow + like state: client-side only, see the NOTE above. */
const followed = new Map();
const liked = new Set();
let sessionGone = false;

/* The server answers with JSON, but tolerate the single-quoted Agda Debug
   shape too, so a stray /raw-style body still renders. */
function parseResponse(text) {
  const s = String(text == null ? '' : text);
  if (s === '') {
    return {};
  }
  try {
    return JSON.parse(s);
  } catch (e) {
    return byRegex(s);
  }
}

function byRegex(s) {
  const grab = (re) => {
    const m = s.match(re);
    return m ? m[1] : undefined;
  };
  const idList = (re) => {
    const raw = grab(re);
    if (!raw) {
      return [];
    }
    return raw
      .split(',')
      .map((x) => parseInt(String(x).trim(), 10))
      .filter((n) => Number.isInteger(n) && n >= 0);
  };
  const obj = {};
  const put = (key, value) => {
    if (value !== undefined) {
      obj[key] = value;
    }
  };
  put('username', grab(/['"]username['"]\s*:\s*['"]([^'"]*)['"]/));
  put('text', grab(/['"]text['"]\s*:\s*['"]([\s\S]*?)['"]\s*,/));
  put('likes', grab(/['"]likes['"]\s*:\s*(-?\d+)/));
  put('session_token', grab(/['"]session_token['"]\s*:\s*['"]([^']*)['"]/));
  put('tweet_id', grab(/['"]tweet_id['"]\s*:\s*['"]([^']*)['"]/));
  obj.timeline = idList(/['"]timeline['"]\s*:\s*\[([^\[\]]*)\]/);
  obj.replies = idList(/['"]replies['"]\s*:\s*\[([^\[\]]*)\]/);
  return obj;
}

/* Body builders: token first, one value per line, no trailing separator. */
function wireLines(kind, args, token) {
  const tk = String(token == null ? '' : token);
  if (kind === 'login' || kind === 'signup') {
    return [clean(args.username), clean(args.password)];
  }
  if (kind === 'logout') {
    return [tk];
  }
  if (kind === 'post-tweet') {
    return [tk, clean(args.text)];
  }
  if (kind === 'global-timeline') {
    const len = String(args.len);
    return tk === '' ? [len] : [tk, len];
  }
  if (kind === 'get-tweet') {
    const id = String(args.id);
    return tk === '' ? [id] : [tk, id];
  }
  if (kind === 'private-timeline') {
    return [tk, String(args.len)];
  }
  if (kind === 'like-tweet' || kind === 'unlike-tweet') {
    return [tk, String(args.id)];
  }
  if (kind === 'follow-user' || kind === 'unfollow-user') {
    return [tk, clean(args.username)];
  }
  return [];
}

function clean(s) {
  return String(s == null ? '' : s).replace(/[\r\n]/g, '');
}

function wireBody(kind, args, token) {
  return wireLines(kind, args, token).join(LINE_SEP);
}

async function performAction(kind, args, opts) {
  if (!ENDPOINTS.includes(kind)) {
    return { error: 'network-error', message: 'Unknown action' };
  }
  const authAction = kind === 'login' || kind === 'signup';
  const token = authAction ? '' : (signedIn() ? currentToken() : '');
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
  if (response.status === 200) {
    return { status: 200, data: data };
  }
  if (response.status === 401) {
    if (authAction) {
      return {
        error: 'auth-failed',
        status: 401,
        message: kind === 'login'
          ? 'Wrong username or password'
          : 'That username is already taken'
      };
    }
    if (opts.silent) {
      return { error: 'session-expired', status: 401, message: 'Not visible yet' };
    }
    if (!sessionGone) {
      sessionGone = true;
      clearSession();
      showAuth('Your session has expired — please log in again.');
    }
    return { error: 'session-expired', status: 401, handled: true, message: 'Session expired' };
  }
  const name = data && data.error ? data.error : response.statusText;
  let message = name;
  if (kind === 'signup' && response.status === 400) {
    message = 'That username is already taken';
  } else if (kind === 'get-tweet' && response.status === 403) {
    message = 'Not allowed to view this post';
  }
  return { error: 'request-failed', status: response.status, message: message };
}

/* --- rows: author[ ✓] — text · likes · Like --- */

/* liveRows maps a list id to the rows currently on screen; the ✓ marker is
   repainted from the client-side followed map. */
const liveRows = new Map();

function authorLabel(row) {
  if (!row.username) {
    return;
  }
  const mark = followed.get(row.username) === true ? CHECK : '';
  row.author.textContent = '@' + row.username + mark;
}

function paintLike(row) {
  if (liked.has(row.id)) {
    row.li.classList.add('liked');
    row.like.textContent = 'Unlike';
  } else {
    row.li.classList.remove('liked');
    row.like.textContent = 'Like';
  }
}

function fillRow(row, data) {
  if (!data || data.username == null) {
    row.body.textContent = 'not visible';
    row.li.classList.add('muted-row');
    return;
  }
  row.li.classList.remove('muted-row');
  row.username = String(data.username);
  authorLabel(row);
  const words = String(data.text == null ? '' : data.text).replace(/\s+/g, ' ');
  row.body.textContent = words.length > 180 ? words.slice(0, 180) + '\u2026' : words;
  const likes = Number(data.likes == null ? 0 : data.likes);
  row.meta.textContent = likes + (likes === 1 ? ' like' : ' likes');
}

function makeRow(id) {
  const li = document.createElement('li');
  li.className = 'row';
  const author = document.createElement('button');
  author.type = 'button';
  author.className = 'author-btn';
  author.textContent = '#' + id;
  const dash = document.createElement('span');
  dash.className = 'dash';
  dash.textContent = DASH;
  const body = document.createElement('span');
  body.className = 'body';
  body.textContent = 'filing\u2026';
  const meta = document.createElement('span');
  meta.className = 'meta';
  const like = document.createElement('button');
  like.type = 'button';
  like.className = 'like-btn';
  li.appendChild(author);
  li.appendChild(dash);
  li.appendChild(body);
  li.appendChild(meta);
  li.appendChild(like);
  const row = { id: id, username: '', li: li, author: author, body: body, meta: meta, like: like };
  author.addEventListener('click', async () => {
    await toggleFollow(row);
  });
  like.addEventListener('click', async () => {
    await toggleLike(row);
  });
  paintLike(row);
  return row;
}

function markFollow(name) {
  for (const list of liveRows.values()) {
    for (const row of list) {
      if (row.username === name) {
        authorLabel(row);
      }
    }
  }
}

function hydrateRow(row) {
  return performAction('get-tweet', { id: row.id }, { silent: true }).then((result) => {
    if (result.error || !result.data) {
      fillRow(row, null);
      return;
    }
    fillRow(row, result.data);
  });
}

/* renderTimeline paints the skeleton rows and returns the per-row get-tweet
   promises so the caller can await them all in one Promise.all. */
function renderTimeline(listId, errorId, result) {
  const listEl = el(listId);
  const errEl = el(errorId);
  listEl.textContent = '';
  if (result.error) {
    errEl.textContent = result.message;
    liveRows.set(listId, []);
    return [];
  }
  errEl.textContent = '';
  const raw = result.data && Array.isArray(result.data.timeline) ? result.data.timeline : [];
  const painted = [];
  const jobs = [];
  for (const value of raw) {
    const id = parseInt(String(value), 10);
    if (!Number.isInteger(id) || id < 0) {
      continue;
    }
    const row = makeRow(id);
    listEl.appendChild(row.li);
    painted.push(row);
    jobs.push(hydrateRow(row));
  }
  if (!painted.length) {
    const empty = document.createElement('li');
    empty.className = 'empty-row';
    empty.textContent = 'Nothing filed yet.';
    listEl.appendChild(empty);
  }
  liveRows.set(listId, painted);
  return jobs;
}

/* --- panels + inline actions --- */

function note(okText, errText) {
  el('action-ok').textContent = okText || '';
  el('action-error').textContent = errText || '';
}

function showAuth(noticeText) {
  el('auth-panel').hidden = false;
  el('app-panel').hidden = true;
  el('logout-btn').hidden = true;
  el('session-status').textContent = 'Logged out';
  el('auth-notice').textContent = noticeText || '';
  loadPublic();
}

function showApp() {
  sessionGone = false;
  el('auth-panel').hidden = true;
  el('app-panel').hidden = false;
  el('logout-btn').hidden = false;
  el('session-status').textContent =
    currentUser() ? 'Filed under @' + currentUser() : 'Logged in';
}

async function toggleFollow(row) {
  const name = row.username;
  if (!name || name === '?') {
    return;
  }
  if (!signedIn()) {
    showAuth('Log in to follow @' + name + '.');
    return;
  }
  const on = followed.get(name) === true;
  const kind = on ? 'unfollow-user' : 'follow-user';
  const result = await performAction(kind, { username: name }, {});
  if (result.handled) {
    return;
  }
  if (result.error) {
    note('', result.message);
    return;
  }
  if (on) {
    followed.delete(name);
  } else {
    followed.set(name, true);
  }
  markFollow(name);
  note(on ? 'Unfollowed @' + name : 'Following @' + name, '');
  await loadColumns();
}

async function toggleLike(row) {
  if (!signedIn()) {
    showAuth('Log in to like posts.');
    return;
  }
  const wasOn = liked.has(row.id);
  const kind = wasOn ? 'unlike-tweet' : 'like-tweet';
  const result = await performAction(kind, { id: row.id }, {});
  if (result.handled) {
    return;
  }
  if (result.error) {
    note('', result.message);
    return;
  }
  if (wasOn) {
    liked.delete(row.id);
  } else {
    liked.add(row.id);
  }
  paintLike(row);
  note(wasOn ? 'Unliked #' + row.id : 'Liked #' + row.id, '');
  await hydrateRow(row);
}

async function loadColumns() {
  const priv = performAction('private-timeline', { len: TIMELINE_LEN }, {});
  const glob = performAction('global-timeline', { len: TIMELINE_LEN }, {});
  const pair = await Promise.all([priv, glob]);
  const privJobs = renderTimeline('private-list', 'private-error', pair[0]);
  const globJobs = renderTimeline('global-list', 'global-error', pair[1]);
  await Promise.all([Promise.all(privJobs), Promise.all(globJobs)]);
}

async function loadPublic() {
  const result = await performAction('global-timeline', { len: TIMELINE_LEN }, {});
  const jobs = renderTimeline('public-list', 'public-error', result);
  await Promise.all(jobs);
}

/* --- form handlers --- */

el('login-form').addEventListener('submit', async (ev) => {
  ev.preventDefault();
  const username = el('login-username').value.trim();
  const password = el('login-password').value;
  el('login-error').textContent = '';
  const result = await performAction('login', { username: username, password: password }, {});
  if (result.status === 200 && result.data && result.data.session_token != null) {
    setSession(result.data.session_token, username);
    showApp();
    await loadColumns();
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
    setSession(result.data.session_token, username);
    showApp();
    await loadColumns();
  } else {
    el('signup-error').textContent = result.message || 'That username is already taken';
  }
});

el('compose-text').addEventListener('keydown', (ev) => {
  if (ev.key === 'Enter' && (ev.ctrlKey || ev.metaKey)) {
    ev.preventDefault();
    el('compose-form').requestSubmit();
  }
});

el('compose-form').addEventListener('submit', async (ev) => {
  ev.preventDefault();
  const text = el('compose-text').value;
  if (!signedIn()) {
    showAuth('Log in to file copy.');
    return;
  }
  if (!text) {
    return;
  }
  el('compose-ok').textContent = '';
  el('compose-error').textContent = '';
  const result = await performAction('post-tweet', { text: text }, {});
  if (result.handled) {
    return;
  }
  if (result.error) {
    el('compose-error').textContent = result.message;
    return;
  }
  const posted = result.data && result.data.tweet_id != null ? result.data.tweet_id : null;
  el('compose-ok').textContent = posted === null ? 'Posted.' : 'Posted as #' + posted;
  el('compose-text').value = '';
  await loadColumns();
});

el('logout-btn').addEventListener('click', async () => {
  await performAction('logout', {}, {});
  clearSession();
  sessionGone = false;
  liked.clear();
  followed.clear();
  liveRows.clear();
  start();
});

function start() {
  if (signedIn()) {
    showApp();
    loadColumns();
  } else {
    clearSession();
    showAuth('');
  }
}

start();
