'use strict';

// frontend3 — "stacked labeled rails" client.
//
// Follow state is a CLIENT-SIDE cache: the wire protocol (backend/src/wire.rs)
// has no read-endpoint for "am I following <name>", so the followState map
// (name -> bool) is the browser's own truth and only follow-user / unfollow-user
// are ever sent to the server. The likedIds set is cached the same way:
// the server never reports "liked by me", only like-tweet / unlike-tweet
// acknowledgements. Everything else — timelines, tweet author/text/likes — is
// re-read from the database-backed server on every render, never kept in RAM.
//
// Wire protocol: POST /api/<name>, Content-Type text/plain, body = lines joined
// by CRLF with the token first and NO trailing newline. A 200 with an empty
// body means ok; 200 {"tweet_id":"N"} / {"session_token":"N"} / {"timeline":[…]}.

const TOKEN_KEY = 'formal3-token';
const USER_KEY = 'formal3-user';
const TIMELINE_LEN = 20;

const el = (id) => document.getElementById(id);

const likedIds = new Set();
const followState = new Map();

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

function parseResponse(text) {
  const s = String(text == null ? '' : text);
  if (!s) {
    return {};
  }
  try {
    return JSON.parse(s.replace(/'/g, '"'));
  } catch (e) {
    return byRegex(s);
  }
}

// Fallback for single-quoted (Agda-style) renderings of the same bodies.
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
      .map((x) => parseInt(x.trim(), 10))
      .filter((n) => Number.isInteger(n) && n >= 0);
  };
  const obj = {};
  const assign = (key, value) => {
    if (value !== undefined) {
      obj[key] = value;
    }
  };
  assign('username', grab(/['"]username['"]\s*:\s*['"]([^'"]*)['"]/));
  assign('text', grab(/['"]text['"]\s*:\s*['"]([\s\S]*?)['"]\s*,\s*['"]likes['"]/));
  assign('likes', grab(/['"]likes['"]\s*:\s*(-?\d+)/));
  assign('session_token', grab(/['"]session_token['"]\s*:\s*['"]?([^'"]*)['"]?/));
  assign('tweet_id', grab(/['"]tweet_id['"]\s*:\s*['"]?([^'"]*)['"]?/));
  obj.replies = idList(/['"]replies['"]\s*:\s*\[([^\[\]]*)\]/);
  obj.timeline = idList(/['"]timeline['"]\s*:\s*\[([^\[\]]*)\]/);
  return obj;
}

// The label for a poster's name: '@name', plus ' ✓' once the client-side
// follow cache says we follow them.
function nameLabel(name) {
  return '@' + name + (followState.get(name) ? ' ✓' : '');
}

// Wire bodies: token FIRST, CRLF-joined, no trailing newline.
function bodyLines(kind, args) {
  const token = currentToken();
  const clean = (s) => String(s == null ? '' : s).replace(/[\r\n]/g, '');
  const num = (v) => String(v == null ? '' : v);
  if (kind === 'login' || kind === 'signup') {
    return [args.username, args.password];
  }
  if (kind === 'logout') {
    return [token || ''];
  }
  if (kind === 'post-tweet') {
    return [token || '', clean(args.text)];
  }
  if (kind === 'global-timeline') {
    return token ? [token, num(args.len)] : [num(args.len)];
  }
  if (kind === 'private-timeline') {
    return [token || '', num(args.len)];
  }
  if (kind === 'get-tweet') {
    return token ? [token, num(args.id)] : [num(args.id)];
  }
  if (kind === 'like-tweet' || kind === 'unlike-tweet') {
    return [token || '', num(args.id)];
  }
  if (kind === 'follow-user' || kind === 'unfollow-user') {
    return [token || '', clean(args.username)];
  }
  return [];
}

async function performAction(kind, args) {
  const lines = bodyLines(kind, args);
  let response;
  try {
    response = await fetch('/api/' + kind, {
      method: 'POST',
      headers: { 'Content-Type': 'text/plain' },
      body: lines.join('\r\n')
    });
  } catch (e) {
    return { error: 'network-error', message: 'Could not reach the server' };
  }
  const text = await response.text();
  const data = parseResponse(text);
  if (response.status === 401) {
    if (kind === 'login' || kind === 'signup') {
      return {
        error: 'auth-failed',
        message: kind === 'login'
          ? 'Wrong username or password'
          : 'Could not create that account'
      };
    }
    const hadToken = currentToken() != null && currentToken() !== '';
    clearSession();
    showAuth(hadToken
      ? 'Your session has expired — please log in again.'
      : 'You need to log in to do that.');
    return { error: 'session-expired', handled: true };
  }
  if (response.status !== 200) {
    return {
      error: 'request-failed',
      status: response.status,
      message: kind === 'signup' && response.status === 400
        ? 'That username is already taken — pick another name.'
        : (data && data.error ? data.error : response.statusText || 'Unexpected response')
    };
  }
  return { status: 200, data: data };
}

function showAuth(noticeText) {
  el('auth-panel').hidden = false;
  el('app-panel').hidden = true;
  el('logout-btn').hidden = true;
  el('session-status').textContent = 'Logged out';
  el('auth-notice').textContent = noticeText || '';
  setRail('private-rail', true);
  loadPublicRail();
}

function showApp() {
  el('auth-panel').hidden = true;
  el('app-panel').hidden = false;
  el('logout-btn').hidden = false;
  el('session-status').textContent =
    'Logged in as @' + currentUser() + ' (token #' + currentToken() + ')';
  setRail('private-rail', false);
  renderRails();
}

function setRail(railId, hidden) {
  const rail = el(railId);
  if (rail) {
    rail.hidden = hidden;
  }
}

// The two rails are fetched in parallel: PRIVATE (private-timeline, token)
// sits directly above PUBLIC (global-timeline, token) in the document, and both
// are re-read from the database on every login / post / like / follow.
function renderRails() {
  if (!currentToken()) {
    setRail('private-rail', true);
    return loadPublicRail();
  }
  setRail('private-rail', false);
  setRail('public-rail', false);
  return Promise.all([
    performAction('private-timeline', { len: TIMELINE_LEN }),
    performAction('global-timeline', { len: TIMELINE_LEN })
  ]).then((pair) => {
    renderRail('private-list', 'private-error', pair[0]);
    renderRail('public-list', 'public-error', pair[1]);
  });
}

function loadPublicRail() {
  setRail('public-rail', false);
  return performAction('global-timeline', { len: TIMELINE_LEN }).then((result) => {
    renderRail('public-list', 'public-error', result);
  });
}

function renderRail(listId, errorId, result) {
  const listEl = el(listId);
  const errEl = el(errorId);
  listEl.textContent = '';
  errEl.textContent = '';
  if (result.error) {
    errEl.textContent = result.message || 'Timeline unavailable';
    return;
  }
  const ids = Array.isArray(result.data.timeline) ? result.data.timeline : [];
  if (!ids.length) {
    const empty = document.createElement('li');
    empty.className = 'empty-row';
    empty.textContent = 'Nothing here yet.';
    listEl.appendChild(empty);
    return;
  }
  for (const id of ids) {
    listEl.appendChild(makeTweetCard(id));
  }
}

// A row rendered as a tweet-CARD: the poster-NAME button (the follow/unfollow
// toggle) at the top-left, the tweet text, the meta line, and the Like button
// at the bottom-right.
function makeTweetCard(id) {
  const card = document.createElement('li');
  card.className = 'tweet-card';

  const authorBtn = document.createElement('button');
  authorBtn.className = 'card-author';
  authorBtn.type = 'button';
  authorBtn.textContent = '#' + id;

  const textEl = document.createElement('p');
  textEl.className = 'card-text';

  const metaEl = document.createElement('p');
  metaEl.className = 'card-meta';
  metaEl.textContent = 'Post #' + id;

  const likeBtn = document.createElement('button');
  likeBtn.className = 'card-like';
  likeBtn.type = 'button';
  likeBtn.textContent = likedIds.has(id) ? 'Unlike' : 'Like';

  const statusEl = document.createElement('p');
  statusEl.className = 'card-status';

  card.appendChild(authorBtn);
  card.appendChild(textEl);
  card.appendChild(metaEl);
  card.appendChild(likeBtn);
  card.appendChild(statusEl);

  // Follow toggle: not-followed -> follow-user and ' ✓' on the label;
  // followed -> unfollow-user and drop the checkmark.
  authorBtn.addEventListener('click', async () => {
    const name = authorBtn.dataset.name;
    if (!name) {
      return;
    }
    if (!currentToken()) {
      statusEl.textContent = 'Log in to follow people.';
      return;
    }
    statusEl.textContent = '';
    const following = followState.get(name) === true;
    const kind = following ? 'unfollow-user' : 'follow-user';
    const result = await performAction(kind, { username: name });
    if (result.error) {
      statusEl.textContent = result.message || 'Could not change that';
      return;
    }
    followState.set(name, !following);
    authorBtn.textContent = nameLabel(name);
    statusEl.textContent = following
      ? 'Unfollowed @' + name + '.'
      : 'Now following @' + name + '.';
    renderRails();
  });

  // Like toggle: first click -> like-tweet, second click -> unlike-tweet.
  likeBtn.addEventListener('click', async () => {
    if (!currentToken()) {
      statusEl.textContent = 'Log in to like posts.';
      return;
    }
    statusEl.textContent = '';
    const liked = likedIds.has(id);
    const result = await performAction(liked ? 'unlike-tweet' : 'like-tweet', { id: id });
    if (result.error) {
      statusEl.textContent = result.message || 'Could not do that';
      return;
    }
    if (liked) {
      likedIds.delete(id);
    } else {
      likedIds.add(id);
    }
    likeBtn.textContent = likedIds.has(id) ? 'Unlike' : 'Like';
    statusEl.textContent = liked
      ? 'Unliked post #' + id + '.'
      : 'Liked post #' + id + '.';
    renderRails();
  });

  hydrateCard(id, authorBtn, textEl, metaEl);
  return card;
}

// Hydrate a card from the database via get-tweet: token when logged in,
// anonymous (id only) when logged out.
function hydrateCard(id, authorBtn, textEl, metaEl) {
  performAction('get-tweet', { id: id }).then((result) => {
    if (result.error) {
      authorBtn.classList.add('muted');
      textEl.textContent = result.message || 'Not available';
      return;
    }
    const t = result.data;
    const name = String(t.username == null ? '?' : t.username);
    authorBtn.dataset.name = name;
    authorBtn.textContent = nameLabel(name);
    textEl.textContent = String(t.text == null ? '' : t.text).replace(/\s+/g, ' ').trim();
    const likes = Number(t.likes == null ? 0 : t.likes);
    const replies = Array.isArray(t.replies) ? t.replies : [];
    metaEl.textContent =
      'Post #' + id +
      ' — ' + likes + (likes === 1 ? ' like' : ' likes') +
      (replies.length ? ' — ' + replies.length + (replies.length === 1 ? ' reply' : ' replies') : '');
  });
}

el('login-form').addEventListener('submit', async (ev) => {
  ev.preventDefault();
  const username = el('login-username').value.trim();
  const password = el('login-password').value;
  el('login-error').textContent = '';
  const result = await performAction('login', { username: username, password: password });
  if (result.error) {
    el('login-error').textContent = result.message;
    return;
  }
  if (result.data && result.data.session_token != null) {
    setSession(result.data.session_token, username);
    showApp();
  } else {
    el('login-error').textContent = 'No session token in the reply';
  }
});

el('signup-form').addEventListener('submit', async (ev) => {
  ev.preventDefault();
  const username = el('signup-username').value.trim();
  const password = el('signup-password').value;
  el('signup-error').textContent = '';
  const result = await performAction('signup', { username: username, password: password });
  if (result.error) {
    el('signup-error').textContent = result.message;
    return;
  }
  if (result.data && result.data.session_token != null) {
    setSession(result.data.session_token, username);
    showApp();
  } else {
    el('signup-error').textContent = 'No session token in the reply';
  }
});

el('compose-text').addEventListener('keydown', (ev) => {
  if (ev.key === 'Enter' && (ev.ctrlKey || ev.metaKey)) {
    ev.preventDefault();
    el('compose-form').requestSubmit();
  }
});

// An empty 200 body means ok; post-tweet replies carry tweet_id as a string.
el('compose-form').addEventListener('submit', async (ev) => {
  ev.preventDefault();
  const text = el('compose-text').value;
  el('compose-error').textContent = '';
  el('compose-ok').textContent = '';
  if (!currentToken()) {
    el('compose-error').textContent = 'Log in to post.';
    return;
  }
  const result = await performAction('post-tweet', { text: text });
  if (result.error) {
    el('compose-error').textContent = result.message;
    return;
  }
  if (result.data && result.data.tweet_id != null) {
    el('compose-ok').textContent = 'Posted as #' + result.data.tweet_id;
    el('compose-text').value = '';
  } else {
    el('compose-ok').textContent = 'Posted.';
  }
  renderRails();
});

el('logout-btn').addEventListener('click', async () => {
  if (currentToken()) {
    await performAction('logout', {});
  }
  clearSession();
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
