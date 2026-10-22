'use strict';

const TOKEN_KEY = 'formal-twitter-token';
const USER_KEY = 'formal-twitter-user';
const TIMELINE_LEN = 20;
const ENDPOINTS = ['login', 'signup', 'post-tweet', 'get-tweet', 'timeline'];

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
  hideTweetDetail();
}

function showTweetDetailError(message) {
  el('tweet-detail').hidden = false;
  el('tweet-detail-content').hidden = true;
  el('tweet-detail-error').textContent = message;
}

function tweetRequiredNotice() {
  if (currentToken()) {
    showTweetDetailError('Please log in again to view this.');
  } else {
    showAuth('You need to log in to view this post.');
  }
}

function parseResponse(text) {
  const s = String(text == null ? '' : text);
  try {
    return JSON.parse(s.replace(/'/g, '"'));
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
    return raw
      ? raw.split(',').map((x) => parseInt(x.trim(), 10)).filter((n) => Number.isInteger(n) && n >= 0)
      : [];
  };
  const obj = {};
  const assign = (key, value) => {
    if (value !== undefined) obj[key] = value;
  };
  assign('username', grab(/'username'\s*:\s*'([^']*)'/));
  assign('text', grab(/'text'\s*:\s*'([\s\S]*)'\s*,\s*'likes'/));
  assign('likes', grab(/'likes'\s*:\s*(-?\d+)/));
  assign('session_token', grab(/'session_token'\s*:\s*'([^']*)'/));
  assign('tweet_id', grab(/'tweet_id'\s*:\s*'([^']*)'/));
  obj.replies = idList(/'replies'\s*:\s*\[([^\[\]]*)\]/);
  obj.timeline = idList(/'timeline'\s*:\s*\[([^\[\]]*)\]/);
  return obj;
}

function buildBody(kind, args, token) {
  if (kind === 'login' || kind === 'signup') {
    return [args.username, args.password];
  }
  if (kind === 'post-tweet') {
    return [token || '', args.text];
  }
  return [];
}

// Browsers cannot send a GET body, so get-tweet/timeline arguments
// travel as query parameters (the backend decodes them positionally).
function buildParams(kind, args, token) {
  const params = new URLSearchParams();
  if (kind === 'get-tweet') {
    if (token) params.set('token', token);
    params.set('id', String(args.id));
  } else if (kind === 'timeline') {
    if (token) params.set('token', token);
    params.set('len', String(args.len));
  }
  return params.toString();
}

async function performAction(kind, args, opts) {
  if (!ENDPOINTS.includes(kind)) {
    return { error: 'network-error', message: 'Unknown action' };
  }
  const authAction = kind === 'login' || kind === 'signup';
  const token = authAction ? null : currentToken();
  const useBody = kind === 'post-tweet' || authAction;
  const url = '/api/' + kind + (useBody ? '' : '?' + buildParams(kind, args, token));
  let response;
  try {
    response = await fetch(url, {
      method: useBody ? 'POST' : 'GET',
      headers: { 'Content-Type': 'text/plain' },
      body: useBody ? buildBody(kind, args, token).join('\n') + '\n' : undefined
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
      return { error: 'session-expired', message: 'Session expired again — please log in' };
    }
    const expired = token != null && token !== '';
    clearSession();
    pending = { kind: kind, args: args, opts: opts, via: opts.via };
    showAuth(expired
      ? 'Your session has expired — please log in again. You will be returned to where you left off.'
      : 'You need to log in to do that. You will be returned to where you left off.');
    return { error: 'session-expired', handled: true };
  }
  if (response.status !== 200) {
    const name = data && data.error ? data.error : response.statusText;
    return {
      error: 'request-failed',
      status: response.status,
      message: kind === 'get-tweet' && response.status === 403 ? 'Not allowed to view this post' : name
    };
  }
  return { status: response.status, data: data || {} };
}

async function afterAuthVisitor() {
  showApp();
  const p = pending;
  pending = null;
  if (p && typeof p.via === 'function' && !p.replayed) {
    p.replayed = true;
    const result = await performAction(p.kind, p.args, Object.assign({}, p.opts, { replaying: true }));
    p.via(result);
  } else {
    loadTimeline();
  }
}

function timelineVia(listId, errorId) {
  return (result) => {
    if (result.handled) return;
    const listEl = el(listId);
    const errEl = el(errorId);
    if (result.error) {
      listEl.textContent = '';
      errEl.textContent = result.message;
      return;
    }
    errEl.textContent = '';
    renderTweetIdList(listEl, result.data.timeline, (id) => openTweet(id, {}));
  };
}

async function loadTimelineInto(listId, errorId) {
  const via = timelineVia(listId, errorId);
  const result = await performAction('timeline', { len: TIMELINE_LEN }, { via: via });
  return via(result);
}

function loadPublicTimeline() {
  return loadTimelineInto('public-list', 'public-error');
}

function loadTimeline() {
  return loadTimelineInto('timeline-list', 'timeline-error');
}

function renderTweetIdList(listEl, ids, onOpen) {
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
    const li = document.createElement('li');
    const button = document.createElement('button');
    button.type = 'button';
    button.textContent = '#' + id;
    button.addEventListener('click', () => onOpen(id));
    li.appendChild(button);
    listEl.appendChild(li);
    hydrateTweetButton(button, id);
  }
}

// The timeline/replies endpoints only return IDs; look each tweet up
// so the list shows author + text. Clicking still opens the detail view.
function hydrateTweetButton(button, id) {
  performAction('get-tweet', { id: id }, {}).then((result) => {
    if (result.handled) return;
    if (result.error || !result.data) {
      button.classList.add('muted');
      button.textContent = '#' + id + (result.message ? ' — ' + result.message : '');
      return;
    }
    const t = result.data;
    const replies = Array.isArray(t.replies) ? t.replies : [];
    const text = String(t.text || ' ').replace(/\s+/g, ' ');
    button.textContent =
      '@' + (t.username || '?') + ': ' + text +
      '  ·  ' + (t.likes || 0) + ' like' + ((t.likes || 0) === 1 ? '' : 's') +
      (replies.length ? '  ·  ' + replies.length + ' repl' + (replies.length === 1 ? 'y' : 'ies') : '');
  });
}

function hideTweetDetail() {
  el('tweet-detail').hidden = true;
  el('tweet-detail-error').textContent = '';
}

function renderTweetDetail(id, data) {
  el('tweet-detail').hidden = false;
  el('tweet-detail-error').textContent = '';
  const box = el('tweet-detail-content');
  box.hidden = false;
  box.textContent = '';
  const body = document.createElement('p');
  body.textContent = data.text || '';
  const meta = document.createElement('p');
  meta.className = 'meta';
  const replies = Array.isArray(data.replies) ? data.replies : [];
  meta.textContent =
    'Post #' + id + ' — by @' + (data.username || '?') +
    ' — ' + (data.likes || 0) + ' likes — ' +
    (replies.length ? 'replies: ' + replies.map((r) => '#' + r).join(', ') : 'no replies');
  box.appendChild(body);
  box.appendChild(meta);
  const replyList = document.createElement('ul');
  replyList.className = 'tweet-list';
  renderTweetIdList(replyList, replies, (replyId) => openTweet(replyId, {}));
  box.appendChild(replyList);
}

async function openTweet(id, opts) {
  const via = (result) => {
    if (result.handled) return;
    if (result.error) {
      if (result.status === 403) {
        if (currentToken()) {
          showTweetDetailError('This post is restricted.');
        } else {
          showAuth('This post is not visible while logged out.');
        }
      } else {
        tweetRequiredNotice();
      }
      return;
    }
    if (currentToken()) {
      renderTweetDetail(id, result.data);
      if (window.scrollTo) window.scrollTo(0, 0);
    } else {
      showAuth('Log in to view the full post.');
    }
  };
  const result = await performAction('get-tweet', { id: id }, Object.assign({ via: via }, opts || {}));
  return via(result);
}

el('login-form').addEventListener('submit', async (ev) => {
  ev.preventDefault();
  const username = el('login-username').value.trim();
  const password = el('login-password').value;
  el('login-error').textContent = '';
  const result = await performAction('login', { username: username, password: password }, {});
  if (result.status === 200 && result.data && result.data.session_token != null) {
    setSession(result.data.session_token, username);
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
    setSession(result.data.session_token, username);
    await afterAuthVisitor();
  } else {
    el('signup-error').textContent = result.message || 'Unexpected response';
  }
});

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
      loadTimeline();
      return;
    }
    el('compose-error').textContent = 'Unexpected response';
  };
  const result = await performAction('post-tweet', { text: text }, { via: via });
  return via(result);
});

el('logout-btn').addEventListener('click', () => {
  clearSession();
  pending = null;
  showAuth('');
});

el('back-btn').addEventListener('click', hideTweetDetail);

function start() {
  if (currentToken()) {
    showApp();
    loadTimeline();
  } else {
    clearSession();
    showAuth('');
  }
}

start();
