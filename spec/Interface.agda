module Interface where

open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe
open import Agda.Builtin.List
open import Agda.Builtin.String

postulate
  unlines : List String → String
  show    : Nat → String
  _++_    : String → String → String
infixr 5 _++_

record LoginToken : Set where
  constructor token
  field
    t : Nat

record TweetId : Set where
  constructor tweet-id
  field
    t : Nat

-- The public API after parsing. Entirely unvalidated on purpose.
data Action : Set where
  post-tweet       : LoginToken → String        → Action
  delete-tweet     : LoginToken → TweetId       → Action
  like             : LoginToken → TweetId       → Action
  unlike           : LoginToken → TweetId       → Action
  follow           : LoginToken → String        → Action
  unfollow         : LoginToken → String        → Action
  get-tweet        : Maybe LoginToken → TweetId → Action
  global-timeline  : Maybe LoginToken → Nat     → Action
  private-timeline : LoginToken → Nat           → Action
  login            : String → String            → Action
  logout           : LoginToken                 → Action
  signup           : String → String            → Action

-- The model has no way to forget an account, so this is not an endpoint yet.
-- delete-account : LoginToken                 → Action

to-request : Action → String
to-request (post-tweet (token tk) txt) =
  unlines ("POST /api/post-tweet 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ show tk
          ∷ txt
          ∷ [])
to-request (delete-tweet (token tk) (tweet-id twt)) =
  unlines ("POST /api/delete-tweet 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ show tk
          ∷ show twt
          ∷ [])
to-request (like (token tk) (tweet-id twt)) =
  unlines ("POST /api/like-tweet 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ show tk
          ∷ show twt
          ∷ [])
to-request (unlike (token tk) (tweet-id twt)) =
  unlines ("POST /api/unlike-tweet 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ show tk
          ∷ show twt
          ∷ [])
to-request (follow (token tk) username) =
  unlines ("POST /api/follow-user 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ show tk
          ∷ username
          ∷ [])
to-request (unfollow (token tk) username) =
  unlines ("POST /api/unfollow-user 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ show tk
          ∷ username
          ∷ [])
to-request (get-tweet (just (token tk)) (tweet-id twt)) =
  unlines ("GET /api/get-tweet 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ show tk
          ∷ show twt
          ∷ [])
to-request (get-tweet nothing (tweet-id twt)) =
  unlines ("GET /api/get-tweet 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ show twt
          ∷ [])
to-request (global-timeline (just (token tk)) len) =
  unlines ("GET /api/global-timeline 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ show tk
          ∷ show len
          ∷ [])
to-request (global-timeline nothing len) =
  unlines ("GET /api/timeline 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ show len
          ∷ [])
to-request (private-timeline (token tk) len) =
  unlines ("GET /api/private-timeline 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ show tk
          ∷ show len
          ∷ [])
to-request (logout (token tk)) =
  unlines ("POST /api/logout 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ show tk
          ∷ [])
to-request (login username passwd) =
  unlines ("POST /api/login 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ username
          ∷ passwd
          ∷ [])
to-request (signup username passwd) =
  unlines ("POST /api/signup 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ username
          ∷ passwd
          ∷ [])

-- Possible responses from the public API
data Response : Set where
  ok                   : Response
  permission-error     : Response
  outdated-login-token : Response
  tweet-id             : TweetId → Response
  timeline             : List TweetId → Response
  session-token        : LoginToken → Response
  login-error          : Response
  signup-error         : Response
  tweet
    : String       -- Poster
    → String       -- Body
    → Nat          -- Likes
    → List TweetId -- Replies
    → Response

show-tweets : List TweetId → String
show-tweets [] = ""
show-tweets (tweet-id twt ∷ []) = show twt
show-tweets (tweet-id twt ∷ xs@(_ ∷ _)) = show twt ++ ", " ++ show-tweets xs

to-response : Response → String
to-response ok =
  unlines ("HTTP/1.1 200 OK"
          ∷ [])
to-response permission-error =
  unlines ("HTTP/1.1 403 Forbidden"
          ∷ "Content-Type: application/json"
          ∷ ""
          ∷ "{'error': 'access_denied'}"
          ∷ [])
to-response outdated-login-token =
  unlines ("HTTP/1.1 401 Unauthorized"
          ∷ "Content-Type: application/json"
          ∷ ""
          ∷ "{'error': 'session_expired'}"
          ∷ [])
to-response (tweet-id (tweet-id twt)) =
  unlines ("HTTP/1.1 200 OK"
          ∷ "Content-Type: application/json"
          ∷ ""
          ∷ ("{'tweet_id': '" ++ show twt ++ "'}")
          ∷ [])
to-response (timeline xs) =
  unlines ("HTTP/1.1 200 OK"
          ∷ "Content-Type: application/json"
          ∷ ""
          ∷ ("{'timeline': [" ++ show-tweets xs ++ "]}")
          ∷ [])
to-response (session-token (token tk)) =
  unlines ("HTTP/1.1 200 OK"
          ∷ "Content-Type: application/json"
          ∷ ""
          ∷ ("{'session_token': '" ++ show tk ++ "'}")
          ∷ [])
to-response login-error =
  unlines ("HTTP/1.1 401 Unauthorized"
          ∷ "Content-Type: application/json"
          ∷ ""
          ∷ "{'error': 'login_failed'}"
          ∷ [])
to-response signup-error =
  unlines ("HTTP/1.1 400 Bad Request"
          ∷ "Content-Type: application/json"
          ∷ ""
          ∷ "{'error': 'signup_failed'}"
          ∷ [])
to-response (tweet username txt like-count replies) =
  unlines ("HTTP/1.1 200 OK"
          ∷ "Content-Type: application/json"
          ∷ ""
          ∷ ("{'username': '" ++ username
             ++ "', 'text': '" ++ txt
             ++ "', 'likes': " ++ show like-count
             ++ ", 'replies': [" ++ show-tweets replies
             ++ "]}")
          ∷ [])

--------------------------------------------------------------------------------
--                                 INTERFACE                                  --
--------------------------------------------------------------------------------

open import Helpers

-- Don't formalise creation of cryptographic tokens. Implementations
-- should use a crypto library + a set to avoid repeats.
postulate
  new-pid : CreateNew TweetId
  new-sid : CreateNew LoginToken

open import Twitter LoginToken TweetId new-sid new-pid

to-output : Result → Response
to-output success                                  = ok
to-output denied                                   = permission-error
to-output expired                                  = outdated-login-token
to-output login-failed                             = login-error
to-output signup-failed                            = signup-error
to-output (returned-timeline x)                    = timeline x
to-output (issued-session x)                       = session-token x
to-output (created-post x)                         = tweet-id x
to-output (returned-post author txt likes replies) = tweet author txt likes replies

from-input : Action → Command
from-input (post-tweet tk txt)           = publish tk txt nothing
from-input (get-tweet (just tk) twt)     = read-post (just tk) twt
from-input (get-tweet nothing twt)       = read-post nothing twt
from-input (global-timeline (just tk) n) = read-global-timeline (just tk) n
from-input (global-timeline nothing n)   = read-global-timeline nothing n
from-input (private-timeline tk n)       = read-personal-timeline tk n
from-input (login username passwd)       = authenticate username passwd
from-input (signup username passwd)      = register username passwd
from-input (delete-tweet tk twt)         = delete tk twt
from-input (like tk twt)                 = like tk twt
from-input (unlike tk twt)               = unlike tk twt
from-input (follow tk username)          = follow tk username
from-input (unfollow tk username)        = unfollow tk username
from-input (logout tk)                   = revoke-token tk
