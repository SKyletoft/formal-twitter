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
  post-tweet     : LoginToken → String        → Action
  -- delete-tweet   : LoginToken → TweetId       → Action
  -- like           : LoginToken → TweetId       → Action
  -- unlike         : LoginToken → TweetId       → Action
  get-tweet      : Maybe LoginToken → TweetId → Action
  timeline       : Maybe LoginToken → Nat     → Action
  -- search         : Maybe LoginToken → String  → Action
  login          : String → String            → Action
  -- logout         : LoginToken                 → Action
  signup         : String → String            → Action
  -- delete-account : LoginToken                 → Action

to-request : Action → String
to-request (post-tweet (token tk) txt) =
  unlines ("POST /api/post-tweet 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ ""
          ∷ show tk
          ∷ txt
          ∷ [])
to-request (get-tweet (just (token tk)) (tweet-id twt)) =
  unlines ("GET /api/get-tweet 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ ""
          ∷ show tk
          ∷ show twt
          ∷ [])
to-request (get-tweet nothing (tweet-id twt)) =
  unlines ("GET /api/get-tweet 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ ""
          ∷ ""
          ∷ show twt
          ∷ [])
to-request (timeline (just (token tk)) len) =
  unlines ("GET /api/timeline 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ ""
          ∷ show tk
          ∷ show len
          ∷ [])
to-request (timeline nothing len) =
  unlines ("GET /api/timeline 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ ""
          ∷ ""
          ∷ show len
          ∷ [])
to-request (login username passwd) =
  unlines ("POST /api/login 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
          ∷ ""
          ∷ username
          ∷ passwd
          ∷ [])
to-request (signup username passwd) =
  unlines ("POST /api/signup 1.1"
          ∷ "Content-Type: text/plain"
          ∷ ""
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
          ∷ ""
          ∷ "{'error': 'access_denied'}"
          ∷ [])
to-response outdated-login-token =
  unlines ("HTTP/1.1 401 Unauthorized"
          ∷ "Content-Type: application/json"
          ∷ ""
          ∷ ""
          ∷ "{'error': 'session_expired'}"
          ∷ [])
to-response (tweet-id (tweet-id twt)) =
  unlines ("HTTP/1.1 200 OK"
          ∷ "Content-Type: application/json"
          ∷ ""
          ∷ ""
          ∷ ("{'tweet_id': '" ++ show twt ++ "'}")
          ∷ [])
to-response (timeline xs) =
  unlines ("HTTP/1.1 200 OK"
          ∷ "Content-Type: application/json"
          ∷ ""
          ∷ ""
          ∷ ("{'timeline': [" ++ show-tweets xs ++ "]}")
          ∷ [])
to-response (session-token (token tk)) =
  unlines ("HTTP/1.1 200 OK"
          ∷ "Content-Type: application/json"
          ∷ ""
          ∷ ""
          ∷ ("{'session_token': '" ++ show tk ++ "'}")
          ∷ [])
to-response login-error =
  unlines ("HTTP/1.1 401 Unauthorized"
          ∷ "Content-Type: application/json"
          ∷ ""
          ∷ ""
          ∷ "{'error': 'login_failed'}"
          ∷ [])
to-response signup-error =
  unlines ("HTTP/1.1 400 Bad Request"
          ∷ "Content-Type: application/json"
          ∷ ""
          ∷ ""
          ∷ "{'error': 'signup_failed'}"
          ∷ [])
to-response (tweet username txt like-count replies) =
  unlines ("HTTP/1.1 200 OK"
          ∷ "Content-Type: application/json"
          ∷ ""
          ∷ ""
          ∷ ("{'username': '" ++ username
             ++ "', 'text': '" ++ txt
             ++ "', 'likes': " ++ show like-count
             ++ ", 'replies': [" ++ show-tweets replies
             ++ "]}")
          ∷ [])
