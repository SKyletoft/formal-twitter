module Interface where

open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe
open import Agda.Builtin.List
open import Agda.Builtin.String

open import Data.Nat.Properties                   using () renaming (_≟_ to _≟ₙ_)
open import Function                              using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no)

postulate
  unlines-crlf : List String → String
  show         : Nat → String
  _++_         : String → String → String
  octet-strlen : String → Nat
  escape       : String → String
  host         : String
  date         : String
infixr 6 _++_

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
  post-tweet       : LoginToken → String           → Action
  post-reply       : LoginToken → String → TweetId → Action
  delete-tweet     : LoginToken → TweetId          → Action
  like             : LoginToken → TweetId          → Action
  unlike           : LoginToken → TweetId          → Action
  follow           : LoginToken → String           → Action
  unfollow         : LoginToken → String           → Action
  get-tweet        : Maybe LoginToken → TweetId    → Action
  global-timeline  : Maybe LoginToken → Nat        → Action
  private-timeline : LoginToken → Nat              → Action
  login            : String → String               → Action
  logout           : LoginToken                    → Action
  signup           : String → String               → Action

-- The model has no way to forget an account, so this is not an endpoint yet.
-- delete-account : LoginToken                 → Action

to-request : Action → String
to-request (post-tweet (token tk) txt) =
  unlines-crlf $ "POST /api/post-tweet HTTP/1.1"
          ∷ "Host: " ++ host
          ∷ "Accept: application/json"
          ∷ "Content-Type: text/plain; charset=utf-8"
          ∷ "Content-Length: " ++ (show ∘ octet-strlen ∘ unlines-crlf $ show tk ∷ txt ∷ [])
          ∷ ""
          ∷ show tk
          ∷ txt
          ∷ []
to-request (post-reply (token tk) txt (tweet-id twt)) =
  unlines-crlf $ "POST /api/post-reply HTTP/1.1"
          ∷ "Host: " ++ host
          ∷ "Accept: application/json"
          ∷ "Content-Type: text/plain; charset=utf-8"
          ∷ "Content-Length: " ++ (show ∘ octet-strlen ∘ unlines-crlf $ show tk ∷ txt ∷ show twt ∷ [])
          ∷ ""
          ∷ show tk
          ∷ txt
          ∷ show twt
          ∷ []
to-request (delete-tweet (token tk) (tweet-id twt)) =
  unlines-crlf $ "POST /api/delete-tweet HTTP/1.1"
          ∷ "Host: " ++ host
          ∷ "Accept: application/json"
          ∷ "Content-Type: text/plain; charset=utf-8"
          ∷ "Content-Length: " ++ (show ∘ octet-strlen ∘ unlines-crlf $ show tk ∷ show twt ∷ [])
          ∷ ""
          ∷ show tk
          ∷ show twt
          ∷ []
to-request (like (token tk) (tweet-id twt)) =
  unlines-crlf $ "POST /api/like-tweet HTTP/1.1"
          ∷ "Host: " ++ host
          ∷ "Accept: application/json"
          ∷ "Content-Type: text/plain; charset=utf-8"
          ∷ "Content-Length: " ++ (show ∘ octet-strlen ∘ unlines-crlf $ show tk ∷ show twt ∷ [])
          ∷ ""
          ∷ show tk
          ∷ show twt
          ∷ []
to-request (unlike (token tk) (tweet-id twt)) =
  unlines-crlf $ "POST /api/unlike-tweet HTTP/1.1"
          ∷ "Host: " ++ host
          ∷ "Accept: application/json"
          ∷ "Content-Type: text/plain; charset=utf-8"
          ∷ "Content-Length: " ++ (show ∘ octet-strlen ∘ unlines-crlf $ show tk ∷ show twt ∷ [])
          ∷ ""
          ∷ show tk
          ∷ show twt
          ∷ []
to-request (follow (token tk) username) =
  unlines-crlf $ "POST /api/follow-user HTTP/1.1"
          ∷ "Host: " ++ host
          ∷ "Accept: application/json"
          ∷ "Content-Type: text/plain; charset=utf-8"
          ∷ "Content-Length: " ++ (show ∘ octet-strlen ∘ unlines-crlf $ show tk ∷ username ∷ [])
          ∷ ""
          ∷ show tk
          ∷ username
          ∷ []
to-request (unfollow (token tk) username) =
  unlines-crlf $ "POST /api/unfollow-user HTTP/1.1"
          ∷ "Host: " ++ host
          ∷ "Accept: application/json"
          ∷ "Content-Type: text/plain; charset=utf-8"
          ∷ "Content-Length: " ++ (show ∘ octet-strlen ∘ unlines-crlf $ show tk ∷ username ∷ [])
          ∷ ""
          ∷ show tk
          ∷ username
          ∷ []
to-request (get-tweet (just (token tk)) (tweet-id twt)) =
  unlines-crlf $ "POST /api/get-tweet HTTP/1.1"
          ∷ "Host: " ++ host
          ∷ "Accept: application/json"
          ∷ "Content-Type: text/plain; charset=utf-8"
          ∷ "Content-Length: " ++ (show ∘ octet-strlen ∘ unlines-crlf $ show tk ∷ show twt ∷ [])
          ∷ ""
          ∷ show tk
          ∷ show twt
          ∷ []
to-request (get-tweet nothing (tweet-id twt)) =
  unlines-crlf $ "POST /api/get-tweet HTTP/1.1"
          ∷ "Host: " ++ host
          ∷ "Accept: application/json"
          ∷ "Content-Type: text/plain; charset=utf-8"
          ∷ "Content-Length: " ++ (show ∘ octet-strlen ∘ unlines-crlf $ show twt ∷ [])
          ∷ ""
          ∷ show twt
          ∷ []
to-request (global-timeline (just (token tk)) len) =
  unlines-crlf $ "POST /api/global-timeline HTTP/1.1"
          ∷ "Host: " ++ host
          ∷ "Accept: application/json"
          ∷ "Content-Type: text/plain; charset=utf-8"
          ∷ "Content-Length: " ++ (show ∘ octet-strlen ∘ unlines-crlf $ show tk ∷ show len ∷ [])
          ∷ ""
          ∷ show tk
          ∷ show len
          ∷ []
to-request (global-timeline nothing len) =
  unlines-crlf $ "POST /api/global-timeline HTTP/1.1"
          ∷ "Host: " ++ host
          ∷ "Accept: application/json"
          ∷ "Content-Type: text/plain; charset=utf-8"
          ∷ "Content-Length: " ++ (show ∘ octet-strlen ∘ unlines-crlf $ show len ∷ [])
          ∷ ""
          ∷ show len
          ∷ []
to-request (private-timeline (token tk) len) =
  unlines-crlf $ "POST /api/private-timeline HTTP/1.1"
          ∷ "Host: " ++ host
          ∷ "Accept: application/json"
          ∷ "Content-Type: text/plain; charset=utf-8"
          ∷ "Content-Length: " ++ (show ∘ octet-strlen ∘ unlines-crlf $ show tk ∷ show len ∷ [])
          ∷ ""
          ∷ show tk
          ∷ show len
          ∷ []
to-request (logout (token tk)) =
  unlines-crlf $ "POST /api/logout HTTP/1.1"
          ∷ "Host: " ++ host
          ∷ "Accept: application/json"
          ∷ "Content-Type: text/plain; charset=utf-8"
          ∷ "Content-Length: " ++ (show ∘ octet-strlen ∘ unlines-crlf $ show tk ∷ [])
          ∷ ""
          ∷ show tk
          ∷ []
to-request (login username passwd) =
  unlines-crlf $ "POST /api/login HTTP/1.1"
          ∷ "Host: " ++ host
          ∷ "Accept: application/json"
          ∷ "Content-Type: text/plain; charset=utf-8"
          ∷ "Content-Length: " ++ (show ∘ octet-strlen ∘ unlines-crlf $ username ∷ passwd ∷ [])
          ∷ ""
          ∷ username
          ∷ passwd
          ∷ []
to-request (signup username passwd) =
  unlines-crlf $ "POST /api/signup HTTP/1.1"
          ∷ "Host: " ++ host
          ∷ "Accept: application/json"
          ∷ "Content-Type: text/plain; charset=utf-8"
          ∷ "Content-Length: " ++ (show ∘ octet-strlen ∘ unlines-crlf $ username ∷ passwd ∷ [])
          ∷ ""
          ∷ username
          ∷ passwd
          ∷ []

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
  unlines-crlf $ "HTTP/1.1 200 OK"
          ∷ "Date: " ++ date
          ∷ "Content-Length: 0"
          ∷ ""
          ∷ []
to-response permission-error =
  let body = "{\"error\": \"access_denied\"}" in
  unlines-crlf $ "HTTP/1.1 403 Forbidden"
          ∷ "Date: " ++ date
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen body)
          ∷ ""
          ∷ body
          ∷ []
to-response outdated-login-token =
  let body = "{\"error\": \"session_expired\"}" in
  unlines-crlf $ "HTTP/1.1 401 Unauthorized"
          ∷ "Date: " ++ date
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen body)
          ∷ ""
          ∷ body
          ∷ []
to-response (tweet-id (tweet-id twt)) =
  let body = "{\"tweet_id\": \"" ++ show twt ++ "\"}" in
  unlines-crlf $ "HTTP/1.1 200 OK"
          ∷ "Date: " ++ date
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen body)
          ∷ ""
          ∷ body
          ∷ []
to-response (timeline xs) =
  let body = "{\"timeline\": [" ++ show-tweets xs ++ "]}" in
  unlines-crlf $ "HTTP/1.1 200 OK"
          ∷ "Date: " ++ date
          ∷ "Cache-Control: no-store"
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen body)
          ∷ ""
          ∷ body
          ∷ []
to-response (session-token (token tk)) =
  let body = "{\"session_token\": \"" ++ show tk ++ "\"}" in
  unlines-crlf $ "HTTP/1.1 200 OK"
          ∷ "Date: " ++ date
          ∷ "Cache-Control: no-store"
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen body)
          ∷ ""
          ∷ body
          ∷ []
to-response login-error =
  let body = "{\"error\": \"login_failed\"}" in
  unlines-crlf $ "HTTP/1.1 401 Unauthorized"
          ∷ "Date: " ++ date
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen body)
          ∷ ""
          ∷ body
          ∷ []
to-response signup-error =
  let body = "{\"error\": \"signup_failed\"}" in
  unlines-crlf $ "HTTP/1.1 400 Bad Request"
          ∷ "Date: " ++ date
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen body)
          ∷ ""
          ∷ body
          ∷ []
to-response (tweet username txt like-count replies) =
  let body = "{\"username\": \"" ++ escape username
             ++ "\", \"text\": \"" ++ escape txt
             ++ "\", \"likes\": " ++ show like-count
             ++ ", \"replies\": [" ++ show-tweets replies
             ++ "]}" in
  unlines-crlf $ "HTTP/1.1 200 OK"
          ∷ "Date: " ++ date
          ∷ "Cache-Control: no-store"
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen body)
          ∷ ""
          ∷ body
          ∷ []

--------------------------------------------------------------------------------
--                                 INTERFACE                                  --
--------------------------------------------------------------------------------

open import Helpers

-- Don't formalise creation of cryptographic tokens. Implementations
-- should use a crypto library + a set to avoid repeats.
postulate
  new-pid : CreateNew TweetId
  new-sid : CreateNew LoginToken

_≟ₜ_ : (l : TweetId) → (r : TweetId) → Dec (l ≡ r)
(tweet-id l) ≟ₜ (tweet-id r) with l ≟ₙ r
... | yes p = yes $ cong tweet-id p
... | no ¬p = no  $ ¬p ∘ cong TweetId.t

_≟ₗ_ : (l : LoginToken) → (r : LoginToken) → Dec (l ≡ r)
(token l) ≟ₗ (token r) with l ≟ₙ r
... | yes p = yes $ cong token p
... | no ¬p = no  $ ¬p ∘ cong LoginToken.t

open import Twitter LoginToken TweetId new-sid new-pid _≟ₜ_ _≟ₗ_

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
from-input (post-reply tk txt twt)       = publish tk txt (just twt)
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
