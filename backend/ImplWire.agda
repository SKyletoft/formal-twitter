-- Wire-layer pins of spec/Interface.agda for backend/src/wire.rs (task T2).
-- Each refl theorem fixes one equation of from-input or of to-output, i.e. exactly the
-- behaviour that parse_action + to_command and respond must reproduce byte for byte.
-- A separate module: opening Interface inside ImplProofs would clash with Twitter's
-- Command and Result at the SessionId/PostId instantiation.

module ImplWire where

open import Agda.Builtin.Nat                                using (Nat)
open import Agda.Builtin.Maybe                              using (just; nothing)
open import Data.List                                       using (List; []; _∷_)
open import Data.String                                     using (String)
open import Relation.Binary.PropositionalEquality           using (_≡_; refl)
open import Interface
import Twitter LoginToken TweetId new-sid new-pid _≟ₜ_ _≟ₗ_ as TW

-- from-input: all 15 clauses of spec/Interface.agda:from-input, the shape of
-- backend/src/wire.rs:to_command.
-- Task T6 adds no clause here: the legacy frontend's GET aliases
-- (backend/src/main.rs:query_param + alias_body + serve_alias) rebuild the POST-
-- equivalent body from the query parameters and then feed the self-same parse_action
-- + to_command, so each alias denotes exactly one request name above, the token
-- parameter being the Maybe token these three clauses already consume.  The byte
-- equality of the two transports is pinned in backend/src/main.rs (test_alias_*) and
-- over the network in backend/tests/smoke.rs (test_get_alias_roundtrip).
wi-post-tweet : ∀ (tk : LoginToken) (txt : String) →
        from-input (post-tweet tk txt) ≡ TW.publish tk txt nothing
wi-post-tweet tk txt = refl

wi-post-reply : ∀ (tk : LoginToken) (txt : String) (twt : TweetId) →
        from-input (post-reply tk txt twt) ≡ TW.publish tk txt (just twt)
wi-post-reply tk txt twt = refl

wi-delete-tweet : ∀ (tk : LoginToken) (twt : TweetId) →
        from-input (delete-tweet tk twt) ≡ TW.delete tk twt
wi-delete-tweet tk twt = refl

wi-like : ∀ (tk : LoginToken) (twt : TweetId) →
        from-input (like tk twt) ≡ TW.like tk twt
wi-like tk twt = refl

wi-unlike : ∀ (tk : LoginToken) (twt : TweetId) →
        from-input (unlike tk twt) ≡ TW.unlike tk twt
wi-unlike tk twt = refl

wi-follow : ∀ (tk : LoginToken) (u : String) →
        from-input (follow tk u) ≡ TW.follow tk u
wi-follow tk u = refl

wi-unfollow : ∀ (tk : LoginToken) (u : String) →
        from-input (unfollow tk u) ≡ TW.unfollow tk u
wi-unfollow tk u = refl

wi-get-tweet-token : ∀ (tk : LoginToken) (twt : TweetId) →
        from-input (get-tweet (just tk) twt) ≡ TW.read-post (just tk) twt
wi-get-tweet-token tk twt = refl

wi-get-tweet-anon : ∀ (twt : TweetId) →
        from-input (get-tweet nothing twt) ≡ TW.read-post nothing twt
wi-get-tweet-anon twt = refl

wi-global-timeline-token : ∀ (tk : LoginToken) (n : Nat) →
        from-input (global-timeline (just tk) n) ≡ TW.read-global-timeline (just tk) n
wi-global-timeline-token tk n = refl

wi-global-timeline-anon : ∀ (n : Nat) →
        from-input (global-timeline nothing n) ≡ TW.read-global-timeline nothing n
wi-global-timeline-anon n = refl

wi-private-timeline : ∀ (tk : LoginToken) (n : Nat) →
        from-input (private-timeline tk n) ≡ TW.read-personal-timeline tk n
wi-private-timeline tk n = refl

wi-login : ∀ (u p : String) →
        from-input (login u p) ≡ TW.authenticate u p
wi-login u p = refl

wi-signup : ∀ (u p : String) →
        from-input (signup u p) ≡ TW.register u p
wi-signup u p = refl

wi-logout : ∀ (tk : LoginToken) →
        from-input (logout tk) ≡ TW.revoke-token tk
wi-logout tk = refl

-- to-output: all 9 clauses of spec/Interface.agda:to-output, the shape of
-- backend/src/wire.rs:respond (status line, header order and body bytes).
wi-out-success : to-output (TW.success) ≡ ok
wi-out-success = refl

wi-out-denied : to-output (TW.denied) ≡ permission-error
wi-out-denied = refl

wi-out-expired : to-output (TW.expired) ≡ outdated-login-token
wi-out-expired = refl

wi-out-login-failed : to-output (TW.login-failed) ≡ login-error
wi-out-login-failed = refl

wi-out-signup-failed : to-output (TW.signup-failed) ≡ signup-error
wi-out-signup-failed = refl

wi-out-timeline : ∀ (xs : List TweetId) →
        to-output (TW.returned-timeline xs) ≡ timeline xs
wi-out-timeline xs = refl

wi-out-session : ∀ (x : LoginToken) →
        to-output (TW.issued-session x) ≡ session-token x
wi-out-session x = refl

wi-out-created : ∀ (twt : TweetId) →
        to-output (TW.created-post twt) ≡ tweet-id twt
wi-out-created twt = refl

wi-out-post : ∀ (a t : String) (l : Nat) (r : List TweetId) →
        to-output (TW.returned-post a t l r) ≡ tweet a t l r
wi-out-post a t l r = refl

-- to-response pins (wi-resp-*): audit M4.  One refl theorem per Response constructor
-- exercised by backend/src/wire.rs:respond_shapes, pinning the whole clause of
-- spec/Interface.agda:to-response with the let-bound body inlined.  Plain refl pins the
-- literal status line (200 OK / 403 Forbidden / 401 Unauthorized / 400 Bad Request), the
-- header LIST (order of Date / Cache-Control / Content-Type), the
-- "Content-Length: " ++ show (octet-strlen ...) term and the exact body expression:
-- the fields Rust respond stores in status_code, headers and body.  unlines-crlf is
-- postulated, so the flat wire BYTES are opaque and cannot be refl'd; the commented
-- wi-bytes-* signatures below STATE that claim instead, and respond_shapes asserts the
-- concrete bytes on the Rust side.

wi-resp-ok : to-response ok ≡
        unlines-crlf ( "HTTP/1.1 200 OK"
          ∷ "Date: " ++ date
          ∷ "Content-Length: 0"
          ∷ ""
          ∷ [] )
wi-resp-ok = refl

wi-resp-denied : to-response permission-error ≡
        unlines-crlf ( "HTTP/1.1 403 Forbidden"
          ∷ "Date: " ++ date
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen "{\"error\": \"access_denied\"}")
          ∷ ""
          ∷ "{\"error\": \"access_denied\"}"
          ∷ [] )
wi-resp-denied = refl

wi-resp-expired : to-response outdated-login-token ≡
        unlines-crlf ( "HTTP/1.1 401 Unauthorized"
          ∷ "Date: " ++ date
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen "{\"error\": \"session_expired\"}")
          ∷ ""
          ∷ "{\"error\": \"session_expired\"}"
          ∷ [] )
wi-resp-expired = refl

wi-resp-login-failed : to-response login-error ≡
        unlines-crlf ( "HTTP/1.1 401 Unauthorized"
          ∷ "Date: " ++ date
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen "{\"error\": \"login_failed\"}")
          ∷ ""
          ∷ "{\"error\": \"login_failed\"}"
          ∷ [] )
wi-resp-login-failed = refl

wi-resp-signup-failed : to-response signup-error ≡
        unlines-crlf ( "HTTP/1.1 400 Bad Request"
          ∷ "Date: " ++ date
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen "{\"error\": \"signup_failed\"}")
          ∷ ""
          ∷ "{\"error\": \"signup_failed\"}"
          ∷ [] )
wi-resp-signup-failed = refl

wi-resp-created : ∀ (n : Nat) →
        to-response (tweet-id (tweet-id n)) ≡
        unlines-crlf ( "HTTP/1.1 200 OK"
          ∷ "Date: " ++ date
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen ("{\"tweet_id\": \"" ++ show n ++ "\"}"))
          ∷ ""
          ∷ "{\"tweet_id\": \"" ++ show n ++ "\"}"
          ∷ [] )
wi-resp-created n = refl

wi-resp-session : ∀ (n : Nat) →
        to-response (session-token (token n)) ≡
        unlines-crlf ( "HTTP/1.1 200 OK"
          ∷ "Date: " ++ date
          ∷ "Cache-Control: no-store"
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen ("{\"session_token\": \"" ++ show n ++ "\"}"))
          ∷ ""
          ∷ "{\"session_token\": \"" ++ show n ++ "\"}"
          ∷ [] )
wi-resp-session n = refl

wi-resp-timeline : ∀ (xs : List TweetId) →
        to-response (timeline xs) ≡
        unlines-crlf ( "HTTP/1.1 200 OK"
          ∷ "Date: " ++ date
          ∷ "Cache-Control: no-store"
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen ("{\"timeline\": [" ++ show-tweets xs ++ "]}"))
          ∷ ""
          ∷ "{\"timeline\": [" ++ show-tweets xs ++ "]}"
          ∷ [] )
wi-resp-timeline xs = refl

wi-resp-post : ∀ (a t : String) (l : Nat) (r : List TweetId) →
        to-response (tweet a t l r) ≡
        unlines-crlf ( "HTTP/1.1 200 OK"
          ∷ "Date: " ++ date
          ∷ "Cache-Control: no-store"
          ∷ "Content-Type: application/json"
          ∷ "Content-Length: " ++ show (octet-strlen ("{\"username\": \"" ++ escape a ++ "\", \"text\": \"" ++ escape t ++ "\", \"likes\": " ++ show l ++ ", \"replies\": [" ++ show-tweets r ++ "]}"))
          ∷ ""
          ∷ "{\"username\": \"" ++ escape a ++ "\", \"text\": \"" ++ escape t ++ "\", \"likes\": " ++ show l ++ ", \"replies\": [" ++ show-tweets r ++ "]}"
          ∷ [] )
wi-resp-post a t l r = refl

-- Opaque framing, STATED ONLY (commented postulate signatures: unlines-crlf has no
-- definition so these are unprovable; respond_shapes asserts the same concrete
-- bytes, and the numbers are the octet-strlen of each body):
-- postulate
--   wi-bytes-ok     : to-response ok ≡
--     "HTTP/1.1 200 OK\r\nDate: " ++ date ++ "\r\nContent-Length: 0\r\n\r\n"
--   wi-bytes-denied : to-response permission-error ≡
--     "HTTP/1.1 403 Forbidden\r\nDate: " ++ date ++ "\r\nContent-Type: application/json\r\nContent-Length: 26\r\n\r\n{\"error\": \"access_denied\"}"
--   wi-bytes-expired : to-response outdated-login-token ≡
--     "HTTP/1.1 401 Unauthorized\r\nDate: " ++ date ++ "\r\nContent-Type: application/json\r\nContent-Length: 28\r\n\r\n{\"error\": \"session_expired\"}"
--   wi-bytes-login-failed : to-response login-error ≡
--     "HTTP/1.1 401 Unauthorized\r\nDate: " ++ date ++ "\r\nContent-Type: application/json\r\nContent-Length: 25\r\n\r\n{\"error\": \"login_failed\"}"
--   wi-bytes-signup-failed : to-response signup-error ≡
--     "HTTP/1.1 400 Bad Request\r\nDate: " ++ date ++ "\r\nContent-Type: application/json\r\nContent-Length: 26\r\n\r\n{\"error\": \"signup_failed\"}"
--   wi-bytes-created : to-response (tweet-id (tweet-id 42)) ≡
--     "HTTP/1.1 200 OK\r\nDate: " ++ date ++ "\r\nContent-Type: application/json\r\nContent-Length: 18\r\n\r\n{\"tweet_id\": \"42\"}"
--   wi-bytes-session : to-response (session-token (token 9)) ≡
--     "HTTP/1.1 200 OK\r\nDate: " ++ date ++ "\r\nCache-Control: no-store\r\nContent-Type: application/json\r\nContent-Length: 22\r\n\r\n{\"session_token\": \"9\"}"
--   wi-bytes-timeline : to-response (timeline []) ≡
--     "HTTP/1.1 200 OK\r\nDate: " ++ date ++ "\r\nCache-Control: no-store\r\nContent-Type: application/json\r\nContent-Length: 16\r\n\r\n{\"timeline\": []}"
--   The tweet case additionally depends on the opaque escape postulate: respond_shapes
--   pins it for the fixture a = a"b / t = c\nd / l = 3 / r = [1, 2].
