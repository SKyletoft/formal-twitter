-- Wire-layer pins of spec/Interface.agda for backend/src/wire.rs (task T2).
-- Each refl theorem fixes one equation of from-input or of to-output, i.e. exactly the
-- behaviour that parse_action + to_command and respond must reproduce byte for byte.
-- A separate module: opening Interface inside ImplProofs would clash with Twitter's
-- Command and Result at the SessionId/PostId instantiation.

module ImplWire where

open import Agda.Builtin.Nat                                using (Nat)
open import Agda.Builtin.Maybe                              using (just; nothing)
open import Data.List                                       using (List)
open import Data.String                                     using (String)
open import Relation.Binary.PropositionalEquality           using (_≡_; refl)
open import Interface
import Twitter LoginToken TweetId new-sid new-pid _≟ₜ_ _≟ₗ_ as TW

-- from-input: all 15 clauses of spec/Interface.agda:from-input, the shape of
-- backend/src/wire.rs:to_command.
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
