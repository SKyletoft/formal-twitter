-- Per-section reload pins for backend/src/db.rs's reload_* functions (task DB3b).
-- Models load_world/reload as "re-query ONE section of the RAM cache from the DB":
-- reload-accounts replaces only the accounts table, reload-sessions replaces
-- sessions together with the derived used_session_ids, reload-follows replaces
-- follows, and reload-posts moves posts + newest_first + used_post_ids as ONE
-- section (all three derive from the posts/likes/replies tables, so they must
-- move together).  Rows, accessors and the sample worlds come from backend/ImplApply.agda
-- (the same build_world/build_after pair db.rs's db_tests use); nf-of is load_world's
-- ORDER BY seq DESC.  The *-tampered caches below are exactly the RAM lies the four
-- db.rs reload tests plant, so every theorem below is a concrete refl check.

module ImplReload where

open import Data.Nat                              using (ℕ; zero; suc)
open import Data.List                             using (List; []; _∷_; _++_; map)
open import Data.Product                          using (_×_; _,_)
open import Agda.Builtin.Maybe                      using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ImplApply

-- ---- the four reload views of db.rs (each keeps the other sections cached) ----

reload-accounts : List ARow → W → W
reload-accounts rows (world a s p l r f) = world rows s p l r f

reload-sessions : List SRow → W → W
reload-sessions rows (world a s p l r f) = world a rows p l r f

reload-follows : List FRow → W → W
reload-follows rows (world a s p l r f) = world a s p l r rows

reload-posts : List PRow → List LRow → List RRow → W → W
reload-posts ps ls rs (world a s p l r f) = world a s ps ls rs f

-- used-post/session ids are not stored: load_world (and reload_*) derives them
-- from the keys of the rows it just re-read.

used-sids : List SRow → List ℕ
used-sids rs = map sid-of rs

used-pids : List PRow → List ℕ
used-pids rs = map pid-of rs

-- ---- the RAM lies the four db_tests reload tests plant ----

accounts-tampered : List ARow
accounts-tampered = arow "alice" "LIE" everyone ∷ []
world-accounts-tampered : W
world-accounts-tampered =
  world accounts-tampered sessions-B posts-B likes-B replies-B follows-B

sessions-tampered : List SRow
sessions-tampered = srow 100 unused ∷ []
used-sids-tampered : List ℕ
used-sids-tampered = 100 ∷ 999 ∷ []
world-sessions-tampered : W
world-sessions-tampered =
  world accounts-B sessions-tampered posts-B likes-B replies-B follows-B

follows-tampered : List FRow
follows-tampered = frow "ghost" "alice" ∷ []
world-follows-tampered : W
world-follows-tampered =
  world accounts-B sessions-B posts-B likes-B replies-B follows-tampered

posts-tampered : List PRow
posts-tampered =
  prow 1 everyone live nothing 1 ∷ prow 2 followers-only live (just 1) 2 ∷ []
-- NB (task RV2f): db.rs test_reload_posts also plants the RAM lies
-- newest_first = [9,8] and used_post_ids = [9,8] (src/db.rs:1120-1121), but W
-- (ImplApply:235) carries NO nf/used cache fields: nf-of and used-pids are
-- recomputed from the post rows, so those lies cannot be planted here and are
-- not modelled as separate values (they were dead defs, removed in RV2f).
-- th-reload-posts below already feeds the TAMPERED section (posts-tampered via
-- world-posts-tampered) and pins the restored rows + nf ≡ 3∷2∷1, and
-- th-reload-posts-used pins the restored used ≡ 1∷2∷3 - exactly src/db.rs:1126-1128.
world-posts-tampered : W
world-posts-tampered =
  world accounts-B sessions-B posts-tampered likes-B replies-B follows-B

-- ---- the reload theorems: the reloaded section is the DB rows, the rest stays cached ----

th-reload-accounts :
  acc-of (reload-accounts accounts-B world-accounts-tampered) ≡ acc-of world-B
th-reload-accounts = refl

th-reload-accounts-rest :
  reload-accounts accounts-B world-accounts-tampered ≡ world-B
th-reload-accounts-rest = refl

-- ---- th-reload-sessions: db.rs test_reload_sessions (sessions AND used_session_ids) ----

th-reload-sessions :
  sess-of (reload-sessions sessions-B world-sessions-tampered) ≡ sess-of world-B
th-reload-sessions = refl

th-reload-sessions-used :
  used-sids (sess-of (reload-sessions sessions-B world-sessions-tampered)) ≡
  100 ∷ 200 ∷ []
th-reload-sessions-used = refl

th-reload-sessions-rest :
  reload-sessions sessions-B world-sessions-tampered ≡ world-B
th-reload-sessions-rest = refl

-- ---- th-reload-follows: db.rs test_reload_follows ----

th-reload-follows :
  foll-of (reload-follows follows-B world-follows-tampered) ≡ foll-of world-B
th-reload-follows = refl

th-reload-follows-rest :
  reload-follows follows-B world-follows-tampered ≡ world-B
th-reload-follows-rest = refl

-- ---- th-reload-posts: db.rs test_reload_posts (posts + newest_first + used_post_ids) ----

-- the posts section is a PAIR: the rows and load_world's ORDER BY seq DESC timeline
-- move together, which is what the reload-posts view below computes.

posts-section : List PRow → List LRow → List RRow → W → List PRow × List ℕ
posts-section ps ls rs w = post-of (reload-posts ps ls rs w) , nf-of (post-of (reload-posts ps ls rs w))

th-reload-posts :
  posts-section posts-B likes-B replies-B world-posts-tampered ≡
  ( posts-B , 3 ∷ 2 ∷ 1 ∷ [] )
th-reload-posts = refl

th-reload-posts-used :
  used-pids (post-of (reload-posts posts-B likes-B replies-B world-posts-tampered)) ≡
  1 ∷ 2 ∷ 3 ∷ []
th-reload-posts-used = refl

th-reload-posts-rest :
  reload-posts posts-B likes-B replies-B world-posts-tampered ≡ world-B
th-reload-posts-rest = refl

