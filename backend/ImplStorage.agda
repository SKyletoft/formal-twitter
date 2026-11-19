-- Storage encodings for db.rs (task T3): the integer pins for visibility,
-- post status and session rows, mirroring enc_vis/dec_vis, enc_status/dec_status
-- and enc_sess_row/dec_sess_row. Self-contained: no spec imports.

module ImplStorage where

open import Data.Nat                        using (ℕ; zero; suc)
open import Data.Nat.Properties             using () renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
open import Data.List                       using (List; []; _∷_; map; reverse)
open import Data.Product                    using (_×_; _,_)
open import Data.String                     using (String)
open import Data.Maybe                      using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no)

-- Visibility: Everyone = 0, FollowersOnly = 1; unknown codes decode to Everyone.

data Vis : Set where
  everyone       : Vis
  followers-only : Vis

vis-to-nat : Vis → ℕ
vis-to-nat everyone = zero
vis-to-nat followers-only = suc zero

vis-of : ℕ → Vis
vis-of n with (_≟ℕ_ n (suc zero))
vis-of n | yes _ = followers-only
vis-of n | no _ = everyone

-- Post status: live (Other) = 0, Deleted = 1; unknown codes decode to live.

data St : Set where
  live    : St
  deleted : St

st-to-nat : St → ℕ
st-to-nat live = zero
st-to-nat deleted = suc zero

st-of : ℕ → St
st-of n with (_≟ℕ_ n (suc zero))
st-of n | yes _ = deleted
st-of n | no _ = live

-- Session rows: (1, just u) → active u; (2, nothing) → revoked;
-- anything else is malformed and decodes to revoked (cf. dec_sess_row fallbacks).

data Sess : Set where
  active  : String → Sess
  revoked : Sess

dec-sess : ℕ → Maybe String → Sess
dec-sess zero (just u) = revoked
dec-sess zero nothing = revoked
dec-sess (suc zero) (just u) = active u
dec-sess (suc zero) nothing = revoked
dec-sess (suc (suc n)) u = revoked

-- The encoding pins that db.rs implements.

th-vis-everyone : vis-of (vis-to-nat everyone) ≡ everyone
th-vis-everyone = refl

th-vis-fo : vis-of (vis-to-nat followers-only) ≡ followers-only
th-vis-fo = refl

th-status-live : st-of (st-to-nat live) ≡ live
th-status-live = refl

th-status-deleted : st-of (st-to-nat deleted) ≡ deleted
th-status-deleted = refl

th-sess-active : dec-sess (suc zero) (just "alice") ≡ active "alice"
th-sess-active = refl

th-sess-revoked : dec-sess (suc (suc zero)) nothing ≡ revoked
th-sess-revoked = refl

-- ---- DB row model: load_world ∘ save_world over the six tables (task RV2b) ----
--
-- Backs test_db_empty (db.rs:838), test_db_roundtrip (:846) and test_db_reopen_equal
-- (:858).  Same pipeline as db.rs over row LISTS: save_world wipes and rewrites
-- every table using enc_vis/enc_status/enc_sess_row, so raw rows (R-suffix) carry
-- the on-disk integer codes; load_world re-reads the six tables, sorts each into
-- its canonical order and decodes with dec_vis/dec_status/dec_sess_row, i.e. vis-of
-- / st-of / dec-sess above (dec-sess deviates from Rust only on malformed rows,
-- which no sample here reaches: the (1, just u)/(2, nothing) codes decode exactly).
-- Row shapes and section views mirror the six tables of ImplApply.agda; likes,
-- replies and follows carry no encoded fields (CREATE_SQL, db.rs:114), so their
-- rows ARE the section views.  Sample rows are build_world (= ImplApply's world-B,
-- db.rs:765) and already sit in load_world's canonical sorted order, the same
-- assumption the accepted ImplApply header makes.  Everything is concrete: every
-- theorem below is refl.

-- raw on-disk rows: vis/status/session codes as ℕ

data AccR : Set where
  mk-acc : (username password : String) → (vis : ℕ) → AccR

data SessR : Set where
  mk-sess : (sid : ℕ) → (code : ℕ) → (user : Maybe String) → SessR

data PostR : Set where
  mk-post : (pid : ℕ) → (vis status : ℕ) → (parent : Maybe ℕ) → (seq : ℕ) → PostR

data LikeT : Set where
  mk-like : (pid : ℕ) → (user : String) → LikeT

data ReplyT : Set where
  mk-reply : (pid reply : ℕ) → ReplyT

data FolT : Set where
  mk-fol : (follower followee : String) → FolT

-- decoded section views (the World fields of load_world, before its derive step)

data AccV : Set where
  mk-acc-v : (username password : String) → (v : Vis) → AccV

data SessV : Set where
  mk-sess-v : (sid : ℕ) → (s : Sess) → SessV

data PostV : Set where
  mk-post-v : (pid : ℕ) → (v : Vis) → (st : St) → (parent : Maybe ℕ) → (seq : ℕ) → PostV

-- the World of db.rs as its six stored tables (cf. ImplApply's W; the derived
-- newest_first / used-id lists are recomputed by nf-of and used-* in ImplReload)

data DBW : Set where
  mk-w : (accounts : List AccV) → (sessions : List SessV) → (posts : List PostV)
       → (likes : List LikeT) → (replies : List ReplyT) → (follows : List FolT) → DBW

db-acc-of : DBW → List AccV
db-sess-of : DBW → List SessV
db-post-of : DBW → List PostV
db-like-of : DBW → List LikeT
db-reply-of : DBW → List ReplyT
db-foll-of : DBW → List FolT
db-acc-of (mk-w a _ _ _ _ _) = a
db-sess-of (mk-w _ s _ _ _ _) = s
db-post-of (mk-w _ _ p _ _ _) = p
db-like-of (mk-w _ _ _ l _ _) = l
db-reply-of (mk-w _ _ _ _ r _) = r
db-foll-of (mk-w _ _ _ _ _ f) = f

-- encode/decode between the views and the raw rows (enc_vis/dec_vis etc. above;
-- save_world writes the seq column from w.newest_first, which agrees with the
-- row seq on samples loaded from a DB, so save/load carry seq untouched)

save-acc : AccV → AccR
save-acc (mk-acc-v u p v) = mk-acc u p (vis-to-nat v)

load-acc : AccR → AccV
load-acc (mk-acc u p c) = mk-acc-v u p (vis-of c)

save-sess : SessV → SessR
save-sess (mk-sess-v s (active u)) = mk-sess s (suc zero) (just u)
save-sess (mk-sess-v s revoked)    = mk-sess s (suc (suc zero)) nothing

load-sess : SessR → SessV
load-sess (mk-sess s c u) = mk-sess-v s (dec-sess c u)

save-post : PostV → PostR
save-post (mk-post-v p v s q n) = mk-post p (vis-to-nat v) (st-to-nat s) q n

load-post : PostR → PostV
load-post (mk-post p c c′ q n) = mk-post-v p (vis-of c) (st-of c′) q n

-- ---- load_world's session sort: Vec.sort of the (sid, code, user) tuples; the
-- sample sids are DISTINCT, so insertion sort on the sid key (load_world's
-- canonical ascending order, cf. ImplApply's ins-desc) reproduces it ----

sid-of-db : SessR → ℕ
sid-of-db (mk-sess s _ _) = s

ins-sid : SessR → List SessR → List SessR
ins-sid r [] = r ∷ []
ins-sid r (r′ ∷ rs) with sid-of-db r ≤?ℕ sid-of-db r′
ins-sid r (r′ ∷ rs) | yes _ = r ∷ r′ ∷ rs
ins-sid r (r′ ∷ rs) | no _  = r′ ∷ ins-sid r rs

sort-sid : List SessR → List SessR
sort-sid [] = []
sort-sid (r ∷ rs) = ins-sid r (sort-sid rs)

-- ---- the save/load pipeline of one DB (save-rows then load-rows is one round
-- through the SQLite file; the six raw tables are the file's content) ----

save-rows : DBW → List AccR × (List SessR × (List PostR × (List LikeT × (List ReplyT × List FolT))))
save-rows (mk-w as ss ps ls rs fs) =
    map save-acc as , (map save-sess ss , (map save-post ps , (ls , (rs , fs))))

load-rows : List AccR → List SessR → List PostR → List LikeT → List ReplyT → List FolT → DBW
load-rows as ss ps ls rs fs =
    mk-w (map load-acc as) (map load-sess ss) (map load-post ps) ls rs fs

roundtrip : DBW → DBW
roundtrip w with save-rows w
roundtrip w | as , (ss , (ps , (ls , (rs , fs)))) = load-rows as ss ps ls rs fs

-- ---- the build_world sample rows (db.rs:765 = ImplApply's world-B) ----

accounts-Bd : List AccV
accounts-Bd = mk-acc-v "alice" "a" everyone ∷ mk-acc-v "bob" "b" followers-only ∷ []

sessions-Bd : List SessV
sessions-Bd = mk-sess-v 100 (active "alice") ∷ mk-sess-v 200 revoked ∷ []

posts-Bd : List PostV
posts-Bd = mk-post-v 1 everyone live nothing 1 ∷
           mk-post-v 2 followers-only live (just 1) 2 ∷
           mk-post-v 3 everyone deleted nothing 3 ∷ []

likes-Bd   : List LikeT
likes-Bd   = mk-like 1 "bob" ∷ []

replies-Bd : List ReplyT
replies-Bd = mk-reply 1 2 ∷ []

follows-Bd : List FolT
follows-Bd = mk-fol "alice" "bob" ∷ mk-fol "bob" "alice" ∷ []

world-Bd = mk-w accounts-Bd sessions-Bd posts-Bd likes-Bd replies-Bd follows-Bd
empty-Wd = mk-w [] [] [] [] [] []

-- ---- the theorems: exactly the three T3 gates of db_tests ----

-- test_db_empty (db.rs:838): a fresh DB has NO rows in any table, so load_world
-- gives the empty World: all six sections are [].
th-load-empty : load-rows [] [] [] [] [] [] ≡ empty-Wd
th-load-empty = refl

th-load-empty-accounts : db-acc-of (load-rows [] [] [] [] [] []) ≡ []
th-load-empty-accounts = refl

th-load-empty-sessions : db-sess-of (load-rows [] [] [] [] [] []) ≡ []
th-load-empty-sessions = refl

th-load-empty-posts : db-post-of (load-rows [] [] [] [] [] []) ≡ []
th-load-empty-posts = refl

th-load-empty-likes : db-like-of (load-rows [] [] [] [] [] []) ≡ []
th-load-empty-likes = refl

th-load-empty-replies : db-reply-of (load-rows [] [] [] [] [] []) ≡ []
th-load-empty-replies = refl

th-load-empty-follows : db-foll-of (load-rows [] [] [] [] [] []) ≡ []
th-load-empty-follows = refl

-- test_db_roundtrip (db.rs:846): save_world(build_world), then reopen + load_world
-- reproduces the World exactly (one tuple equality = World's componentwise ==).
th-load-save-roundtrip : roundtrip world-Bd ≡ world-Bd
th-load-save-roundtrip = refl

-- test_db_reopen_equal (db.rs:858): two reopen+load passes read the SAME rows off
-- one file.  load_world sorts each table back into its canonical order (load-rows
-- is a pure map over the sorted rows, and the sort is the identity on save_world's
-- canonical row order), so the load is DETERMINISTIC in the row lists and the two
-- loads agree.  Pinned here: decoding the sessions commutes with the sid sort even
-- for a scrambled re-read (reverse below), hence both reads give one section.
th-load-deterministic :
  map load-sess (sort-sid (reverse (map save-sess sessions-Bd))) ≡
  map load-sess (sort-sid (map save-sess sessions-Bd))
th-load-deterministic = refl
