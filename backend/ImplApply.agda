-- Bounded write-through pins for backend/src/db.rs:apply (task T4a).
-- Models the six DB tables as association lists over the sample worlds of
-- backend/src/db.rs:mod db_tests (build_world = BEFORE, build_after = AFTER) and
-- reproduces apply()'s clause structure: accounts INSERT/DELETE by username,
-- sessions INSERT/UPDATE(status)/DELETE by sid, posts INSERT with seq = (max DB
-- seq) + 1 growing per insert / UPDATE on status+visibility flip / DELETE by pid
-- (which also sweeps that pid's likes and replies), and pair INSERT/DELETE for
-- likes, replies and follows.  Everything is concrete, so every theorem below
-- is refl; no postulates.
--
-- The rows carry only the fields apply() reads or writes (author/text are never
-- touched by the diff, so they are elided); load_world's row sort is mirrored by
-- building the result as "before-rows kept in order ++ after-rows inserted in
-- order", which is the canonical ascending key order in both sample worlds.

module ImplApply where

open import Data.Nat                                using (ℕ; zero; suc)
open import Data.Nat.Properties                     using () renaming (_≟_ to _≟ℕ_; _≥?_ to _≥?ℕ_)
open import Data.String                             using (String; _≟_)
open import Agda.Builtin.Bool                       using (Bool; true; false)
open import Data.Bool                               using (not)
open import Agda.Builtin.Maybe                      using (Maybe; just; nothing)
open import Data.List                               using (List; []; _∷_; _++_; map)
open import Relation.Binary.PropositionalEquality   using (_≡_; refl)
open import Relation.Nullary.Decidable.Core         using (yes; no)

-- ---- row shapes (the six tables of db.rs, apply()'s fields only) ----

data Vis : Set where
  everyone       : Vis
  followers-only : Vis

data St : Set where
  live    : St
  deleted : St

data Sess : Set where
  active  : String → Sess
  revoked : Sess
  unused  : Sess

data ARow : Set where
  arow : (username password : String) → (v : Vis) → ARow

data SRow : Set where
  srow : (sid : ℕ) → (s : Sess) → SRow

data PRow : Set where
  prow : (pid : ℕ) → (v : Vis) → (st : St) → (parent : Maybe ℕ) → (seq : ℕ) → PRow

data LRow : Set where
  lrow : (pid : ℕ) → (user : String) → LRow

data RRow : Set where
  rrow : (pid reply : ℕ) → RRow

data FRow : Set where
  frow : (follower followee : String) → FRow

-- ---- accessors ----

uname-of : ARow → String
uname-of (arow u _ _) = u

sid-of : SRow → ℕ
sid-of (srow s _) = s

pid-of : PRow → ℕ
pid-of (prow p _ _ _ _) = p

vis-of : PRow → Vis
vis-of (prow _ v _ _ _) = v

st-of : PRow → St
st-of (prow _ _ s _ _) = s

parent-of : PRow → Maybe ℕ
parent-of (prow _ _ _ p _) = p

seq-of : PRow → ℕ
seq-of (prow _ _ _ _ q) = q

set-seq : PRow → ℕ → PRow
set-seq (prow p v s q _) n = prow p v s q n

lpid-of : LRow → ℕ
lu-of : LRow → String
lpid-of (lrow p _) = p
lu-of (lrow _ u) = u

rpid-of : RRow → ℕ
rp-of : RRow → ℕ
rpid-of (rrow p _) = p
rp-of (rrow _ r) = r

ff-of : FRow → String
fe-of : FRow → String
ff-of (frow f _) = f
fe-of (frow _ e) = e

-- ---- decidable membership (the HashMap/HashSet probes in apply) ----

key∈ : ℕ → List ℕ → Bool
key∈ k [] = false
key∈ k (k′ ∷ ks) with k ≟ℕ k′
key∈ k (k′ ∷ ks) | yes _ = true
key∈ k (k′ ∷ ks) | no _  = key∈ k ks

str∈ : String → List String → Bool
str∈ s [] = false
str∈ s (s′ ∷ ss) with s ≟ s′
str∈ s (s′ ∷ ss) | yes _ = true
str∈ s (s′ ∷ ss) | no _  = str∈ s ss

∈-like : LRow → List LRow → Bool
∈-like r [] = false
∈-like (lrow p u) (lrow p₁ u₁ ∷ rs) with p ≟ℕ p₁ | u ≟ u₁
∈-like (lrow p u) (lrow p₁ u₁ ∷ rs) | yes _ | yes _ = true
∈-like (lrow p u) (lrow p₁ u₁ ∷ rs) | yes _ | no _  = ∈-like (lrow p u) rs
∈-like (lrow p u) (lrow p₁ u₁ ∷ rs) | no _  | _     = ∈-like (lrow p u) rs

∈-reply : RRow → List RRow → Bool
∈-reply r [] = false
∈-reply (rrow p q) (rrow p₁ q₁ ∷ rs) with p ≟ℕ p₁ | q ≟ℕ q₁
∈-reply (rrow p q) (rrow p₁ q₁ ∷ rs) | yes _ | yes _ = true
∈-reply (rrow p q) (rrow p₁ q₁ ∷ rs) | yes _ | no _  = ∈-reply (rrow p q) rs
∈-reply (rrow p q) (rrow p₁ q₁ ∷ rs) | no _  | _     = ∈-reply (rrow p q) rs

∈-follow : FRow → List FRow → Bool
∈-follow r [] = false
∈-follow (frow f e) (frow f₁ e₁ ∷ rs) with f ≟ f₁ | e ≟ e₁
∈-follow (frow f e) (frow f₁ e₁ ∷ rs) | yes _ | yes _ = true
∈-follow (frow f e) (frow f₁ e₁ ∷ rs) | yes _ | no _  = ∈-follow (frow f e) rs
∈-follow (frow f e) (frow f₁ e₁ ∷ rs) | no _  | _     = ∈-follow (frow f e) rs

-- ---- bounded filter (O(rows) over the canonical row order) ----

flt : {A : Set} → (A → Bool) → List A → List A
flt p [] = []
flt p (x ∷ xs) with p x
flt p (x ∷ xs) | true = x ∷ flt p xs
flt p (x ∷ xs) | false = flt p xs

-- ---- lookups (HashMap.get in apply) ----

sess-at : ℕ → List SRow → Maybe Sess
sess-at k [] = nothing
sess-at k (srow k′ s ∷ rs) with k ≟ℕ k′
sess-at k (srow k′ s ∷ rs) | yes _ = just s
sess-at k (srow k′ s ∷ rs) | no _  = sess-at k rs

post-at : ℕ → List PRow → Maybe PRow
post-at k [] = nothing
post-at k (r ∷ rs) with k ≟ℕ pid-of r
post-at k (r ∷ rs) | yes _ = just r
post-at k (r ∷ rs) | no _  = post-at k rs

st-at : ℕ → List PRow → Maybe St
st-at k rs with post-at k rs
st-at k rs | just r = just (st-of r)
st-at k rs | nothing = nothing

seq-at : ℕ → List PRow → Maybe ℕ
seq-at k rs with post-at k rs
seq-at k rs | just r = just (seq-of r)
seq-at k rs | nothing = nothing

parent-at : ℕ → List PRow → Maybe (Maybe ℕ)
parent-at k rs with post-at k rs
parent-at k rs | just r = just (parent-of r)
parent-at k rs | nothing = nothing

-- ---- next_seq: apply loads the DB's seqs and folds (s ≥ n) → s +1 ----

-- apply's fold over the loaded seqs: next_seq starts at 1 and each s ≥ next_seq
-- bumps it by one (left-to-right, exactly the Rust loop).
step-next-seq : ℕ → List ℕ → ℕ
step-next-seq n [] = n
step-next-seq n (q ∷ qs) with q ≥?ℕ n
step-next-seq n (q ∷ qs) | yes _ = step-next-seq (suc n) qs
step-next-seq n (q ∷ qs) | no _  = step-next-seq n qs

-- ---- the six per-table diffs of apply ----

post-update : List PRow → PRow → PRow
post-update rows r with post-at (pid-of r) rows
post-update rows r | just r′ = prow (pid-of r) (vis-of r′) (st-of r′) (parent-of r) (seq-of r)
post-update rows r | nothing = r

stamped : List PRow → ℕ → List PRow
stamped [] _ = []
stamped (r ∷ rs) n = set-seq r n ∷ stamped rs (suc n)

apply-accounts : List ARow → List ARow → List ARow
apply-accounts before after =
    flt (λ r → str∈ (uname-of r) (map uname-of after)) before
 ++ flt (λ r → not (str∈ (uname-of r) (map uname-of before))) after

apply-sessions : List SRow → List SRow → List SRow
apply-sessions before after =
    map (sess-update after)
        (flt (λ r → key∈ (sid-of r) (map sid-of after)) before)
 ++ flt (λ r → not (key∈ (sid-of r) (map sid-of before))) after
  where
  sess-update : List SRow → SRow → SRow
  sess-update rows r with sess-at (sid-of r) rows
  sess-update rows r | just s = srow (sid-of r) s
  sess-update rows r | nothing = r

apply-posts : List PRow → List PRow → List PRow
apply-posts before after =
    map (post-update after)
        (flt (λ r → key∈ (pid-of r) (map pid-of after)) before)
 ++ stamped (flt (λ r → not (key∈ (pid-of r) (map pid-of before))) after)
          (step-next-seq (suc zero) (map seq-of before))

apply-likes : List LRow → List LRow → List LRow
apply-likes before after =
    flt (λ r → ∈-like r after) before
 ++ flt (λ r → not (∈-like r before)) after

apply-replies : List RRow → List RRow → List RRow
apply-replies before after =
    flt (λ r → ∈-reply r after) before
 ++ flt (λ r → not (∈-reply r before)) after

apply-follows : List FRow → List FRow → List FRow
apply-follows before after =
    flt (λ r → ∈-follow r after) before
 ++ flt (λ r → not (∈-follow r before)) after

-- ---- the World of db.rs, as the six tables ----

data W : Set where
  world : (accounts : List ARow) → (sessions : List SRow) → (posts : List PRow)
        → (likes : List LRow) → (replies : List RRow) → (follows : List FRow) → W

acc-of : W → List ARow
sess-of : W → List SRow
post-of : W → List PRow
like-of : W → List LRow
reply-of : W → List RRow
foll-of : W → List FRow
acc-of (world a _ _ _ _ _) = a
sess-of (world _ s _ _ _ _) = s
post-of (world _ _ p _ _ _) = p
like-of (world _ _ _ l _ _) = l
reply-of (world _ _ _ _ r _) = r
foll-of (world _ _ _ _ _ f) = f

apply-diff : W → W → W
apply-diff (world a s p l r f) (world a′ s′ p′ l′ r′ f′) =
  world (apply-accounts a a′) (apply-sessions s s′) (apply-posts p p′)
        (apply-likes l l′) (apply-replies r r′) (apply-follows f f′)

-- newest-first: load_world's ORDER BY seq DESC (insertion sort, stable on the
-- distinct seqs that apply stamps).

ins-desc : PRow → List PRow → List PRow
ins-desc r [] = r ∷ []
ins-desc r (s ∷ ss) with seq-of r ≥?ℕ seq-of s
ins-desc r (s ∷ ss) | yes _ = r ∷ s ∷ ss
ins-desc r (s ∷ ss) | no _  = s ∷ ins-desc r ss

sort-desc : List PRow → List PRow
sort-desc [] = []
sort-desc (r ∷ rs) = ins-desc r (sort-desc rs)

nf-of : List PRow → List ℕ
nf-of rs = map pid-of (sort-desc rs)

-- ---- the two sample worlds of db_tests: build_world (BEFORE) and build_after (AFTER)

accounts-B = arow "alice" "a" everyone ∷ arow "bob" "b" followers-only ∷ []
sessions-B = srow 100 (active "alice") ∷ srow 200 revoked ∷ []
posts-B    = prow 1 everyone live nothing 1 ∷
             prow 2 followers-only live (just 1) 2 ∷
             prow 3 everyone deleted nothing 3 ∷ []
likes-B    = lrow 1 "bob" ∷ []
replies-B  = rrow 1 2 ∷ []
follows-B  = frow "alice" "bob" ∷ frow "bob" "alice" ∷ []

accounts-A = arow "alice" "a" everyone ∷ arow "bob" "b" followers-only ∷
             arow "zoe" "z" everyone ∷ []
sessions-A = srow 100 revoked ∷ srow 300 unused ∷ []
posts-A    = prow 1 everyone live nothing 1 ∷
             prow 2 followers-only deleted (just 1) 2 ∷
             prow 3 everyone deleted nothing 3 ∷
             prow 500 everyone live (just 1) 4 ∷ []
likes-A    = lrow 1 "bob" ∷ lrow 1 "carol" ∷ []
replies-A  = rrow 1 2 ∷ rrow 1 500 ∷ []
follows-A  = frow "alice" "bob" ∷ frow "carol" "alice" ∷ []

world-B = world accounts-B sessions-B posts-B likes-B replies-B follows-B
world-A = world accounts-A sessions-A posts-A likes-A replies-A follows-A
empty-W = world [] [] [] [] [] []

-- ---- theorems: exactly what test_apply_inserts_all and test_apply_diff assert ----

-- test_apply_inserts_all: apply from the wiped DB reloads as `after` (= build_world),
-- so every table of the diff equals the build_world rows.
th-apply-empty-world : apply-diff empty-W world-B ≡ world-B
th-apply-empty-world = refl

-- per-table versions of the same gate (test_apply_inserts_all checks load_world == after)
th-apply-empty-accounts : apply-accounts [] accounts-B ≡ accounts-B
th-apply-empty-accounts = refl

th-apply-empty-posts : nf-of (apply-posts [] posts-B) ≡ 3 ∷ 2 ∷ 1 ∷ []
th-apply-empty-posts = refl

th-apply-empty-likes : apply-likes [] likes-B ≡ likes-B
th-apply-empty-likes = refl

th-apply-empty-follows : apply-follows [] follows-B ≡ follows-B
th-apply-empty-follows = refl

-- test_apply_diff: reload == after for every table (the six whole-table pins below).
th-accounts-table : acc-of (apply-diff world-B world-A) ≡ accounts-A
th-accounts-table = refl

th-sessions-table : sess-of (apply-diff world-B world-A) ≡ sessions-A
th-sessions-table = refl

th-posts-table : post-of (apply-diff world-B world-A) ≡ posts-A
th-posts-table = refl

th-likes-table : like-of (apply-diff world-B world-A) ≡ likes-A
th-likes-table = refl

th-replies-table : reply-of (apply-diff world-B world-A) ≡ replies-A
th-replies-table = refl

th-follows-table : foll-of (apply-diff world-B world-A) ≡ follows-A
th-follows-table = refl

-- sessions: sid 100 kept (UPDATE Active→Revoked), sid 200 DELETEd, sid 300 INSERTed Unused
th-sess-100-updated : sess-at 100 (apply-sessions sessions-B sessions-A) ≡ just revoked
th-sess-100-updated = refl

th-sess-200-dropped : sess-at 200 (apply-sessions sessions-B sessions-A) ≡ nothing
th-sess-200-dropped = refl

th-sess-300-inserted : sess-at 300 (apply-sessions sessions-B sessions-A) ≡ just unused
th-sess-300-inserted = refl

-- posts: max(before seq) = 3, so the one new pid gets seq = 3 + 1
th-max-seq-before : step-next-seq (suc zero) (map seq-of posts-B) ≡ 4
th-max-seq-before = refl

-- pid 1 keeps its live status (its likes/replies gained, status untouched)
th-post-1-live : st-at 1 (apply-posts posts-B posts-A) ≡ just live
th-post-1-live = refl

th-post-2-updated : st-at 2 (apply-posts posts-B posts-A) ≡ just deleted
th-post-2-updated = refl

th-post-3-status : st-at 3 (apply-posts posts-B posts-A) ≡ just deleted
th-post-3-status = refl

th-post-500-inserted : st-at 500 (apply-posts posts-B posts-A) ≡ just live
th-post-500-inserted = refl

th-post-500-seq : seq-at 500 (apply-posts posts-B posts-A) ≡ just 4
th-post-500-seq = refl

-- existing seqs stay put (nothing is rewritten)
th-post-1-seq-kept : seq-at 1 (apply-posts posts-B posts-A) ≡ just 1
th-post-1-seq-kept = refl

th-post-2-seq-kept : seq-at 2 (apply-posts posts-B posts-A) ≡ just 2
th-post-2-seq-kept = refl

-- load_world(&conn).newest_first == [500,3,2,1]
th-newest-first-after : nf-of (apply-posts posts-B posts-A) ≡ 500 ∷ 3 ∷ 2 ∷ 1 ∷ []
th-newest-first-after = refl

-- posts[3].1.parent == Some(1): the INSERT keeps after's parent, the UPDATE keeps the
-- before parent of pid 2.
th-parent-500 : parent-at 500 (apply-posts posts-B posts-A) ≡ just (just 1)
th-parent-500 = refl

th-parent-2-kept : parent-at 2 (apply-posts posts-B posts-A) ≡ just (just 1)
th-parent-2-kept = refl

-- likes/replies pair deltas
th-like-kept : ∈-like (lrow 1 "bob") (apply-likes likes-B likes-A) ≡ true
th-like-kept = refl

th-like-added : ∈-like (lrow 1 "carol") (apply-likes likes-B likes-A) ≡ true
th-like-added = refl

th-reply-kept : ∈-reply (rrow 1 2) (apply-replies replies-B replies-A) ≡ true
th-reply-kept = refl

th-reply-added : ∈-reply (rrow 1 500) (apply-replies replies-B replies-A) ≡ true
th-reply-added = refl

-- follows delta: (bob,alice) DELETEd, (carol,alice) INSERTed, (alice,bob) kept
th-follow-kept : ∈-follow (frow "alice" "bob") (apply-follows follows-B follows-A) ≡ true
th-follow-kept = refl

th-follow-added : ∈-follow (frow "carol" "alice") (apply-follows follows-B follows-A) ≡ true
th-follow-added = refl

th-follow-dropped : ∈-follow (frow "bob" "alice") (apply-follows follows-B follows-A) ≡ false
th-follow-dropped = refl

-- ---- apply()'s success flag (task DB3a) ----

-- The Bool that db.rs:apply now returns is true iff the whole batch COMMITs, i.e.
-- iff every INSERTed PRIMARY KEY (accounts username, sessions sid, posts pid) is
-- absent from the rows already on disk; likes/replies/follows have no PK so their
-- INSERTs never error.  collide models the PK check over the pid column.
collide : List ℕ → List ℕ → Bool
collide db [] = false
collide db (p ∷ ps) with key∈ p db
collide db (p ∷ ps) | true = true
collide db (p ∷ ps) | false = collide db ps

inserted-pids : W → W → List ℕ
inserted-pids before after =
  flt (λ p → not (key∈ p (map pid-of (post-of before)))) (map pid-of (post-of after))

apply-ok : W → W → Bool
apply-ok before after =
  not (collide (map pid-of (post-of before)) (inserted-pids before after))

-- test_apply_returns_true: the DB equals BEFORE, so the sample diff INSERTs only pid
-- 500 (fresh), every statement returns Ok, and apply COMMITs with true.
th-apply-ok : apply-ok world-B world-A ≡ true
th-apply-ok = refl
