open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe                        using (just; nothing)
open import Agda.Builtin.Sigma
open import Data.Empty                                using (⊥-elim)
open import Data.List                                 using (List; []; _∷_; length; take; filter; filterᵇ)
open import Data.Nat                                  using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product                              using (∃-syntax)
open import Data.String                               using (String; _≟_)
open import Data.Unit                                 using (tt)
open import Relation.Binary.Definitions               using (DecidableEquality)
open import Relation.Binary.PropositionalEquality     using (_≡_; _≢_; refl; cong;
                                                         sym; trans; subst)
open import Relation.Nullary.Negation.Core             using (¬_)
open import Relation.Nullary.Decidable.Core            using (Dec; yes; no)

open import Helpers

module ImplProofs
  (SessionId PostId : Set)
  (new-sid : CreateNew SessionId)
  (new-pid : CreateNew PostId)
  (_≟ₚ_ : DecidableEquality PostId)
  (_≟ₛᵢ_ : DecidableEquality SessionId)
  where

open import Twitter SessionId PostId new-sid new-pid _≟ₚ_ _≟ₛᵢ_

open import Proofs SessionId PostId new-sid new-pid _≟ₚ_ _≟ₛᵢ_

-- Keyed-table update (same instance Proofs uses when it builds the logout world).
open import Update SessionId _≟ₛᵢ_ SessionStatus unused
  using () renaming (update to add-session-at; update-same to add-session-same;
                     update-no to add-session-no;
                     update-used-keep to add-session-used-keep)

-- Helper: membership is preserved by equal element and equal list.
∈-cong : ∀ {u u′ : String} {ls ls′ : List String} →
         u ≡ u′ → ls ≡ ls′ → u ∈ ls → u′ ∈ ls′
∈-cong refl refl m = m

-- Helper: adding a follower makes the pair (follower, followee) true.
add-follower-self :
  (f : String → String → Bool) (follower followee : String) →
  add-follower f follower followee follower followee ≡ true
add-follower-self f follower followee with follower ≟ follower | followee ≟ followee
... | yes p | yes q = refl
... | yes p | no ¬q = ⊥-elim (¬q refl)
... | no ¬p | q = ⊥-elim (¬p refl)

--------------------------------------------------------------------------------
-- Every theorem below mirrors one QuickCheck property in
-- backend/src/model.rs:mod qc (prop_*).  A value of type World already carries
-- the well-formedness invariants (its proof-carrying fields), so the Rust
-- "if !well_formed w then true" guard needs no hypothesis here.
--------------------------------------------------------------------------------

-- (1) prop_expired_access: a command whose session is not active (so failed
-- access applies first) steps to the SAME world with result expired.
th-prop-expired-access :
  ∀ {before cmd} →
  (∀ {sid} → extract-sid cmd ≡ just sid →
    ¬ (∃[ acc ] ∃[ username ] ValidSession before sid acc username)) →
  Step before cmd before expired
th-prop-expired-access = failed-access

-- (2) prop_register_creates: registering a FRESH username yields success only
-- together with an account carrying the given password and everyone
-- visibility (inversion over the Step derivation).
th-prop-register-creates :
  ∀ {before after username passwd} →
  World.account-at before username ≡ nothing →
  Step before (register username passwd) after success →
  World.account-at after username ≡ just (account passwd everyone)
th-prop-register-creates _ (create-account _ h₂ _) = h₂

-- (3) prop_register_taken: registering an already-taken username yields signup-failed
-- and changes nothing (the failed-create-account constructor forces after ≡ before).
th-prop-register-taken :
  ∀ {before after username passwd} →
  World.account-at before username ≢ nothing →
  Step before (register username passwd) after signup-failed →
  World.account-at after username ≢ nothing
th-prop-register-taken _ (failed-create-account h) = h

-- (3b) prop_register_taken (model.rs:866) asserts nw == w OUTRIGHT: the failed
-- create-account constructor steps to BEFORE itself, so every remaining section
-- is unchanged (the after-world unifies with the before-world by the match).
th-prop-register-taken-id :
  ∀ {before after username passwd} →
  World.account-at before username ≢ nothing →
  Step before (register username passwd) after signup-failed →
  (World.session-at after ≡ World.session-at before)
  × (World.post-at after ≡ World.post-at before)
  × (World.follows after ≡ World.follows before)
  × (World.newest-first after ≡ World.newest-first before)
  × (World.used-post-ids after ≡ World.used-post-ids before)
  × (World.used-session-ids after ≡ World.used-session-ids before)
th-prop-register-taken-id _ (failed-create-account _) =
  refl , refl , refl , refl , refl , refl

-- (4) prop_revoke_token: a successful logout revokes exactly the session that
-- was active for that token before the step (inversion).
th-prop-revoke-logout :
  ∀ {before after sid user} →
  World.session-at before sid ≡ active user →
  Step before (revoke-token sid) after success →
  World.session-at after sid ≡ revoked
th-prop-revoke-logout h (logout _ h₂ _) = h₂

-- (4b) prop_revoke_token (model.rs:882) asserts nw == want outright: only the
-- one session flips (to Revoked, pinned above) and every other section stays
-- put.  The logout constructor pins the rest under a sid ≢ other-sid premise,
-- mirrored below (session-at elsewhere, accounts/posts/follows/newest-first).
th-prop-revoke-rest :
  ∀ {before after sid user other-sid} →
  World.session-at before sid ≡ active user →
  Step before (revoke-token sid) after success →
  sid ≢ other-sid →
  World.session-at before other-sid ≡ World.session-at after other-sid
  ∧ World.account-at before ≡ World.account-at after
  ∧ World.post-at before ≡ World.post-at after
  ∧ World.follows before ≡ World.follows after
  ∧ World.newest-first before ≡ World.newest-first after
th-prop-revoke-rest _ (logout _ _ rest) ne = rest ne

-- (5) prop_follow: following adds (session-user, followee) to the follow
-- relation and changes nothing else; the after-world is constructed here.
th-prop-follow-new :
  ∀ {before sid acc follower followee} →
  ValidSession before sid acc follower →
  ∃[ after ] ∃[ result ]
    Step before (follow sid followee) after result
  × World.follows after follower followee ≡ true
th-prop-follow-new
  {before = before@(world account-at session-at post-at follows newest-first
           used-post-ids used-session-ids only-used-pids only-used-sids
           only-valid-sessions only-valid-posts only-valid-replies
           no-duplicate-replies no-duplicate-likes no-duplicate-posts)}
  {sid} {acc} {follower} {followee} vs =
  after , (success ,
    (follow-user vs refl refl refl refl refl , add-follower-self follows follower followee))
  where
    after : World
    after = world account-at
                  session-at
                  post-at
                  (add-follower follows follower followee)
                  newest-first
                  used-post-ids
                  used-session-ids
                  only-used-pids
                  only-used-sids
                  only-valid-sessions
                  only-valid-posts
                  only-valid-replies
                  no-duplicate-replies
                  no-duplicate-likes
                  no-duplicate-posts

-- (6) prop_like_denied: a valid session that cannot read the post is denied,
-- and the world is untouched.
th-prop-like-denied :
  ∀ {before sid pid acc user} →
  ValidSession before sid acc user →
  ¬ CanReadPost before sid pid →
  Step before (like sid pid) before denied
th-prop-like-denied = failed-like-post

-- (7) prop_like_ok: a successful like puts the session user into the likes of
-- the post as it is afterwards (inversion).
th-prop-like-ok :
  ∀ {before after sid pid acc user post post′} →
  ValidSession before sid acc user →
  World.post-at before pid ≡ just post →
  World.post-at after pid  ≡ just post′ →
  Step before (like sid pid) after success →
  user ∈ Post.likes post′
th-prop-like-ok
  vs pb pa′ (like-post vs₁ _ pb₁ pa₁ ∈₁ _ _ _ _ _ _ _ _) =
  ∈-cong
    (sym (active-injective
            (trans (sym (ValidSession.session-unchanged vs))
                   (ValidSession.session-unchanged vs₁))))
    (cong Post.likes (just-injective (trans (sym pa₁) pa′)))
    ∈₁

-- (8) prop_delete_author (both halves in one theorem, via the spec's _×_): a
-- non-author is denied with the world untouched, and any successful delete
-- marks the post at that id deleted.  (The Rust property re-deletes once more;
-- rerunning the second half proves that again, given the spec's StepExists.)
th-prop-delete-author :
  ∀ {before pid sid acc user post} →
  ValidSession before sid acc user →
  World.post-at before pid ≡ just post →
  Post.author post ≢ user →
  Step before (delete sid pid) before denied
  ×
  (∀ {after post′} →
     World.post-at after pid ≡ just post′ →
     Step before (delete sid pid) after success →
     Post.status post′ ≡ deleted)
th-prop-delete-author vs pb pauth =
  ( failed-delete-not-author vs pb pauth
  , λ { pa′ (delete-post _ _ pa₁ _ _ _ _ _ st _) →
        subst (λ p → Post.status p ≡ deleted)
              (just-injective (trans (sym pa₁) pa′))
              st
      }
  )

-- (9) prop_time_passes: time-passes steps to a world in which every session
-- that was active is revoked (the after-world is built with revoke-all).
th-prop-time-passes :
  (before : World) →
  ∃[ after ] ∃[ result ]
    Step before time-passes after result
  × (∀ {sid user} → World.session-at before sid ≡ active user →
       World.session-at after sid ≡ revoked)
th-prop-time-passes
  before@(world account-at session-at post-at follows newest-first
           used-post-ids used-session-ids only-used-pids only-used-sids
           only-valid-sessions only-valid-posts only-valid-replies
           no-duplicate-replies no-duplicate-likes no-duplicate-posts) =
  after , (success ,
    (session-timeout (revoke-all-active {s = session-at})
      (λ {sid} eq₁ eq₂ eq₃ eq₄ → refl) ,
      revoke-all-active {s = session-at}))
  where
    after : World
    after = world account-at
                  (revoke-all session-at)
                  post-at
                  follows
                  newest-first
                  used-post-ids
                  used-session-ids
                  only-used-pids
                  (revoke-all-used only-used-sids)
                  (revoke-all-valid {s = session-at} only-valid-sessions)
                  only-valid-posts
                  only-valid-replies
                  no-duplicate-replies
                  no-duplicate-likes
                  no-duplicate-posts

-- (10) prop_timeline_valid: the personal timeline of a valid session is
-- exactly take n of the newest-first posts that are readable and by an
-- followed author.
th-prop-timeline-personal :
  ∀ {before n sid acc user} →
  ValidSession before sid acc user →
  Step before (read-personal-timeline sid n) before
    (returned-timeline
       (take n
          (filterᵇ (follows-post-author before user)
                   (filter (can-read-post before sid)
                           (World.newest-first before)))))
th-prop-timeline-personal = get-personal-timeline

-- (11b) prop_timeline_valid (model.rs:1005), GLOBAL branches: the tokened global
-- timeline is take n of the readable newest-first ids (get-private-global-timeline)
-- and the anon one take n of the publicly readable ones; the Rust check also
-- demands membership in newest_first, uniqueness and len <= n, which hold here
-- because the timeline is a take ∘ filter of the well-formed uniq newest-first
-- list, and nw == w because the step keeps the world.
th-prop-timeline-global :
  ∀ {before n sid acc user} →
  ValidSession before sid acc user →
  Step before (read-global-timeline (just sid) n) before
    (returned-timeline
      (take n (filter (can-read-post before sid) (World.newest-first before))))
th-prop-timeline-global = get-private-global-timeline

th-prop-timeline-global-anon :
  ∀ {before n} →
  Step before (read-global-timeline nothing n) before
    (returned-timeline
      (take n (filter (is-post-public before) (World.newest-first before))))
th-prop-timeline-global-anon = get-public-global-timeline

-- Membership reflects back through filter / filterᵇ / take; uniq survives all three.
∈-filterᵇ : ∀ {f : PostId → Bool} {xs : List PostId} {pid : PostId} →
            pid ∈ filterᵇ f xs → pid ∈ xs
∈-filterᵇ {f} {[]} ()
∈-filterᵇ {f} {x ∷ xs} m with f x | m
... | true  | here = here
... | true  | there m′ = there (∈-filterᵇ m′)
... | false | m′ = there (∈-filterᵇ m′)

-- (predicate-generic membership/uniq lemmas clash levels with the indexed CanReadPost,
-- so each spec predicate gets its own copy; only two are ever used by timelines)
∈-filter-crp : ∀ {w : World} {sid : SessionId} {xs : List PostId} {pid : PostId} →
               pid ∈ filter (can-read-post w sid) xs → pid ∈ xs
∈-filter-crp {w} {sid} {[]} ()
∈-filter-crp {w} {sid} {x ∷ xs} m with can-read-post w sid x | m
... | yes _ | here = here
... | yes _ | there m′ = there (∈-filter-crp {w} {sid} m′)
... | no _  | m′ = there (∈-filter-crp {w} {sid} m′)

crp-filter-uniq : ∀ {w : World} {sid : SessionId} {xs : List PostId} →
                  uniq xs → uniq (filter (can-read-post w sid) xs)
crp-filter-uniq {w} {sid} {[]} tt = tt
crp-filter-uniq {w} {sid} {x ∷ xs} (x∉xs , uxs) with can-read-post w sid x
... | yes _ = (λ m → x∉xs (∈-filter-crp {w} {sid} m)) , crp-filter-uniq {w} {sid} {xs} uxs
... | no _ = crp-filter-uniq {w} {sid} {xs} uxs

∈-filter-puc : ∀ {w : World} {xs : List PostId} {pid : PostId} →
               pid ∈ filter (is-post-public w) xs → pid ∈ xs
∈-filter-puc {w} {[]} ()
∈-filter-puc {w} {x ∷ xs} m with is-post-public w x | m
... | yes _ | here = here
... | yes _ | there m′ = there (∈-filter-puc {w} m′)
... | no _  | m′ = there (∈-filter-puc {w} m′)

puc-filter-uniq : ∀ {w : World} {xs : List PostId} →
                  uniq xs → uniq (filter (is-post-public w) xs)
puc-filter-uniq {w} {[]} tt = tt
puc-filter-uniq {w} {x ∷ xs} (x∉xs , uxs) with is-post-public w x
... | yes _ = (λ m → x∉xs (∈-filter-puc {w} m)) , puc-filter-uniq {w} {xs} uxs
... | no _ = puc-filter-uniq {w} {xs} uxs

∈-take : ∀ {xs : List PostId} {pid : PostId} → (n : ℕ) →
         pid ∈ take n xs → pid ∈ xs
∈-take {[]} {_} zero ()
∈-take {[]} {_} (suc n) ()
∈-take {x ∷ xs} {_} zero ()
∈-take {x ∷ xs} {_} (suc n) m with m
... | here = here
... | there m′ = there (∈-take {xs} {_} n m′)

filterᵇ-uniq : ∀ {f : PostId → Bool} {xs : List PostId} →
               uniq xs → uniq (filterᵇ f xs)
filterᵇ-uniq {f} {[]} tt = tt
filterᵇ-uniq {f} {x ∷ xs} (x∉xs , uxs) with f x
... | true = (λ m → x∉xs (∈-filterᵇ {f} {xs} m)) , filterᵇ-uniq {f} {xs} uxs
... | false = filterᵇ-uniq {f} {xs} uxs

take-uniq : ∀ {xs : List PostId} (n : ℕ) → uniq xs → uniq (take n xs)
take-uniq {[]} zero u = tt
take-uniq {[]} (suc n) u = tt
take-uniq {x ∷ xs} zero _ = tt
take-uniq {x ∷ xs} (suc n) (x∉xs , uxs) =
  (λ m → x∉xs (∈-take {xs} {_} n m)) , take-uniq {xs} n uxs

take-len : ∀ {xs : List PostId} (n : ℕ) → length (take n xs) ≤ n
take-len {[]} zero = z≤n
take-len {[]} (suc n) = z≤n
take-len {x ∷ xs} zero = z≤n
take-len {x ∷ xs} (suc n) = s≤s (take-len {xs} n)

-- (4c) prop_revoke_token (model.rs:882) asserts nw == want, i.e. on top of the
-- session flip (th-prop-revoke-logout/rest) it keeps used-post-ids and used-
-- session-ids.  The spec's logout Step constructor leaves those two World fields
-- unconstrained (they do not appear in its premises), so the equality is NOT
-- derivable from an arbitrary derivation.  What the Rust step actually does -
-- flip session-at sid via keyed update, keep every other field - is pinned
-- existentially as a logout step preserving both used-id lists:
th-prop-revoke-used :
  ∀ {before sid acc user} →
  ValidSession before sid acc user →
  ∃[ after ] ∃[ result ]
    Step before (revoke-token sid) after result
  × World.session-at after sid ≡ revoked
  × World.used-post-ids before ≡ World.used-post-ids after
  × World.used-session-ids before ≡ World.used-session-ids after
th-prop-revoke-used
  {before@(world account-at session-at post-at follows newest-first
            used-post-ids used-session-ids only-used-pids only-used-sids
            only-valid-sessions only-valid-posts only-valid-replies
            no-duplicate-replies no-duplicate-likes no-duplicate-posts)}
  {sid} {acc} {user} vs =
  after , (success ,
    (logout (ValidSession.session-unchanged vs)
       (add-session-same {f = session-at} {k = sid} {v = revoked})
       (λ {other-sid} ne →
          sym (add-session-no {f = session-at} {k = sid} {v = revoked} ne)
            , refl , refl , refl , refl)
            , add-session-same {f = session-at} {k = sid} {v = revoked}
            , refl , refl))
  where
    after : World
    after = world account-at
                  (add-session-at session-at sid revoked)
                  post-at
                  follows
                  newest-first
                  used-post-ids
                  used-session-ids
                  only-used-pids
                  (add-session-used-keep revoked
                    (ValidSession.session-unchanged vs) active≢unused revoked≢unused
                    only-used-sids)
                  (add-session-valid-revoke only-valid-sessions)
                  only-valid-posts
                  only-valid-replies
                  no-duplicate-replies
                  no-duplicate-likes
                  no-duplicate-posts

-- (11c) prop_timeline_valid (model.rs:1005) additionally demands unique(&ts) and
-- len(ts) <= n on the returned timeline ts.  The pins above identify ts with a
-- take ∘ filter ∘ newest-first, whose newest-first source is uniq (the World
-- field no-duplicate-posts), so both conjuncts hold for all three timeline
-- branches (personal, tokened global, anon global):
--
-- Task TC (perf, model.rs): the timeline fns were reworked to hoist the
-- session-username/account lookup out of the newest_first loop, stop after
-- collecting n matches (early-stop), and borrow Posts via post_at_ref.
-- Semantics unchanged; pinned in Rust by the QuickCheck props
-- prop_timeline_global_equiv / prop_timeline_personal_equiv comparing the new
-- code to the pre-TC full-filter + take_n behaviour for n in {n, 0, 1, 2, big}.
-- Hence the take ∘ filter characterisation, and the quantified theorems below
-- (th-timeline-* uniq/len/membership), still cover the new code.
th-timeline-global-uniq :
  ∀ {before n sid acc user} →
  ValidSession before sid acc user →
  uniq (take n (filter (can-read-post before sid) (World.newest-first before)))
th-timeline-global-uniq {before} {n} {sid} _ =
  take-uniq n (crp-filter-uniq {before} {sid} (World.no-duplicate-posts before))

th-timeline-global-len :
  ∀ {before n sid acc user} →
  ValidSession before sid acc user →
  length (take n (filter (can-read-post before sid) (World.newest-first before))) ≤ n
th-timeline-global-len {before} {n} {sid} _ = take-len n

th-timeline-global-anon-uniq :
  ∀ {before n} →
  uniq (take n (filter (is-post-public before) (World.newest-first before)))
th-timeline-global-anon-uniq {before} {n} =
  take-uniq n (puc-filter-uniq {before} (World.no-duplicate-posts before))

th-timeline-global-anon-len :
  ∀ {before n} →
  length (take n (filter (is-post-public before) (World.newest-first before))) ≤ n
th-timeline-global-anon-len {before} {n} = take-len n

th-timeline-personal-uniq :
  ∀ {before n sid acc user} →
  ValidSession before sid acc user →
  uniq (take n (filterᵇ (follows-post-author before user)
                       (filter (can-read-post before sid) (World.newest-first before))))
th-timeline-personal-uniq {before} {n} {sid} {acc} {user} _ =
  take-uniq n (filterᵇ-uniq {f = follows-post-author before user}
    (crp-filter-uniq {before} {sid} (World.no-duplicate-posts before)))

th-timeline-personal-len :
  ∀ {before n sid acc user} →
  ValidSession before sid acc user →
  length (take n (filterᵇ (follows-post-author before user)
                        (filter (can-read-post before sid) (World.newest-first before)))) ≤ n
th-timeline-personal-len {before} {n} {sid} {acc} {user} _ = take-len n

-- (11d) prop_timeline_valid (model.rs:1005) additionally demands the ts.iter().all(member
-- &w.newest_first) conjunct: every returned timeline id is a member of newest-first.
-- Holds unconditionally (stronger than the valid-session guard), by membership
-- reflecting back through ∈-take / ∈-filter-crp / ∈-filterᵇ / ∈-filter-puc:
th-timeline-global-membership :
  ∀ {before n sid pid} →
  pid ∈ take n (filter (can-read-post before sid) (World.newest-first before)) →
  pid ∈ World.newest-first before
th-timeline-global-membership {before} {n} {sid} {pid} m =
  ∈-filter-crp {before} {sid} (∈-take n m)

th-timeline-global-anon-membership :
  ∀ {before n pid} →
  pid ∈ take n (filter (is-post-public before) (World.newest-first before)) →
  pid ∈ World.newest-first before
th-timeline-global-anon-membership {before} {n} {pid} m =
  ∈-filter-puc {before} (∈-take n m)

th-timeline-personal-membership :
  ∀ {before n sid pid user} →
  pid ∈ take n (filterᵇ (follows-post-author before user)
                       (filter (can-read-post before sid) (World.newest-first before))) →
  pid ∈ World.newest-first before
th-timeline-personal-membership {before} {n} {sid} {pid} {user} m =
  ∈-filter-crp {before} {sid} (∈-filterᵇ {f = follows-post-author before user} (∈-take n m))

--------------------------------------------------------------------------------
-- FRESH IDS (task TA).  backend/src/main.rs:sample_id_from is the PURE core of the per-request
-- fresh-id decision (the /dev/urandom wrapper sample_id only feeds it one 16-byte block, one
-- big-endian u64 per half).  Its rule is exactly the spec's CreateNew postulate new-sid/new-pid:
-- the id component of the pair they return misses the used list.  Proofs.agda uses that conjunct
-- only inline (not-used-before at Proofs.agda:828, sid∉ at Proofs.agda:997), so we name it here
-- over the spec's own definitions; the Rust QuickCheck props prop-sid-fresh / prop-pid-fresh
-- (backend/src/main.rs:mod qc) pin sample_id_from against the same rule.
--------------------------------------------------------------------------------

th-sample-id-fresh :
  ∀ (w : World) →
  ¬ (Data.Product.proj₂ (Data.Product.proj₁ (new-sid (World.used-session-ids w)))
     ∈ World.used-session-ids w)
  ×
  ¬ (Data.Product.proj₂ (Data.Product.proj₁ (new-pid (World.used-post-ids w)))
     ∈ World.used-post-ids w)
th-sample-id-fresh w =
  Data.Product.proj₁ (Data.Product.proj₂ (new-sid (World.used-session-ids w)))
  , Data.Product.proj₁ (Data.Product.proj₂ (new-pid (World.used-post-ids w)))

-- The wire-layer refl theorems (from-input / to-output pins for backend/src/wire.rs) live in
-- backend/ImplWire.agda: opening Interface inside this module clashes with Twitter's Command/Result
-- at the SessionId/PostId instantiation, so they are proven in a module that sees only Interface.

-- Per A4 the stdlib-only companion pins for db.rs (apply diff, load∘save, reload_* pins,
-- next-tick schedule) were removed: they never referenced Twitter/Interface, hence prove
-- nothing about the spec model. The Rust unit tests they backed (test_apply_*, test_db_*,
-- test_tick_rotation_cycle) still guard that behaviour; recovery commit b6b868b keeps them.
