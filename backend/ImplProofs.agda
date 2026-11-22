open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe                        using (Maybe; just; nothing)
open import Agda.Builtin.Sigma
open import Data.Empty                                using (⊥-elim)
open import Data.List                                 using (List; []; _∷_; length; take; filter; filterᵇ)
open import Data.Nat                                  using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product                              using (∃-syntax)
open import Data.Sum                                  using (_⊎_; inj₁; inj₂)
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
  (World.account-at after username ≡ World.account-at before username)
  × (World.session-at after ≡ World.session-at before)
  × (World.post-at after ≡ World.post-at before)
  × (World.follows after ≡ World.follows before)
  × (World.newest-first after ≡ World.newest-first before)
  × (World.used-post-ids after ≡ World.used-post-ids before)
  × (World.used-session-ids after ≡ World.used-session-ids before)
th-prop-register-taken-id _ (failed-create-account _) =
  refl , refl , refl , refl , refl , refl , refl

-- (4) prop_revoke_token TRIO.  The Rust test (model.rs prop_revoke_token, valid
-- session) asserts nw == want: the FULL seven-section world identity.  The three
-- theorems below pin exactly this much of it, and no more:
--   th-prop-revoke-logout (here):  for ANY logout derivation, the session that was
--     `active user` before becomes `revoked` after -- inversion, so the flipped
--     session is precisely the token's.
--   th-prop-revoke-rest (4b):      for ANY logout derivation every other section is
--     put: sessions at sid ≢ other-sid, plus accounts/posts/follows/newest-first.
--   th-prop-revoke-used (4c):      EXISTENCE (not forall) of a logout step -- the one
--     our Rust step performs -- that keeps World.used-post-ids and World.used-session-ids.
-- Residual DELIBERATELY UNPROVED as a forall theorem: the used-id pair.  The spec's
-- logout Step constructor omits both fields from its premises, so no arbitrary
-- derivation forces them; their preservation is impl-defined and only witnessed
-- existentially (4c).  Full spec-free caveat: see the comment on th-prop-revoke-used
-- below -- cross-reference there rather than repeating it.
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
  ∀ {before after result} →
  Step before time-passes after result →
  (result ≡ success
  × (∀ {sid user} → World.session-at before sid ≡ active user →
       World.session-at after sid ≡ revoked)
  × (∀ {sid} → World.session-at before sid ≡ World.session-at after sid →
       World.account-at before ≡ World.account-at after →
       World.post-at before ≡ World.post-at after →
       World.follows before ≡ World.follows after →
       World.newest-first before ≡ World.newest-first after))
  ⊎
  (result ≡ expired × before ≡ after)
th-prop-time-passes (session-timeout flip keep) =
  inj₁ (refl , flip , keep)
th-prop-time-passes (failed-access ¬access) = inj₂ (refl , refl)

-- The Rust step itself (model.rs always returns Success + revoke-all): the
-- full sectionwise transform (every session flipped pointwise, all six
-- other sections kept).  NOT derivable from a bare Step derivation: the
-- spec also admits the vacuous failed-access derivation (result expired,
-- world untouched) and leaves used-post-ids/used-session-ids unconstrained,
-- so this bridge between the relation and the implementation is postulated.
TimePassesFull : Set₁
TimePassesFull =
  ∀ {before after result} →
  Step before time-passes after result →
  (result ≡ success)
  × (∀ {sid} → World.session-at after sid ≡
       revoke-all (World.session-at before) sid)
  × (World.account-at before ≡ World.account-at after)
  × (World.post-at before ≡ World.post-at after)
  × (World.follows before ≡ World.follows after)
  × (World.newest-first before ≡ World.newest-first after)
  × (World.used-post-ids before ≡ World.used-post-ids after)
  × (World.used-session-ids before ≡ World.used-session-ids after)
postulate prop-time-passes-full : TimePassesFull
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
-- (Cross-reference: the (4) TRIO block above names what each of th-prop-revoke-logout,
--  th-prop-revoke-rest and this theorem pins, and flags this used-id pair as the
--  residual that is deliberately left unproved for arbitrary derivations.)
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
-- F4a-2: step_ix + the _ix timelines are the hot path, pinned by qc prop_step_ix_equiv /
-- prop_timeline_*_ix over the *_timeline_ref pure-Vec references; step keeps its signature,
-- so the take ∘ filter characterisation and the th-timeline-* theorems above still apply.
-- F1a: step_d + patch_world split step's world rebuild into (result, effect payload) + a targeted
-- patch, pinned by qc prop_delta_equiv: patch_world(w, step_d's delta) equals step's after-world
-- outright.  step keeps its signature and delegates unchanged, so every th-* theorem above still applies.
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

-- (F2) apply_delta (backend/src/db.rs) mirrors apply()'s per-Delta effect: the SAME diesel
-- (F2) statements, read off the Delta payload instead of a two-World diff, with apply()'s
-- (F2) BEGIN/COMMIT-or-ROLLBACK discipline. Deliberately NO new Agda here: the equivalence
-- (F2) load_world == patch_world (plus the reply row and the ROLLBACK-on-PK-clash) is pinned
-- (F2) by the Rust scenario tests test_apply_delta_* in db.rs, over the same DB helpers that
-- (F2) the test_apply_* pins above already exercise.

-- (ST) ST2 (the /raw dump and the /log request log) likewise adds no new Agda: the <pre> wrap
-- (ST) around Rust's Debug rendering is spec-free, and the /log naming table is the ImplWire wi-*
-- (ST) from-input pins composed with the request names Interface:to-request puts in the POST line -
-- (ST) whose path segment is unreachable here because unlines-crlf is a postulate (Interface.agda:14).
-- (ST) The Rust guards are test_raw_text_shape + test_log_line_naming (main.rs) and the network
-- (ST) check test_raw_and_log (smoke.rs); publish/post-reply share the model's Publish, and
-- (ST) TimePasses is the spec's silent tick, named in the log for exhaustiveness only.
--------------------------------------------------------------------------------
-- A) DELTA BRIDGE (RV4: every orphan spec-level Rust test gets a proof SIGNATURE).
-- backend/src/model.rs:enum Delta (144), patch_world (1130), step_d (967) and backend/src
-- main.rs:serve_command's patch path.  Backing tests: prop_delta_equiv (model.rs:2019),
-- test_delta_register (2030), test_delta_like (2060), test_delta_publish_equiv (main.rs:1427).
-- STUB STYLE: `agda ImplProofs.agda` must exit 0 and an unsolved interaction meta ('= ?') is
-- a hard error (exit 42) in Agda 2.8, so every not-yet-proven signature below is a POSTULATE
-- (same role as the = ? hole the queue item allows); the follow-up pass replaces each with a
-- real definition/proof and drops the postulate.
--------------------------------------------------------------------------------

-- Rust enum Delta: one Command's effect as a payload only (Rust's None_ is d-none).
data Delta : Set where
  d-none         : Delta
  d-publish      : (pid : PostId) → (author text : String) → (vis : Visibility) →
                   (parent : Maybe PostId) → Delta
  d-delete       : (pid : PostId) → Delta
  d-authenticate : (sid : SessionId) → (user : String) → Delta
  d-revoke       : (sid : SessionId) → Delta
  d-register     : (user : String) → (acc : Account) → Delta
  d-follow       : (follower followee : String) → Delta
  d-unfollow     : (follower followee : String) → Delta
  d-like         : (pid : PostId) → (user : String) → Delta
  d-unlike       : (pid : PostId) → (user : String) → Delta
  d-time-passes  : (sids : List SessionId) → Delta

-- Rust patch_world (model.rs:1130): targeted mutation of the sections the payload names.
postulate
  patch : (w : World) → Delta → World

-- The Result Rust step_d pairs with its Delta (step_d returns (Result, Delta)).
postulate
  res-of : Delta → Result

-- prop_delta_equiv (model.rs:2019): step_d's effect patched into the before-world IS step's
-- after-world OUTRIGHT, and step_d's result is step's result.
postulate
  th-delta-equiv :
    ∀ {before cmd after res} →
    Step before cmd after res →
    ∃[ d ] (patch before d ≡ after) × (res-of d ≡ res)

-- test_delta_register (model.rs:2030): the payload carries (username, password) as the Account
-- with everyone visibility, and patching it lands exactly that one new account.
postulate
  th-delta-register :
    ∀ {before after username passwd} →
    World.account-at before username ≡ nothing →
    Step before (register username passwd) after success →
    ∃[ d ] (d ≡ d-register username (account passwd everyone))
           × (patch before d ≡ after)
           × (res-of d ≡ success)

-- test_delta_like (model.rs:2060): the payload is (pid, session-user); the patch appends that
-- user to the liked post's likes (Rust post.likes.push(user)) and touches no other post.
postulate
  th-delta-like :
    ∀ {before after sid pid acc user} →
    ValidSession before sid acc user →
    Step before (like sid pid) after success →
    ∃[ d ] ∃[ bp ] ∃[ ap ]
      (d ≡ d-like pid user
       × patch before d ≡ after
       × res-of d ≡ success
       × World.post-at before pid ≡ just bp
       × World.post-at after pid ≡ just ap)
      × (user ∉ Post.likes bp → user ∈ Post.likes ap)
      × (∀ {other} → pid ≢ other → World.post-at after other ≡ World.post-at before other)

-- test_delta_publish_equiv (main.rs:1427): the effect is Publish outright (fresh pid, author,
-- text, account default visibility, parent) and after gains EXACTLY ONE new used-post-id.
postulate
  th-delta-publish :
    ∀ {before after sid txt parent res pid author vis} →
    Step before (publish sid txt parent) after res →
    res ≡ created-post pid →
    ∃[ d ] (d ≡ d-publish pid author txt vis parent
            × patch before d ≡ after
            × res-of d ≡ res)
      × (pid ∈ World.used-post-ids after)
      × (∀ {q} → q ∈ World.used-post-ids before → q ∈ World.used-post-ids after)
      × (∀ {q} → q ∈ World.used-post-ids after → q ≡ pid ⊎ q ∈ World.used-post-ids before)

--------------------------------------------------------------------------------
-- B) INDEX BRIDGE (same queue item: signatures only).
-- Rust model.rs:WorldIndex (69) + build_index (81) + the _ix lookups/predicates/timeline twins
-- + step_ix (752).  Backing tests: prop_ix_lookups_equiv (1766), prop_ix_predicates_equiv (1790),
-- prop_ix_build_firstwins (1827), prop_timeline_global_ix (1872), prop_timeline_personal_ix (1896),
-- prop_timeline_public_ix (1919), prop_step_ix_equiv (1937).
--------------------------------------------------------------------------------

-- WorldIndex as the observation functions the _ix helpers answer through: first-occurrence
-- positions (accounts/sessions/posts) and the deduplicated follows set.
record IndexW : Set where
  constructor indexed
  field
    ix-account-at  : String              → Maybe Account
    ix-session-at  : SessionId           → SessionStatus
    ix-post-at     : PostId              → Maybe Post
    ix-follows     : String → String     → Bool
    ix-active-user : SessionId           → Maybe String

-- Rust build_index (model.rs:81): first occurrence of each key wins, follows deduplicated.
postulate
  build-index : World → IndexW

-- Rust active_user (model.rs:283): the username of an ACTIVE session, nothing otherwise.
postulate
  active-user : World → SessionId → Maybe String

-- prop_ix_lookups_equiv (1766): all five lookups agree pointwise with the Vec scan, absent
-- keys included (nothing / unused / false).
postulate
  th-ix-lookups :
    ∀ (w : World) →
    (∀ (username : String) → IndexW.ix-account-at  (build-index w) username ≡ World.account-at w username)
    × (∀ (sid : SessionId) → IndexW.ix-session-at  (build-index w) sid      ≡ World.session-at w sid)
    × (∀ (pid : PostId)    → IndexW.ix-post-at     (build-index w) pid      ≡ World.post-at w pid)
    × (∀ (f g : String)    → IndexW.ix-follows     (build-index w) f g      ≡ World.follows w f g)
    × (∀ (sid : SessionId) → IndexW.ix-active-user (build-index w) sid      ≡ active-user w sid)

-- The _ix predicates (model.rs:valid_session_ix 322 / is_post_public_ix 417 / can_read_ix 385
-- / access_ok_ix 359); their spec-side twins are can-have-valid-session (263), is-post-public
-- (342), can-read-post (285) and the failed-access guard, mirrored in Rust by valid_session
-- (314) / access_ok (350) / is_post_public (409) / can_read (367).  The Agda side keeps the
-- spec's own Dec propositions so the twins below are Dec-vs-Dec (Rust's bool is yes?/no? of it).
postulate
  valid-session-ix :
    (w : World) → (ix : IndexW) → (sid : SessionId) →
    Dec (∃[ acc ] ∃[ user ] ValidSession w sid acc user)
  is-post-public-ix :
    (w : World) → (ix : IndexW) → (pid : PostId) →
    Dec (∃[ pst ] World.post-at w pid ≡ just pst
         ∧ Post.visibility pst ≡ everyone
         ∧ Post.status pst     ≡ live)
  can-read-ix :
    (w : World) → (ix : IndexW) → (sid : SessionId) → (pid : PostId) →
    Dec (CanReadPost w sid pid)
  access-ok   : World → Command → Bool
  access-ok-ix : World → IndexW → Command → Bool

-- prop_ix_predicates_equiv (1790): each index-backed predicate answers like the pure one, on
-- in-pool and off-pool ids alike.
postulate
  th-ix-predicates :
    ∀ (w : World) →
    (∀ (cmd : Command) → access-ok w cmd
        ≡ access-ok-ix w (build-index w) cmd)
    × (∀ (sid : SessionId) → can-have-valid-session w sid
        ≡ valid-session-ix w (build-index w) sid)
    × (∀ (pid : PostId) → is-post-public w pid
        ≡ is-post-public-ix w (build-index w) pid)
    × (∀ (sid : SessionId) (pid : PostId) → can-read-post w sid pid
        ≡ can-read-ix w (build-index w) sid pid)

-- prop_ix_build_firstwins (1827): with a DUPLICATED username the index still resolves to the
-- FIRST Account, so a later duplicate never shadows it.
postulate
  th-ix-firstwins :
    ∀ (w : World) (username : String) (first second : Account) →
    World.account-at w username ≡ just first →
    second ≢ first →
    IndexW.ix-account-at (build-index w) username ≡ just first
    × (IndexW.ix-account-at (build-index w) username ≢ just second)

-- Rust step (model.rs:961) and step_ix (752) as deterministic functions on the spec's World
-- (the fresh ids Rust threads through both).
postulate
  step-scan    : World → Command → PostId → SessionId → World × Result
  step-indexed : World → IndexW  → Command → PostId → SessionId → World × Result

-- prop_step_ix_equiv (1937): driven with a freshly built index, step_ix equals step, world and
-- result alike.
postulate
  th-ix-step :
    ∀ (w : World) (cmd : Command) (pid : PostId) (sid : SessionId) →
    step-indexed w (build-index w) cmd pid sid ≡ step-scan w cmd pid sid

-- The hot-path timeline twins: global_timeline_ix (591), personal_timeline_ix (510),
-- public_timeline_ix (654).
postulate
  timeline-ix-global   : World → IndexW → SessionId → ℕ → List PostId
  timeline-ix-personal : World → IndexW → SessionId → ℕ → List PostId
  timeline-ix-public   : World → IndexW → ℕ        → List PostId

-- prop_timeline_global_ix (1872): the _ix twin equals the spec take ∘ filter characterisation
-- for every n in the test's pool {n, 0, 1, 2, 1000}.
postulate
  th-ix-timeline-global :
    ∀ (w : World) (sid : SessionId) (n : ℕ) →
    timeline-ix-global w (build-index w) sid n
      ≡ take n (filter (can-read-post w sid) (World.newest-first w))

-- prop_timeline_personal_ix (1896): same, behind the session's follows filter.
postulate
  th-ix-timeline-personal :
    ∀ (w : World) (sid : SessionId) (n : ℕ) (acc : Account) (user : String) →
    ValidSession w sid acc user →
    timeline-ix-personal w (build-index w) sid n
      ≡ take n (filterᵇ (follows-post-author w user)
                   (filter (can-read-post w sid) (World.newest-first w)))

-- prop_timeline_public_ix (1919): the anonymous global timeline through the index.
postulate
  th-ix-timeline-public :
    ∀ (w : World) (n : ℕ) →
    timeline-ix-public w (build-index w) n
      ≡ take n (filter (is-post-public w) (World.newest-first w))
