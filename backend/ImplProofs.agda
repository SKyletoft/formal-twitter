open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe                        using (Maybe; just; nothing)
open import Agda.Builtin.Sigma
open import Data.Empty                                using (⊥-elim; ⊥)
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

--------------------------------------------------------------------------------
-- (3c) prop_login_success (model.rs): an ISSUED session (the login constructor, Twitter.agda:490)
-- (3c) forces the token's session to be ACTIVE for the logging-in user, and the constructor's
-- (3c) rest premise pins every OTHER section put -- mirrored verbatim, binders included, because
-- (3c) login states its rest POINTWISE (other-sid pid u1 u2), unlike logout's eta-reduced rest.
-- (3c) Deliberately NOT claimed here: World.used-session-ids.  The login constructor never names
-- (3c) that field, so the Rust gain (used_session_ids.push(fresh_sid)) is impl-defined, tied to
-- (3c) session-at only by the World's own only-used-sids field; cf. the spec-free caveat on
-- (3c) th-prop-revoke-used.  Rust's used-sid LoginFailed refusal is impl-defined the same way
-- (3c) (step's own guard, no spec rule) and stays out of both the hypotheses and the conclusion.
th-prop-login-issued :
  ∀ {before after username passwd sid} →
  Step before (authenticate username passwd) after (issued-session sid) →
  (World.session-at after sid ≡ active username)
  × (∀ {other-sid pid u1 u2} →
      sid ≢ other-sid →
      World.session-at before other-sid ≡ World.session-at after other-sid
      ∧ World.account-at before u1      ≡ World.account-at after u1
      ∧ World.post-at before pid        ≡ World.post-at after pid
      ∧ World.follows before u1 u2      ≡ World.follows after u1 u2
      ∧ World.newest-first before       ≡ World.newest-first after)
th-prop-login-issued (login _ h₂ _ _ rest _) = h₂ , rest

-- (3d) prop_login_unknown_user (spec failed-login-1, Twitter.agda:507): with no account at all
-- (3d) the login fails and after ≡ before OUTRIGHT, so all seven sections stay put (the same
-- (3d) shape as th-prop-register-taken-id, whose proof is the sibling failed-create-account).
-- (3d) The second clause covers the OTHER login-failed derivation shape (failed-login-2); its
-- (3d) premises contradict this theorem's, but both constructors step to before itself, so the
-- (3d) same identity holds -- the Rust claim (nw == w) is total on login-failed, not partial.
th-prop-login-unknown :
  ∀ {before after username passwd} →
  World.account-at before username ≡ nothing →
  Step before (authenticate username passwd) after login-failed →
  (World.account-at after username ≡ World.account-at before username)
  × (World.session-at after ≡ World.session-at before)
  × (World.post-at after ≡ World.post-at before)
  × (World.follows after ≡ World.follows before)
  × (World.newest-first after ≡ World.newest-first before)
  × (World.used-post-ids after ≡ World.used-post-ids before)
  × (World.used-session-ids after ≡ World.used-session-ids before)
th-prop-login-unknown _ (failed-login-1 _) =
  refl , refl , refl , refl , refl , refl , refl
th-prop-login-unknown _ (failed-login-2 _ _) =
  refl , refl , refl , refl , refl , refl , refl

-- (3e) prop_login_wrong_password (spec failed-login-2, Twitter.agda:512): the account is there
-- (3e) but its password differs, and the very same login-failed identity holds.  The Rust prop's
-- (3e) FRESH-sid hypothesis mirrors login's session-at before sid ≡ unused premise, but a failed
-- (3e) login needs no session at all: failed-login-2 never mentions a sid, so none appears here
-- (3e) and freshness is NOT a spec condition for login failure (Rust's used-sid guard is impl-defined
-- (3e) and yields the same LoginFailed, same world).
th-prop-login-wrong :
  ∀ {before after username passwd user} →
  World.account-at before username ≡ just user →
  Account.password user ≢ passwd →
  Step before (authenticate username passwd) after login-failed →
  (World.account-at after username ≡ World.account-at before username)
  × (World.session-at after ≡ World.session-at before)
  × (World.post-at after ≡ World.post-at before)
  × (World.follows after ≡ World.follows before)
  × (World.newest-first after ≡ World.newest-first before)
  × (World.used-post-ids after ≡ World.used-post-ids before)
  × (World.used-session-ids after ≡ World.used-session-ids before)
th-prop-login-wrong _ _ (failed-login-2 _ _) =
  refl , refl , refl , refl , refl , refl , refl
th-prop-login-wrong _ _ (failed-login-1 _) =
  refl , refl , refl , refl , refl , refl , refl
--------------------------------------------------------------------------------

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

-- (ST) ST2 (the /raw dump and the /log request log) likewise adds no new Agda: the raw {:#?}
-- (ST) rendering of the World in Rust (RAW1: plaintext, no markup) is spec-free, and the /log naming
-- (ST) table is the ImplWire wi-* from-input pins composed with the request names Interface:to-request
-- (ST) puts in the POST line -
-- (ST) whose path segment is unreachable here because unlines-crlf is a postulate (Interface.agda:14).
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

--------------------------------------------------------------------------------
-- (RV6) read-post quintet: model.rs prop_read_logged_in / prop_read_public_shape /
-- prop_read_denied_missing / prop_read_denied_private / prop_read_denied_deleted, read off step's
-- ReadPost arm (model.rs:842-862): readable is can_read_ix for Some sid and is_post_public_ix for
-- the NOTHING token; unreadable returns (w.clone(), Denied); otherwise post_at_ix rebuilds
-- ReturnedPost author text (len_u64 likes) replies -- the COUNT of Post.likes, since Result's
-- returned-post carries a Nat -- and clones w OUTRIGHT, which is why every theorem below concludes
-- after ≡ before, the Rust's `nw == w`.
--------------------------------------------------------------------------------

-- (RV6a) prop_read_logged_in (spec read-post-logged-in, Twitter.agda:540): the returned post IS the
-- stored post at pid -- author, text, the NUMBER of likes, replies -- and the world is carried
-- untouched.  The constructor names its OWN post, so each claim is sym-of-the-constructor's equation
-- (Post.author post₁ ≡ author etc.) pushed along just-injective (trans (sym pa₁) pa) : post₁ ≡ post,
-- the two post-at proofs at one id naming one post.
th-prop-read-logged-in :
  ∀ {before after pid sid acc user post author txt likes replies} →
  ValidSession before sid acc user →
  CanReadPost before sid pid →
  World.post-at before pid ≡ just post →
  Step before (read-post (just sid) pid) after (returned-post author txt likes replies) →
  (after ≡ before)
  × (author ≡ Post.author post)
  × (txt ≡ Post.text post)
  × (likes ≡ length (Post.likes post))
  × (replies ≡ Post.replies post)
th-prop-read-logged-in vs crp pa (read-post-logged-in _ pa₁ a₁ t₁ l₁ r₁) =
  refl
  , trans (sym a₁) (cong Post.author (just-injective (trans (sym pa₁) pa)))
  , trans (sym t₁) (cong Post.text (just-injective (trans (sym pa₁) pa)))
  , trans (sym l₁) (cong length (cong Post.likes (just-injective (trans (sym pa₁) pa))))
  , trans (sym r₁) (cong Post.replies (just-injective (trans (sym pa₁) pa)))

-- (RV6b) prop_read_public_shape (spec read-post-anonymously, Twitter.agda:550): the NOTHING session
-- token reads a LIVE Everyone post, and the result is the very same ReturnedPost shape of the stored
-- post -- return-post (Twitter.agda:362) is author text (length likes) replies by definition, so the
-- theorem case-splits the post at pid to see that shape.  NOT claimed anywhere: an anonymous read of
-- a private/deleted/missing post -- Twitter.agda has no such Step constructor (read-post-anonymously
-- needs everyone AND live), so the impl's Denied there is impl-defined.
th-prop-read-public :
  ∀ {before after pid p author txt likes replies} →
  World.post-at before pid ≡ just p →
  Post.visibility p ≡ everyone →
  Post.status p ≡ live →
  Step before (read-post nothing pid) after (returned-post author txt likes replies) →
  (after ≡ before)
  × (author ≡ Post.author p)
  × (txt ≡ Post.text p)
  × (likes ≡ length (Post.likes p))
  × (replies ≡ Post.replies p)
th-prop-read-public pa vis st
  (read-post-anonymously {p = post author₁ txt₁ vis₁ live₁ likes₁ replies₁ parent₁} pa₁ _ _) =
  refl
  , sym (cong Post.author (just-injective (trans (sym pa) pa₁)))
  , sym (cong Post.text (just-injective (trans (sym pa) pa₁)))
  , sym (cong length (cong Post.likes (just-injective (trans (sym pa) pa₁))))
  , sym (cong Post.replies (just-injective (trans (sym pa) pa₁)))

-- (RV6c) prop_read_denied_missing (spec cant-read-post-public, Twitter.agda:518 -- the read-post rule
-- whose post-at premise is nothing, i.e. the MISSING post): the result index is pinned to the spec's
-- denied (Rust's res == Result::Denied) and every cant-read-post-* constructor steps to before, so
-- after ≡ before is refl; the three clauses cover the three denied read-post rules, failed-access
-- (expired) being impossible for a denied result.
th-prop-read-denied-missing :
  ∀ {before after pid sid acc user} →
  ValidSession before sid acc user →
  World.post-at before pid ≡ nothing →
  Step before (read-post (just sid) pid) after denied →
  after ≡ before
th-prop-read-denied-missing vs pa (cant-read-post-public _ _) = refl
th-prop-read-denied-missing vs pa (cant-read-post-private _ _ _ _ _) = refl
th-prop-read-denied-missing vs pa (cant-read-post-private-deleted _ _ _) = refl

-- (RV6d) prop_read_denied_private (spec cant-read-post-private, Twitter.agda:524): live followers-only
-- post, the session user does NOT follow the author, so CanReadPost's followers-only branch fails.
th-prop-read-denied-private :
  ∀ {before after pid sid acc user post} →
  ValidSession before sid acc user →
  World.post-at before pid ≡ just post →
  Post.visibility post ≡ followers-only →
  Post.status post ≡ live →
  World.follows before user (Post.author post) ≡ false →
  Step before (read-post (just sid) pid) after denied →
  after ≡ before
th-prop-read-denied-private vs pa vis slv flw (cant-read-post-private _ _ _ _ _) = refl
th-prop-read-denied-private vs pa vis slv flw (cant-read-post-public _ _) = refl
th-prop-read-denied-private vs pa vis slv flw (cant-read-post-private-deleted _ _ _) = refl

-- (RV6e) prop_read_denied_deleted (spec cant-read-post-private-deleted, Twitter.agda:533): a tombstone
-- post is unreadable, so Denied and the world is carried untouched.
th-prop-read-denied-deleted :
  ∀ {before after pid sid acc user post} →
  ValidSession before sid acc user →
  World.post-at before pid ≡ just post →
  Post.status post ≡ deleted →
  Step before (read-post (just sid) pid) after denied →
  after ≡ before
th-prop-read-denied-deleted vs pa st (cant-read-post-private-deleted _ _ _) = refl
th-prop-read-denied-deleted vs pa st (cant-read-post-private _ _ _ _ _) = refl
th-prop-read-denied-deleted vs pa st (cant-read-post-public _ _) = refl

--------------------------------------------------------------------------------
-- (RV7) publish trio: model.rs prop_publish_new / prop_reply_publish /
-- prop_reply_denied over the correlated PublishCase generator (model.rs:1554-1640), read
-- off step's Publish arm (model.rs:752-825, whose parent-replies prepend is the
-- RV5-0 fix).  The Step's command/result index pins the constructor so each
-- theorem below has EXACTLY ONE live clause: a nothing parent rules out
-- successful-reply / failed-reply (just-vs-nothing clash in the command), a
-- created-post result rules out failed-reply, and a denied result rules out
-- both success rules.  The impl's author = session username and vis = session
-- account's default-visibility pins (Rust's nw == want) are an impl-defined
-- refinement: spec's successful-post leaves the Account existential, so we
-- witness with ∃ here; the new-reply visibility INHERITANCE (new-reply
-- Twitter.agda:214-217: followers-only parent ⇒ followers-only child, else account
-- default) is definitional via the new-reply application.  The used-post-ids
-- gain (Rust used_post_ids.push) is IMPL-DEFINED -- Twitter.agda's World has no
-- such field -- so it stays unclaimed; the pointwise "everything else unchanged"
-- conjunct comes verbatim from the constructor's rest premise.
--------------------------------------------------------------------------------

-- (RV7a) prop_publish_new (spec successful-post, Twitter.agda:387-399): the pid WAS
-- absent (PostIsNew.was-absent), the new post sits at pid after (is-present), and
-- newest-first is PREPENDED with pid (the constructor's nf premise, kept as-is).
th-prop-publish-new :
  ∀ {before after sid txt pid} →
  Step before (publish sid txt nothing) after (created-post pid) →
  World.post-at before pid ≡ nothing
  × (∃[ author ] ∃[ acct ] World.post-at after pid ≡ just (new-post author txt acct))
  × (pid ∷ World.newest-first before ≡ World.newest-first after)
th-prop-publish-new (successful-post {username = author} {user = acct} _ pnl nf _) =
  PostIsNew.was-absent pnl
  , (author , (acct , PostIsNew.is-present pnl))
  , nf

-- (RV7b) prop_reply_publish (spec successful-reply, Twitter.agda:401-422): pid was
-- absent and the reply (new-reply author txt acct ppid ppost) sits at pid; the PARENT
-- post at ppid existed before with the constructor's shape post pauthor ptxt pv live
-- plikes preplies pparent and AFTER carries replies PREPENDED with pid (pp′-eq :410,
-- the Rust parent.replies.insert(0,pid) fix); newest-first prepend; pid ≢ ppid (neq).
th-prop-reply-publish :
  ∀ {before after sid txt ppid pid} →
  Step before (publish sid txt (just ppid)) after (created-post pid) →
  World.post-at before pid ≡ nothing
  × (∃[ author ] ∃[ acct ] ∃[ ppost ] ∃[ ppar ]
      (World.post-at before ppid ≡ just ppost
      × World.post-at after pid ≡ just (new-reply author txt acct ppar ppost)))
  × (∃[ pauthor ] ∃[ ptxt ] ∃[ pv ] ∃[ plikes ] ∃[ preplies ] ∃[ pparent ]
      (World.post-at before ppid
        ≡ just (post pauthor ptxt pv live plikes preplies pparent)
      × World.post-at after ppid
        ≡ just (post pauthor ptxt pv live plikes (pid ∷ preplies) pparent)))
  × (pid ∷ World.newest-first before ≡ World.newest-first after)
  × pid ≢ ppid
th-prop-reply-publish
  (successful-reply {_} {_} {_} {_} {author} {acct} {_} {_} {ppar} {ppost}
     vs₁ pnl nf
     {ptxt = ptxt} {pauthor = pauthor} {pvisibility = pv}
     {plikes = plikes} {preplies = preplies} {pparent = pparent}
     crp pp-eq pp′-eq pa₀ pa₁ neq _) =
  PostIsNew.was-absent pnl
  , (author , (acct , (ppost , (ppar , (pa₀ , PostIsNew.is-present pnl)))))
  , (pauthor , (ptxt , (pv , (plikes , (preplies , (pparent ,
      (trans pa₀ (cong (λ q → just q) pp-eq)
       , trans pa₁ (cong (λ q → just q) pp′-eq))))))))
  , nf
  , neq

-- (RV7c) prop_reply_denied (spec failed-reply, Twitter.agda:424-428): the parent is
-- NOT readable, so the result is denied AND the before world is carried outright
-- (Rust's nw == w); the unreadability witness (Rust's !can_read guard) comes
-- from the constructor's ¬ premise.
th-prop-reply-denied :
  ∀ {before after sid txt ppid} →
  Step before (publish sid txt (just ppid)) after denied →
  (after ≡ before) × (¬ CanReadPost before sid ppid)
th-prop-reply-denied (failed-reply _ ncrp) = refl , ncrp

--------------------------------------------------------------------------------
-- (RV8) unlike / unfollow / follow-gate / timeline-excludes quintet: model.rs's
-- prop_unlike_ok (2051) / prop_unlike_denied (2080) / prop_unfollow (2102) /
-- prop_follow_gates_timeline (2157) / prop_timeline_excludes_deleted (2206), read
-- off step's Unfollow arm (model.rs:923) and Unlike arm (model.rs:948) through the
-- PLAIN as_unlike / as_unfollow destructors (model.rs:1316 / 1323 -- no derive-magic
-- accessors, no new dependency).  Spec rules: unlike-post (Twitter.agda:621),
-- failed-unlike-post (649), unfollow-user (666), the POSITIVE CanReadPost.post-is-private
-- (173), get-personal-timeline (557) and get-public-global-timeline (583).
-- Every lemma below is a real definition: this block introduces NO postulate.
--------------------------------------------------------------------------------

-- Membership transports through equal element + equal list, also for ABSENCE.
∉-cong : ∀ {u u′ : String} {ls ls′ : List String} →
         u ≡ u′ → ls ≡ ls′ → u ∉ ls → u′ ∉ ls′
∉-cong refl refl neq = neq

-- remove-follower is the pair-difference of the follow relation (Rust's follows.retain): the
-- targeted pair becomes false, every OTHER pair survives pointwise, and an already-absent pair
-- leaves the relation unchanged pointwise, which is prop_unfollow's idempotence half.
remove-follower-self :
  (f : String → String → Bool) (follower followee : String) →
  remove-follower f follower followee follower followee ≡ false
remove-follower-self f follower followee with follower ≟ follower | followee ≟ followee
... | yes _ | yes _ = refl
... | yes p | no ¬q = ⊥-elim (¬q refl)
... | no ¬p | q = ⊥-elim (¬p refl)

remove-follower-other :
  (f : String → String → Bool) (follower followee x y : String) →
  x ≢ follower ⊎ y ≢ followee →
  remove-follower f follower followee x y ≡ f x y
remove-follower-other f follower followee x y (inj₁ neq) with follower ≟ x | followee ≟ y
... | yes p | q = ⊥-elim (neq (sym p))
... | no ¬p | q = refl
remove-follower-other f follower followee x y (inj₂ neq) with follower ≟ x | followee ≟ y
... | yes p | yes q = ⊥-elim (neq (sym q))
... | yes p | no ¬q = refl
... | no ¬p | q = refl

remove-follower-idem :
  (f : String → String → Bool) (follower followee : String) →
  f follower followee ≡ false →
  (x y : String) → remove-follower f follower followee x y ≡ f x y
remove-follower-idem f follower followee absent x y with follower ≟ x | followee ≟ y
... | yes p | yes q =
  trans (sym absent) (trans (cong (f follower) q) (cong (λ z → f z y) p))
... | yes p | no ¬q = refl
... | no ¬p | q = refl

-- The timeline's follows-layer (follows-post-author, Twitter.agda:366) answers TRUE on a post
-- whose author the session user follows: the positive half of get-personal-timeline's filterᵇ.
follows-post-author-true :
  ∀ {w : World} {user : String} {pid : PostId} {post} →
  World.post-at w pid ≡ just post →
  World.follows w user (Post.author post) ≡ true →
  follows-post-author w user pid ≡ true
follows-post-author-true {w} {user} {pid} pa h rewrite pa = h

-- Membership in a filtered list carries the decision's YES-proof (the with-abstraction pins
-- filter's own scrutinee, so here's element is rigid and hands the proof over).
∈-filter-crp-yes :
  ∀ {w : World} {sid : SessionId} {xs : List PostId} {pid : PostId} →
  pid ∈ filter (can-read-post w sid) xs → CanReadPost w sid pid
∈-filter-crp-yes {w} {sid} {[]} {pid} ()
∈-filter-crp-yes {w} {sid} {x ∷ xs} {pid} m with can-read-post w sid x | m
... | yes cr | here = cr
... | yes _ | there m′ = ∈-filter-crp-yes {w} {sid} {xs} m′
... | no ¬cr | m′ = ∈-filter-crp-yes {w} {sid} {xs} m′

∈-filterᵇ-yes :
  ∀ {f : PostId → Bool} {xs : List PostId} {pid : PostId} →
  pid ∈ filterᵇ f xs → f pid ≡ true
∈-filterᵇ-yes {f} {[]} {pid} ()
∈-filterᵇ-yes {f} {x ∷ xs} {pid} m with f x in fx | m
... | true | here rewrite sym fx = refl
... | true | there m′ = ∈-filterᵇ-yes {f} {xs} m′
... | false | m′ = ∈-filterᵇ-yes {f} {xs} m′

∈-filter-puc-yes :
  ∀ {w : World} {xs : List PostId} {pid : PostId} →
  pid ∈ filter (is-post-public w) xs →
  ∃[ post ] World.post-at w pid ≡ just post
            ∧ Post.visibility post ≡ everyone
            ∧ Post.status post     ≡ live
∈-filter-puc-yes {w} {[]} {pid} ()
∈-filter-puc-yes {w} {x ∷ xs} {pid} m with is-post-public w x | m
... | yes pr | here = pr
... | yes _ | there m′ = ∈-filter-puc-yes {w} {xs} m′
... | no ¬pr | m′ = ∈-filter-puc-yes {w} {xs} m′

-- Contradiction on a Bool proved both ways, phrased with the Bool generalized so both index
-- pairs are constructor pairs (absurd patterns on stuck equalities are rejected).
contra-Bool : (b : Bool) → b ≡ true → b ≡ false → ⊥
contra-Bool true h ()
contra-Bool false () fx

-- Forward direction: a readable id that is in newest-first survives both filters, and an n that
-- covers the filtered list keeps every id (the take-prefix claim of prop_follow_gates_timeline).
∈-filterᵇ-keep :
  ∀ {f : PostId → Bool} {xs : List PostId} {pid : PostId} →
  f pid ≡ true → pid ∈ xs → pid ∈ filterᵇ f xs
∈-filterᵇ-keep {f} {[]} {pid} h ()
∈-filterᵇ-keep {f} {x ∷ xs} {pid} h m with m | f x in fx
... | here | true = here
... | here | false = ⊥-elim (contra-Bool (f x) h fx)
... | there m′ | true = there (∈-filterᵇ-keep {f} {xs} h m′)
... | there m′ | false = ∈-filterᵇ-keep {f} {xs} h m′

∈-filter-crp-keep :
  ∀ {w : World} {sid : SessionId} {xs : List PostId} {pid : PostId}
    {cr : CanReadPost w sid pid} →
  can-read-post w sid pid ≡ yes cr →
  pid ∈ xs →
  pid ∈ filter (can-read-post w sid) xs
∈-filter-crp-keep {w} {sid} {[]} {pid} {cr} eq ()
∈-filter-crp-keep {w} {sid} {x ∷ xs} {pid} {cr} eq m with m | can-read-post w sid x
... | here | yes _ = here
... | here | no ¬cr′ = ⊥-elim (¬cr′ cr)
... | there m′ | yes _ = there (∈-filter-crp-keep {w} {sid} {xs} eq m′)
... | there m′ | no _ = ∈-filter-crp-keep {w} {sid} {xs} eq m′

∈-take-lem :
  ∀ {xs : List PostId} {pid : PostId} (n : ℕ) →
  length xs ≤ n → pid ∈ xs → pid ∈ take n xs
∈-take-lem {[]} {pid} n le ()
∈-take-lem {x ∷ xs} {pid} zero () m
∈-take-lem {x ∷ xs} {pid} (suc n) (s≤s le) here = here
∈-take-lem {x ∷ xs} {pid} (suc n) (s≤s le) (there m) =
  there (∈-take-lem {xs} {pid} n le m)

-- A readable post is LIVE at the id it is readable at, on either CanReadPost constructor.
crp-live :
  ∀ {w : World} {sid : SessionId} {pid : PostId} →
  (cr : CanReadPost w sid pid) →
  ∃[ post ] World.post-at w pid ≡ just post × Post.status post ≡ live
crp-live {w} {sid} {pid} (post-is-private {post = pst} vs pa _ st _) = pst , (pa , st)
crp-live {w} {sid} {pid} (post-is-public {post = pst} vs pa _ st) = pst , (pa , st)

--------------------------------------------------------------------------------
-- (RV8a) prop_unlike_ok (spec unlike-post, Twitter.agda:621): a VALID session that can READ pid's
-- post, whose likes ALREADY carry the session user, answers success (the Step's result index pins it)
-- and the after-world differs from the before-world in ONE cell: pid's post drops EXACTLY the session
-- user from Post.likes and keeps author/text/visibility/status/replies/parent, and every OTHER post,
-- the accounts, the sessions, the follow relation and newest-first are carried outright -- the field-
-- wise reading of Rust's nw == want (step's Unlike arm retainS over pid's cell only, model.rs:948-961).
th-prop-unlike-ok :
  ∀ {before after sid pid acc user} →
  ValidSession before sid acc user →
  CanReadPost before sid pid →
  Step before (unlike sid pid) after success →
  ∃[ bp ] ∃[ ap ]
    World.post-at before pid ≡ just bp
    × World.post-at after pid ≡ just ap
    × (user ∈ Post.likes bp → user ∉ Post.likes ap)
    × (∀ {user′} → user ≢ user′ →
         (user′ ∈ Post.likes ap → user′ ∈ Post.likes bp)
         ∧ (user′ ∉ Post.likes ap → user′ ∉ Post.likes bp))
    × Post.author bp ≡ Post.author ap
    × Post.text bp ≡ Post.text ap
    × Post.visibility bp ≡ Post.visibility ap
    × Post.status bp ≡ Post.status ap
    × Post.replies bp ≡ Post.replies ap
    × Post.parent bp ≡ Post.parent ap
    × (∀ {other} → pid ≢ other →
         World.post-at before other ≡ World.post-at after other
         ∧ World.account-at before ≡ World.account-at after
         ∧ World.session-at before ≡ World.session-at after
         ∧ World.follows before ≡ World.follows after
         ∧ World.newest-first before ≡ World.newest-first after)
th-prop-unlike-ok {before} {after} {sid} {pid} {acc} {user} vs crp
  (unlike-post {post = ap} {post' = bp}
   vs₁ cr₁ pb′ pa′ ∉₁ a t v s r p oth rest) =
  bp , (ap , (pb′ , (pa′ , ((λ _ → ∉-cong eu refl ∉₁) ,
    ((λ { neq → oth (λ eq → neq (trans (sym eu) eq)) }) ,
     (a , (t , (v , (s , (r , (p , rest)))))))))))
  where
    eu = sym (active-injective
               (trans (sym (ValidSession.session-unchanged vs))
                      (ValidSession.session-unchanged vs₁)))

--------------------------------------------------------------------------------
-- (RV8b) prop_unlike_denied (spec failed-unlike-post, Twitter.agda:649): a VALID session that
-- cannot READ the post is DENIED and the world is carried outright (Rust's res == Denied && nw == w:
-- step's can_read guard at model.rs:949 returns (w.clone(), Denied) before any rebuild).
th-prop-unlike-denied :
  ∀ {before sid pid acc user} →
  ValidSession before sid acc user →
  ¬ CanReadPost before sid pid →
  Step before (unlike sid pid) before denied
th-prop-unlike-denied = failed-unlike-post

--------------------------------------------------------------------------------
-- (RV8c) prop_unfollow (spec unfollow-user, Twitter.agda:669 + the set semantics of remove-follower):
-- ANY valid session drops the exact (session-user, followee) pair; the after-world is BUILT here as
-- before with that one relation replaced by remove-follower, so -- like Rust's follows.retain -- the
-- step is idempotent, every other pair agrees pointwise, and every other section (accounts, sessions,
-- posts, newest-first, both used-id lists) is carried outright.
th-prop-unfollow :
  ∀ {before sid acc follower followee} →
  ValidSession before sid acc follower →
  ∃[ after ] ∃[ result ]
    Step before (unfollow sid followee) after result
  × result ≡ success
  × World.follows after follower followee ≡ false
  × World.follows after ≡ remove-follower (World.follows before) follower followee
  × World.account-at before ≡ World.account-at after
  × World.session-at before ≡ World.session-at after
  × World.post-at before ≡ World.post-at after
  × World.newest-first before ≡ World.newest-first after
  × World.used-post-ids before ≡ World.used-post-ids after
  × World.used-session-ids before ≡ World.used-session-ids after
  × (∀ {f g : String} → f ≢ follower ⊎ g ≢ followee →
       World.follows before f g ≡ World.follows after f g)
  × (World.follows before follower followee ≡ false →
       ∀ {f g : String} → World.follows after f g ≡ World.follows before f g)
th-prop-unfollow
  {before = before@(world account-at session-at post-at follows newest-first
            used-post-ids used-session-ids only-used-pids only-used-sids
            only-valid-sessions only-valid-posts only-valid-replies
            no-duplicate-replies no-duplicate-likes no-duplicate-posts)}
  {sid} {acc} {follower} {followee} vs =
  after , (success ,
    (unfollow-user vs refl refl refl refl refl , (refl , (remove-follower-self follows follower followee ,
      (refl , (refl , (refl , (refl , (refl , (refl , (refl , (other , idem))))))))))))
  where
    after : World
    after = world account-at
                  session-at
                  post-at
                  (remove-follower follows follower followee)
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
    other : ∀ {f g : String} → f ≢ follower ⊎ g ≢ followee →
            World.follows before f g ≡ World.follows after f g
    other {f} {g} h = sym (remove-follower-other follows follower followee f g h)
    idem : World.follows before follower followee ≡ false →
           ∀ {f g : String} → World.follows after f g ≡ World.follows before f g
    idem absent {f} {g} = remove-follower-idem follows follower followee absent f g

--------------------------------------------------------------------------------
-- (RV8d) prop_follow_gates_timeline: a session that already follows the AUTHOR of a live FOLLOWERS-
-- ONLY post clears the gate.  (1) CanReadPost holds POSITIVELY through CanReadPost.post-is-private
-- (Twitter.agda:173), the visibility/status/follows premises being exactly the constructor's premises;
-- (2) the post is in the personal timeline (get-personal-timeline, Twitter.agda:557): its id survives
-- BOTH filters (the can-read layer through the spec's own can-read-post decision, which is the Dec the
-- Rust can_read answers yes?/no? of -- the same Dec-vs-Dec relation th-ix-predicates pins) and an n
-- covering the filtered list keeps it in the take-prefix; (3) Like takes its success path so the
-- session user lands in the post's likes (th-prop-like-ok's inversion) and NO like-derivation with a
-- readable post is denied; (4) the timeline command carries the world outright (Rust's nw == w).
th-prop-follow-gate :
  ∀ {before after n sid pid acc user post} →
  ValidSession before sid acc user →
  World.post-at before pid ≡ just post →
  Post.visibility post ≡ followers-only →
  Post.status post ≡ live →
  World.follows before user (Post.author post) ≡ true →
  pid ∈ World.newest-first before →
  (∃[ cr ] can-read-post before sid pid ≡ yes cr) →
  length (filterᵇ (follows-post-author before user)
                  (filter (can-read-post before sid) (World.newest-first before))) ≤ n →
  CanReadPost before sid pid
  × pid ∈ take n (filterᵇ (follows-post-author before user)
                        (filter (can-read-post before sid) (World.newest-first before)))
  × (∀ {ap} → World.post-at after pid ≡ just ap →
       Step before (like sid pid) after success → user ∈ Post.likes ap)
  × (∀ {after′} → Step before (like sid pid) after′ denied → ¬ CanReadPost before sid pid)
  × (∀ {tl} → Step before (read-personal-timeline sid n) before (returned-timeline tl) →
       tl ≡ take n (filterᵇ (follows-post-author before user)
                      (filter (can-read-post before sid) (World.newest-first before))))
  × (∀ {after′ tl} → Step before (read-personal-timeline sid n) after′ (returned-timeline tl) →
       after′ ≡ before)
th-prop-follow-gate
  {before} {after} {n} {sid} {pid} {acc} {user} {post = pst}
  vs pa vis st fu mem (cr , eq) len =
  (post-is-private vs pa vis st fu) ,
  ((∈-take-lem {filterᵇ (follows-post-author before user)
                  (filter (can-read-post before sid) (World.newest-first before))}
                {pid} n len
      (∈-filterᵇ-keep {f = follows-post-author before user}
        (follows-post-author-true {before} {user} {pid} {pst} pa fu)
        (∈-filter-crp-keep {before} {sid} {World.newest-first before} {pid} {cr} eq mem))) ,
   (((λ { pa′ step → th-prop-like-ok vs pa pa′ step }) ,
     ((λ { (failed-like-post _ ncr) → ncr }) ,
      (((λ { (get-personal-timeline {user = u} vs′) →
    cong (λ h → take n (filterᵇ h (filter (can-read-post before sid) (World.newest-first before))))
         (cong (follows-post-author before)
               (sym (active-injective
                      (trans (sym (ValidSession.session-unchanged vs))
                             (ValidSession.session-unchanged vs′))))) }) ,
        λ { (get-personal-timeline vs′) → refl }))))))

--------------------------------------------------------------------------------
-- (RV8e) prop_timeline_excludes_deleted, PERSONAL branch (get-personal-timeline, Twitter.agda:557):
-- every id the timeline returns sits at a LIVE, READABLE post, is a member of newest-first (newest-
-- first ORDER), and the result is a PREFIX -- take n of the filtered newest-first -- of length <= n;
-- the world is carried outright.  Membership is read through the two filter layers (∈-take / ∈-filterᵇ
-- / ∈-filter-crp) and reflected back through their YES-proofs.
th-prop-timeline-excludes :
  ∀ {before n sid acc user pid} →
  ValidSession before sid acc user →
  pid ∈ take n (filterᵇ (follows-post-author before user)
                        (filter (can-read-post before sid) (World.newest-first before))) →
  CanReadPost before sid pid
  × follows-post-author before user pid ≡ true
  × pid ∈ World.newest-first before
  × (∃[ post ] (World.post-at before pid ≡ just post × Post.status post ≡ live))
  × length (take n (filterᵇ (follows-post-author before user)
                        (filter (can-read-post before sid) (World.newest-first before)))) ≤ n
  × (∀ {tl} → Step before (read-personal-timeline sid n) before (returned-timeline tl) →
       tl ≡ take n (filterᵇ (follows-post-author before user)
                      (filter (can-read-post before sid) (World.newest-first before))))
  × (∀ {after′ tl} → Step before (read-personal-timeline sid n) after′ (returned-timeline tl) →
       after′ ≡ before)
th-prop-timeline-excludes {before} {n} {sid} {acc} {user} {pid} vs m =
  (∈-filter-crp-yes {w = before} {sid} {xs = World.newest-first before} {pid = pid}
    (∈-filterᵇ {f = follows-post-author before user} {xs = filter (can-read-post before sid) (World.newest-first before)} {pid = pid} (∈-take {xs = filterᵇ (follows-post-author before user) (filter (can-read-post before sid) (World.newest-first before))} {pid = pid} n m))) ,
  ((∈-filterᵇ-yes {f = follows-post-author before user} {xs = filter (can-read-post before sid) (World.newest-first before)} {pid = pid} (∈-take {xs = filterᵇ (follows-post-author before user) (filter (can-read-post before sid) (World.newest-first before))} {pid = pid} n m)) ,
   ((∈-filter-crp {w = before} {sid} {xs = World.newest-first before} {pid = pid}
     (∈-filterᵇ {f = follows-post-author before user} {xs = filter (can-read-post before sid) (World.newest-first before)} {pid = pid} (∈-take {xs = filterᵇ (follows-post-author before user) (filter (can-read-post before sid) (World.newest-first before))} {pid = pid} n m))) ,
    (tl-exists ,
    (take-len
       {xs = filterᵇ (follows-post-author before user) (filter (can-read-post before sid) (World.newest-first before))} n ,
     (((λ { (get-personal-timeline {user = u} vs′) →
    cong (λ h → take n (filterᵇ h (filter (can-read-post before sid) (World.newest-first before))))
        (cong (follows-post-author before)
              (sym (active-injective
                     (trans (sym (ValidSession.session-unchanged vs))
                            (ValidSession.session-unchanged vs′))))) }) ,
       λ { (get-personal-timeline vs′) → refl }))))))
  where
  tl-exists : (∃[ post ] (World.post-at before pid ≡ just post × Post.status post ≡ live))
  tl-exists =
    crp-live {w = before} {sid} {pid = pid} (∈-filter-crp-yes {w = before} {sid} {xs = World.newest-first before} {pid = pid}
              (∈-filterᵇ {f = follows-post-author before user} {xs = filter (can-read-post before sid) (World.newest-first before)} {pid = pid} (∈-take {xs = filterᵇ (follows-post-author before user) (filter (can-read-post before sid) (World.newest-first before))} {pid = pid} n m)))

--------------------------------------------------------------------------------
-- (RV8f) prop_timeline_excludes_deleted, ANON-GLOBAL branch (get-public-global-timeline, Twitter.agda
-- 583): the ids returned anonymously sit at publicly-readable (live, everyone) posts, are newest-first
-- members, and the list is a take-prefix of length <= n.
th-prop-timeline-excludes-anon :
  ∀ {before n pid} →
  pid ∈ take n (filter (is-post-public before) (World.newest-first before)) →
  (∃[ post ] (World.post-at before pid ≡ just post
            ∧ Post.visibility post ≡ everyone
            ∧ Post.status post     ≡ live))
  × pid ∈ World.newest-first before
  × length (take n (filter (is-post-public before) (World.newest-first before))) ≤ n
  × (∀ {tl} → Step before (read-global-timeline nothing n) before (returned-timeline tl) →
       tl ≡ take n (filter (is-post-public before) (World.newest-first before)))
  × (∀ {after′ tl} → Step before (read-global-timeline nothing n) after′ (returned-timeline tl) →
       after′ ≡ before)
th-prop-timeline-excludes-anon {before} {n} {pid} m =
  (pp-exists ,
   ((∈-filter-puc {w = before} {xs = World.newest-first before} {pid = pid} (∈-take {xs = filter (is-post-public before) (World.newest-first before)} {pid = pid} n m)) ,
    (take-len {xs = filter (is-post-public before) (World.newest-first before)} n ,
     (((λ { (get-public-global-timeline) → refl }) ,
       λ { (get-public-global-timeline) → refl })))))
  where
  pp-exists : (∃[ post ] (World.post-at before pid ≡ just post
                ∧ Post.visibility post ≡ everyone
                ∧ Post.status post     ≡ live))
  pp-exists = ∈-filter-puc-yes {w = before} {xs = World.newest-first before} {pid = pid} (∈-take {xs = filter (is-post-public before) (World.newest-first before)} {pid = pid} n m)
