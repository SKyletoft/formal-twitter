open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe                        using (just; nothing)
open import Agda.Builtin.Sigma
open import Data.Empty                                using (⊥-elim)
open import Data.List                                 using (List; []; _∷_; take; filter; filterᵇ)
open import Data.Product                              using (∃-syntax)
open import Data.String                               using (String; _≟_)
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

-- (4) prop_revoke_token: a successful logout revokes exactly the session that
-- was active for that token before the step (inversion).
th-prop-revoke-logout :
  ∀ {before after sid user} →
  World.session-at before sid ≡ active user →
  Step before (revoke-token sid) after success →
  World.session-at after sid ≡ revoked
th-prop-revoke-logout h (logout _ h₂ _) = h₂

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
