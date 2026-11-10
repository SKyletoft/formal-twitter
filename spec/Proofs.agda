module Proofs (SessionId PostId : Set) where

open import Twitter SessionId PostId

open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.String

open import Data.Product                          using (∃-syntax)
open import Function                              using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; refl; sym; trans)
open import Relation.Nullary.Negation.Core        using (¬_)

--------------------------------------------------------------------------------
--                               PROOF-HELPERS                                --
--------------------------------------------------------------------------------

private variable a b : Set

infixr 2 _∧_
_∧_ : Set → Set → Set
a ∧ b = Σ a (λ _ → b)

--------------------------------------------------------------------------------
--                                PROOF-TYPES                                 --
--------------------------------------------------------------------------------

PostDoesntExistBeforePosting =
  ∀ {before after sid pid txt parent} →
  Step before (publish sid txt parent) after (created-post pid) →
  (pid ∉ World.newest-first before) ∧ (World.post-at before pid ≡ nothing)

CantReplyToDeletedTweet =
  ∀ {before after sid txt parent pid post} →
  World.post-at before parent ≡ just post →
  Post.status post            ≡ deleted →
  ¬ Step before (publish sid txt (just parent)) after (created-post pid)

CantReplyToTweetYouCantRead =
  ∀ {before after sid pid txt parent} →
  ¬ CanReadPost before sid parent →
  ¬ Step before (publish sid txt (just parent)) after (created-post pid)

CantMakePublicReplyToPrivateParent =
  ∀ {before after pid sid txt parent post parent-post} →
  World.post-at before parent ≡ just parent-post →
  World.post-at after pid     ≡ just post →
  Post.visibility parent-post ≡ followers-only →
  Post.visibility post        ≡ everyone →
  ¬ Step before (publish sid txt (just parent)) after (created-post pid)

StepExists =
  ∀ (before : World) (cmd : Command) →
  ∃[ after ] ∃[ result ]
  Step before cmd after result

--------------------------------------------------------------------------------
--                                  HELPERS                                   --
--------------------------------------------------------------------------------

nothing≢just : {x : a} → nothing ≢ just x
nothing≢just ()

deleted≢live : deleted ≢ live
deleted≢live ()

everyone≢followers-only : everyone ≢ followers-only
everyone≢followers-only ()

new-reply-private :
  ∀ {username txt user parent-id ppost} →
  Post.visibility ppost ≡ followers-only →
  Post.visibility (new-reply username txt user parent-id ppost) ≡ followers-only
new-reply-private {ppost = record { visibility = everyone }} ()
new-reply-private {ppost = record { visibility = followers-only }} refl = refl

--------------------------------------------------------------------------------
--                                   PROOFS                                   --
--------------------------------------------------------------------------------

post-doesnt-exist-before-posting : PostDoesntExistBeforePosting
post-doesnt-exist-before-posting {before = before} (successful-post _ record {was-absent = absent} _ _ _ _ _ _) =
  nothing≢just ∘ trans (sym absent) ∘ snd ∘ World.only-valid-posts before , absent
post-doesnt-exist-before-posting {before = before} (successful-reply _ record {was-absent = absent} _ _ _ _ _ _ _ _ _ _ _ _) =
  nothing≢just ∘ trans (sym absent) ∘ snd ∘ World.only-valid-posts before , absent

cant-reply-to-deleted-tweet : CantReplyToDeletedTweet
cant-reply-to-deleted-tweet post-at-del status-del
  (successful-reply _ _ _ _ ppost≡ post-at-ppost _ _ _ _ _ _ _ _) with ppost≡
... | refl =
  deleted≢live (trans (sym status-del)
    (cong Post.status
      (just-injective (trans (sym post-at-del) post-at-ppost))))

cant-reply-to-tweet-you-cant-read : CantReplyToTweetYouCantRead
cant-reply-to-tweet-you-cant-read ¬can-read
  (successful-reply _ _ _ can-read _ _ _ _ _ _ _ _ _ _) = ¬can-read can-read

cant-make-public-reply-to-private-parent : CantMakePublicReplyToPrivateParent
cant-make-public-reply-to-private-parent
  post-at-before post-at-after parent-vis post-vis
  (successful-reply {ppost = ppost} _ is-new _ _ _ post-at-ppost _ _ _ _ _ _ _ _) =
  let post≡new = just-injective
        (trans (sym post-at-after) (PostIsNew.is-present is-new))
      vis≡ = cong Post.visibility post≡new
      ppost≡parent = just-injective
        (trans (sym post-at-ppost) post-at-before)
      ppost-vis = trans (cong Post.visibility ppost≡parent) parent-vis
  in everyone≢followers-only
       (trans (sym post-vis)
         (trans vis≡ (new-reply-private ppost-vis)))
