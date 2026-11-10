module Proofs (SessionId PostId : Set) where

open import Twitter SessionId PostId

open import Agda.Builtin.Maybe
open import Agda.Builtin.String
open import Agda.Builtin.Sigma

open import Data.Product                          using (∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; trans)
open import Function                              using (_∘_)

private variable a b : Set

infixr 2 _∧_
_∧_ : Set → Set → Set
a ∧ b = Σ a (λ _ → b)

nothing≢just : {x : a} → nothing ≢ just x
nothing≢just ()

post-doesnt-exist-before-posting :
  {sid : SessionId} {txt : String} {pid : PostId} {before after : World} {parent : Maybe PostId} →
  Step before (publish sid txt parent) after (created-post pid) →
  (pid ∉ World.newest-first before) ∧ (World.post-at before pid ≡ nothing)
post-doesnt-exist-before-posting {before = before} (successful-post _ record {was-absent = absent} _ _ _ _ _ _) =
  nothing≢just ∘ trans (sym absent) ∘ snd ∘ World.only-valid-posts before , absent
post-doesnt-exist-before-posting {before = before} (successful-reply _ record {was-absent = absent} _ _ _ _ _ _ _ _ _ _ _ _) =
  nothing≢just ∘ trans (sym absent) ∘ snd ∘ World.only-valid-posts before , absent

-- cant-reply-to-deleted-tweet

-- cant-reply-to-tweet-you-cant-read

-- cant-make-public-reply-to-private-parent

-- cant-make-public-reply-to-private-parent-trans

step-exists :
  ∀ (before : World) (cmd : Command) →
  ∃[ after ] ∃[ result ]
  Step before cmd after result
step-exists w (publish x x₁ x₂) = {!!}
step-exists w (read-post x x₁) = {!!}
step-exists w (read-timeline x x₁) = {!!}
step-exists w (authenticate x x₁) = {!!}
step-exists w (register x x₁) = {!!}
