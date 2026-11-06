module Proofs (SessionId PostId : Set) where

open import Twitter SessionId PostId

open import Agda.Builtin.Maybe
open import Agda.Builtin.String
open import Agda.Builtin.Sigma

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; trans)
open import Function                              using (_∘_)

private variable a b : Set

infixr 2 _∧_
_∧_ : Set → Set → Set
a ∧ b = Σ a (λ _ → b)

nothing≢just : {x : a} → nothing ≢ just x
nothing≢just ()

post-doesnt-exist-before-posting :
  {sid : SessionId} {txt : String} {pid : PostId} {before after : World} →
  Step before (publish sid txt) after (created-post pid) →
  (pid ∉ World.newest-first before) ∧ (World.post-at before pid ≡ nothing)
post-doesnt-exist-before-posting {before = before} (successful-post _ record {was-absent = absent} _ _ _ _ _ _) =
  nothing≢just ∘ trans (sym absent) ∘ snd ∘ World.only-valid-posts before , absent
