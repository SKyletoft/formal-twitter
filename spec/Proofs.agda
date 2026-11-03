module Proofs (SessionId PostId : Set) where

open import Twitter SessionId PostId

open import Agda.Builtin.Maybe
open import Agda.Builtin.String

open import Data.Empty                            using (⊥; ⊥-elim)
open import Data.Product                          using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; trans)

private variable a b c : Set

record _∧_ a b : Set where
  constructor and
  field
    fst : a
    snd : b

nothing≢just : {x : a} → nothing ≢ just x
nothing≢just ()

post-doesnt-exist-before-posting :
  (sid : SessionId) (txt : String) (pid : PostId) (before after : World) →
  Step before (publish sid txt) after (created-post pid) →
  (pid ∉ World.newest-first before) ∧ (World.post-at before pid ≡ nothing)
post-doesnt-exist-before-posting sid txt pid before after
  (successful-post _ new _ _ _ _ _ _) = and not-in absent
  where
    absent : World.post-at before pid ≡ nothing
    absent = PostIsNew.was-absent new

    not-in : pid ∉ World.newest-first before
    not-in mem with World.only-valid-posts before mem
    ... | (p , eq) = nothing≢just (trans (sym absent) eq)
