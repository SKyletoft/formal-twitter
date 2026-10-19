module Proofs where

open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.String
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

open import Twitter

unwrap : ValidState → State
unwrap (VS s) = s

twitter-is-valid : ((VS old-state) : ValidState)
                 → (a : Action)
                 → Σ ValidState (λ (VS new-state) → new-state ≡ fst (event-loop old-state a))
twitter-is-valid vs a = vs , refl

tweeting-returns-a-tweet-reference : ((VS s) : ValidState) → (u1 : UserId) → (t : String) → Σ Nat (λ n → snd (event-loop s (tweet u1 t)) ≡ tweet-id (tweet n))
tweeting-returns-a-tweet-reference = {!!}

cant-delete-others-tweets : ((VS s) : ValidState)
                          → (u1 : UsnerId)
                          → (t : String)
                          → (u2 : UserId)
                          → (let a1 = tweet u1 t
                                 s' , r = event-loop s a1
                                 a2 = delete-tweet u2 {!!}
                                 s'' , _ = event-loop s' a2
                            in s' ≡ s'')
cant-delete-others-tweets = {!!}

-- liking-twice-does-nothing : ValidState → Σ ValidState (λ vs → {!!})
