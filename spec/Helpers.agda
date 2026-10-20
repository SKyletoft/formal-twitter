module Helpers where

open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Vec using (Vec; lookup; []; _∷_)
open import Equality
open import Monad as Monad_

open Eq {{...}}
open Monad {{...}}

_×_ : Set → Set → Set
a × b = Σ a (λ _ → b)

infixr 2 _×_

to-fin : (n : Nat) → Fin (suc n)
to-fin zero = zero
to-fin (suc x) = suc (to-fin x)

to-nat : {n : Nat} → Fin n → Nat
to-nat zero = zero
to-nat (suc n) = suc (to-nat n)

weaken : {n : Nat} → Fin n → Fin (suc n)
weaken zero = zero
weaken (suc n) = suc (weaken n)

_:::_ : {n : Nat} {a : Set} → Vec a n → a → Vec a (suc n)
[] ::: y = y ∷ []
(x ∷ xs) ::: y = x ∷ (xs ::: y)

bounds-check : {n : Nat} → Nat → Maybe (Fin n)
bounds-check {zero} _        = nothing
bounds-check {suc n} zero    = just zero
bounds-check {suc n} (suc m) = map suc (bounds-check {n} m)

member? : {a : Set} {{_ : Eq a}} → a → List a → Bool
member? _ [] = false
member? x (y ∷ ys) = (y == x) ∨ member? x ys
