open import Agda.Builtin.List
open import Agda.Builtin.Sigma


open import Data.Unit                             using (⊤)
open import Level                                 using (_⊔_)
open import Relation.Nullary.Negation.Core        using (¬_)

module Helpers where

variable a b c : Set

infix 4 _∈_ _∉_
data _∈_ (x : a) : List a → Set where
  here  : ∀ {xs}            → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

_∉_ : (x : a) → List a → Set
x ∉ y = ¬ (x ∈ y)

infixr 2 _×_ _∧_
_×_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
a × b = Σ a (λ _ → b)

_∧_ = _×_

uniq : List a → Set
uniq []       = ⊤
uniq (x ∷ xs) = (x ∉ xs) × uniq xs

CreateNew : Set → Set
CreateNew element =
  (us : List element) →
  Σ ((List element) × element) (λ { (us' , sid) → sid ∉ us ∧
                                                  sid ∈ us' ∧
                                                  (∀ {s} → s ∈ us → s ∈ us') })
