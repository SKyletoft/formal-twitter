module Helpers where

open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Maybe

open import Data.Empty                            using (⊥; ⊥-elim)
open import Data.Unit                             using (⊤; tt)
open import Level                                 using (_⊔_)
open import Relation.Nullary.Negation.Core        using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong;
                                                         cong₂; trans; sym)
open import Data.Product                          using (∃-syntax)

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

-- Transport of membership / uniqueness along a list equality
∈-cong : (x : a) (m n : List a) → m ≡ n → x ∈ m → x ∈ n
∈-cong x m n refl m∈ = m∈

∈[] : (x : a) → x ∈ [] → ⊥
∈[] x ()

uniq-transport : (m n : List a) → m ≡ n → uniq m → uniq n
uniq-transport m n refl u = u

uniq-cons : (x : a) (xs : List a) → x ∉ xs → uniq xs → uniq (x ∷ xs)
uniq-cons x xs x∉xs u = x∉xs , u

uniq-≡[] : (xs : List a) → xs ≡ [] → uniq xs
uniq-≡[] xs refl = tt

CreateNew : Set → Set
CreateNew element =
  (us : List element) →
  Σ ((List element) × element) (λ { (us' , sid) → sid ∉ us ∧
                                                  sid ∈ us' ∧
                                                  (∀ {s} → s ∈ us → s ∈ us') })

id : ∀ {ℓ} → Set ℓ → Set ℓ
id x = x
