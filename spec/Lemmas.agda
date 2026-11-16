open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma


open import Data.String                           using (String)
                                                  renaming (_≟_ to _≟ₛ_)
open import Data.Empty                            using (⊥-elim)
open import Data.Unit                             using (tt)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no)
open import Relation.Nullary.Negation.Core        using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Data.Product                          using (∃-syntax)

open import Helpers

module Lemmas where

nothing≢just : ∀ {x : a} → nothing ≢ just x ; nothing≢just {_} ()

∈[] : ∀ {x : a} → ¬ (x ∈ []) ; ∈[] {_} ()

∉-head : ∀ {x y : a} {xs : List a} → x ∉ (y ∷ xs) → x ≢ y
∉-head neq refl = neq here

∉-tail : ∀ {x y : a} {xs : List a} → x ∉ (y ∷ xs) → x ∉ xs
∉-tail neq m = neq (there m)

∈-sym : ∀ {x y : a} {xs : List a} → x ≡ y → y ∈ xs → x ∈ xs ; ∈-sym refl m∈ = m∈

∉-prepend : ∀ {x y : a} {xs : List a} → x ≢ y → x ∉ xs → x ∉ (y ∷ xs)
∉-prepend ne ne′ m∈ with m∈
... | here      = ne refl
... | there m∈′ = ne′ m∈′

∈-decidable : (x : String) (xs : List String) → Dec (x ∈ xs)
∈-decidable x [] = no λ { () }
∈-decidable x (y ∷ ys) with x ≟ₛ y
... | yes refl = yes here
... | no x≢y with ∈-decidable x ys
...   | yes x∈ys = yes (there x∈ys)
...   | no x∉ys = no (∉-prepend x≢y x∉ys)

uniq-cons : (x : a) (xs : List a) → x ∉ xs → uniq xs → uniq (x ∷ xs)
uniq-cons x xs x∉xs u = x∉xs , u

uniq-≡[] : (xs : List a) → xs ≡ [] → uniq xs ; uniq-≡[] xs refl = tt

Dec-elim : ∀ {a b} {A : Set a} {B : Set b} →
  Dec A → (A → B) → (¬ A → B) → B
Dec-elim (yes p) f g = f p
Dec-elim (no ¬p) f g = g ¬p

∈-not-head : ∀ {x y : a} {xs : List a} → x ≢ y → x ∈ y ∷ xs → x ∈ xs
∈-not-head ne here     = ⊥-elim (ne refl)
∈-not-head ne (there m) = m

∉-distinct : ∀ {xs : List a} {f : a → Maybe b} {pid : a} →
  f pid ≡ nothing →
  (∀ {z} → z ∈ xs → ∃[ post ] f z ≡ just post) →
  ∀ {pid'} → pid' ∈ xs → pid ≢ pid'
∉-distinct {f = f} {pid = pid} absent F m e =
  let post' , eq = F m
  in nothing≢just (trans (sym absent) (subst (λ z → f z ≡ just post') (sym e) eq))

∉-witnessed : ∀ {xs : List a} {f : a → Maybe b} {pid : a} →
  f pid ≡ nothing →
  (∀ {z} → z ∈ xs → ∃[ post ] f z ≡ just post) →
  pid ∉ xs
∉-witnessed absent F m = ∉-distinct absent F m refl

remove-like : (user : a) (pl : List a) → user ∈ pl → List a
remove-like user (y ∷ ys) here       = ys
remove-like user (y ∷ ys) (there p) = y ∷ remove-like user ys p

∈-splice : ∀ {user user′ : a} {pl : List a} {p : user ∈ pl} →
           user′ ∈ remove-like user pl p → user′ ∈ pl
∈-splice {p = here} m∈ = there m∈
∈-splice {pl = y ∷ ys} {p = there p′} m∈ with m∈
... | here          = here
... | there m∈′     = there (∈-splice {p = p′} m∈′)

∈-remove : ∀ {user user′ : a} {pl : List a} {p : user ∈ pl} →
           user ≢ user′ → user′ ∈ pl → user′ ∈ remove-like user pl p
∈-remove {p = here} ne m∈ with m∈
... | here          = ⊥-elim (ne refl)
... | there m∈′     = m∈′
∈-remove {pl = y ∷ ys} {p = there p′} ne m∈ with m∈
... | here          = here
... | there m∈′     = there (∈-remove {p = p′} ne m∈′)

∉-splice : ∀ {user user′ : a} {pl : List a} {p : user ∈ pl} →
           user ≢ user′ → user′ ∉ remove-like user pl p → user′ ∉ pl
∉-splice ne m∉ m∈ = m∉ (∈-remove ne m∈)

remove-transport :
  ∀ {user user′ : a} {pl : List a} {p : user ∈ pl} →
  user ≢ user′ →
  (user′ ∈ remove-like user pl p → user′ ∈ pl)
  ∧ (user′ ∉ remove-like user pl p → user′ ∉ pl)
remove-transport ne = ∈-splice , ∉-splice ne

remove-loses : ∀ {user : a} {pl : List a} (p : user ∈ pl) →
               uniq pl → user ∉ remove-like user pl p
remove-loses here (y∉ys , u) = y∉ys
remove-loses (there p′) (y∉ys , u-ys) m∈ with m∈
... | here              = y∉ys p′
... | there m∈′         = remove-loses p′ u-ys m∈′

remove-uniq : ∀ {user : a} {pl : List a} (p : user ∈ pl) →
              uniq pl → uniq (remove-like user pl p)
remove-uniq here (y∉ys , u-ys) = u-ys
remove-uniq (there p′) (y∉ys , u-ys) =
    (λ m∈ → y∉ys (∈-splice {p = p′} m∈)) , remove-uniq p′ u-ys
