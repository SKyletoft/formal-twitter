open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma


open import Data.Product                          using (∃-syntax)
open import Relation.Binary.Definitions           using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)

open import Helpers
open import Lemmas

module Add
  (Key : Set)
  (_≟_ : DecidableEquality Key)
  (W : Set)
  where

open import Update Key _≟_ (Maybe W) nothing

just-inj : ∀ {x y : W} → just x ≡ just y → x ≡ y ; just-inj refl = refl

add : (Key → Maybe W) → Key → W → Key → Maybe W
add f k v k′ = update f k (just v) k′

add-same : ∀ {f : Key → Maybe W} {k : Key} {v : W} → add f k v k ≡ just v
add-same {k = k} = update-same {k = k}

add-at : ∀ {f : Key → Maybe W} {k : Key} {v : W} {k′ : Key} →
  k ≡ k′ → add f k v k′ ≡ just v
add-at {f = f} {k = k} {v = v} {k′ = k′} eq =
  subst (λ z → add f k v z ≡ just v) eq add-same

add-no : ∀ {f : Key → Maybe W} {k : Key} {v : W} {k′ : Key} →
  k ≢ k′ → add f k v k′ ≡ f k′
add-no {k = k} {k′ = k′} ne = update-no {k = k} {k′ = k′} ne

add-inj : ∀ {f : Key → Maybe W} {k k′ : Key} {v w : W} →
  add f k v k′ ≡ just w → k ≡ k′ → w ≡ v
add-inj {k = k} {k′ = k′} eq refl = just-inj (trans (sym eq) add-same)

add-used : ∀ {us : List Key} {f : Key → Maybe W} {k : Key} {v : W} →
  k ∉ us →
  (∀ {z} → (z ∈ us → f z ≢ nothing) ∧ (z ∉ us → f z ≡ nothing)) →
  ∀ {k′} →
  (k′ ∈ k ∷ us → add f k v k′ ≢ nothing) ∧
  (k′ ∉ k ∷ us → add f k v k′ ≡ nothing)
add-used {k = k} {v = v} ∉w fs =
  update-used (just v) (λ eq → nothing≢just (sym eq)) ∉w fs

add-used-keep : ∀ {us : List Key} {f : Key → Maybe W} {k : Key} {v₀ : W} (v₁ : W) →
  f k ≡ just v₀ →
  (∀ {z} → (z ∈ us → f z ≢ nothing) ∧ (z ∉ us → f z ≡ nothing)) →
  ∀ {k′} →
  (k′ ∈ us → add f k v₁ k′ ≢ nothing) ∧
  (k′ ∉ us → add f k v₁ k′ ≡ nothing)
add-used-keep {k = k} {v₀ = v₀} v₁ fk≡ fs =
  update-used-keep (just v₁) fk≡
    (λ eq → nothing≢just (sym eq)) (λ eq → nothing≢just (sym eq)) fs

add-posts : ∀ {us : List Key} {f : Key → Maybe W} {k : Key} {v : W} →
  (∀ {z} → z ∈ us → ∃[ w ] f z ≡ just w) →
  (∀ {k′} → k′ ∈ us → k ≢ k′) →
  ∀ {k′} →
  k′ ∈ k ∷ us →
  ∃[ w ] add f k v k′ ≡ just w
add-posts {k = k} {v = v} F N here = v , add-same
add-posts {k = k} F N {k′} (there m) =
  let w , eq = F m
  in w , trans (add-no (N m)) eq

add-prop : ∀ {ℓ} →
  ∀ {f : Key → Maybe W} {k : Key} (v : W) →
  ∀ {P : W → Set ℓ} →
  P v →
  (∀ {z w} → f z ≡ just w → P w) →
  ∀ {k′ w} → add f k v k′ ≡ just w → P w
add-prop {f = f} {k = k} v {P = P} Pv Fold {k′} {w} eq =
  Dec-elim (k ≟ k′)
    (λ e → subst (λ ww → P ww)
      (just-inj (trans (sym (add-at e)) eq)) Pv)
    (λ ne → Fold (trans (sym (add-no ne)) eq))

add-prop² : ∀ {ℓ} {f : Key → Maybe W} {k k₂ : Key} (v₁ v₂ : W) {P : W → Set ℓ} →
  P v₁ → P v₂ → (∀ {z w} → f z ≡ just w → P w) →
  ∀ {z w} → add (add f k v₁) k₂ v₂ z ≡ just w → P w
add-prop² {f = f} {k = k} {k₂ = k₂} v₁ v₂ {P = P} Pv₁ Pv₂ Fold {z} {w} eq =
  Dec-elim (k₂ ≟ z)
    (λ e → subst (λ ww → P ww)
      (just-inj (trans (sym (add-at e)) eq)) Pv₂)
    (λ ne → add-prop v₁ Pv₁ Fold {z} {w} (trans (sym (add-no ne)) eq))

add-present : ∀ {us : List Key} {f : Key → Maybe W} {k : Key} {v : W} →
  (∀ {z} → z ∈ us → ∃[ w ] f z ≡ just w) →
  ∀ {z} → z ∈ us → ∃[ w ] add f k v z ≡ just w
add-present {f = f} {k = k} {v = v} F {z} m =
  Dec-elim (k ≟ z)
    (λ e → v , add-at e)
    (λ ne → let w , eq = F m in w , trans (add-no ne) eq)

add-witness : ∀ {us : List Key} {f : Key → Maybe W} {k k₂ : Key} (v₁ v₂ : W) →
  (∀ {z} → z ∈ us → ∃[ w ] add f k v₁ z ≡ just w) →
  ∀ {z} → z ∈ us → ∃[ w ] add (add f k v₁) k₂ v₂ z ≡ just w
add-witness {f = f} {k = k} {k₂ = k₂} v₁ v₂ F {z} m =
  Dec-elim (k₂ ≟ z)
    (λ e → v₂ , add-at e)
    (λ ne → let w , eq = F m in w , trans (add-no ne) eq)
