open import Agda.Builtin.List
open import Agda.Builtin.Sigma


open import Data.Empty                            using (⊥-elim)
open import Function                              using (_∘_; _$_)
open import Relation.Binary.Definitions           using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no)

open import Helpers
open import Lemmas

module Update
  (Key : Set)
  (_≟_ : DecidableEquality Key)
  (Value : Set)
  (default : Value)
  where

update : (Key → Value) → Key → Value → Key → Value
update f k v k′ with k ≟ k′
... | yes _ = v
... | no  _ = f k′

update-same : ∀ {f : Key → Value} {k : Key} {v : Value} → update f k v k ≡ v
update-same {k = k} with k ≟ k
... | yes _  = refl
... | no ne = ⊥-elim (ne refl)

update-at : ∀ {f : Key → Value} {k : Key} {v : Value} {k′ : Key} →
  k ≡ k′ → update f k v k′ ≡ v
update-at {f = f} {k = k} {v = v} {k′ = k′} eq =
  subst (λ z → update f k v z ≡ v) eq update-same

update-no : ∀ {f : Key → Value} {k : Key} {v : Value} {k′ : Key} →
  k ≢ k′ → update f k v k′ ≡ f k′
update-no {k = k} {k′ = k′} ne with k ≟ k′
... | yes eq = ⊥-elim (ne eq)
... | no _   = refl

update-no-¬ : ∀ {f : Key → Value} {k : Key} {v : Value} {k′ : Key} →
  k ≢ k′ → f k′ ≢ default → update f k v k′ ≢ default
update-no-¬ {f = f} {k = k} {v = v} {k′ = k′} ne nu eq =
  nu (trans (sym (update-no ne)) eq)

update-used : ∀ {us : List Key} {f : Key → Value} {k : Key} (v : Value) →
  v ≢ default →
  k ∉ us →
  (∀ {z} → (z ∈ us → f z ≢ default) ∧ (z ∉ us → f z ≡ default)) →
  ∀ {k′} →
  (k′ ∈ k ∷ us → update f k v k′ ≢ default) ∧
  (k′ ∉ k ∷ us → update f k v k′ ≡ default)
update-used {us = us} {f = f} {k = k} v v≢d ∉w fs {k′} = F′ , S′
  where
    ne-tail : k′ ∈ us → k ≢ k′
    ne-tail m e = ∉w (∈-sym e m)

    F′ : k′ ∈ k ∷ us → update f k v k′ ≢ default
    F′ here      = λ eq → v≢d (sym (trans (sym eq) update-same))
    F′ (there m) = λ eq → fst (fs {k′}) m (trans (sym (update-no (ne-tail m))) eq)

    S′ : k′ ∉ k ∷ us → update f k v k′ ≡ default
    S′ nm = trans (update-no (∉-head nm ∘ sym)) (snd (fs {k′}) (∉-tail nm))

update-used-keep : ∀ {us : List Key} {f : Key → Value} {k : Key} {v₀ : Value} (v₁ : Value) →
  f k ≡ v₀ →
  v₀ ≢ default →
  v₁ ≢ default →
  (∀ {z} → (z ∈ us → f z ≢ default) ∧ (z ∉ us → f z ≡ default)) →
  ∀ {k′} →
  (k′ ∈ us → update f k v₁ k′ ≢ default) ∧
  (k′ ∉ us → update f k v₁ k′ ≡ default)
update-used-keep {us = us} {f = f} {k = k} {v₀ = v₀} v₁ fk≡v₀ v₀≢d v₁≢d fs {k′} = F′ , S′
  where
    ne : k′ ∉ us → k ≢ k′
    ne nm e = v₀≢d
      $ sym
      ∘ trans (sym (snd (fs {k′}) nm))
      ∘ subst (λ z → f z ≡ v₀) e
      $ fk≡v₀

    F′ : k′ ∈ us → update f k v₁ k′ ≢ default
    F′ m = Dec-elim (k ≟ k′)
      (λ e → λ eq → v₁≢d
                  $ sym
                  ∘ trans (sym eq)
                  ∘ subst (λ z → update f k v₁ z ≡ v₁) e
                  $ update-same)
      (λ n₁ → update-no-¬ n₁ (fst (fs {k′}) m))

    S′ : k′ ∉ us → update f k v₁ k′ ≡ default
    S′ nm = trans (update-no (ne nm)) (snd (fs {k′}) nm)
