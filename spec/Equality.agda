module Equality where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_)
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.String.Base using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
import Agda.Builtin.Nat as Natᵇ
import Agda.Builtin.String as Stringᵇ
import Data.Bool as Bool
import Data.Nat as Nat
import Data.Fin as Fin
import Data.String as String
import Data.List.Properties as ListProps
import Data.Vec.Properties as VecProps
import Data.Maybe.Properties as MaybeProps
open import Interface using (LoginToken; TweetId; token; tweet; tweet-id)

record Eq (A : Set) : Set where
  infix 4 _≟_ _==_
  field
    _≟_ : (x y : A) → Dec (x ≡ y)
    _==_ : (x y : A) → Bool
open Eq {{...}}

as-bool : {P : Set} → Dec P → Bool
as-bool (yes _)  = true
as-bool (no _)   = false

if_then_else_ : {A : Set} {P : Set} → Dec P → A → A → A
if_then_else_ (yes _) t _ = t
if_then_else_ (no _)  _ f = f

instance
  Bool-Eq : Eq Bool
  Eq._≟_ Bool-Eq = Bool._≟_
  Eq._==_ Bool-Eq = λ x y → (x ∧ y) ∨ (not x ∧ not y)

  Nat-Eq : Eq ℕ
  Eq._≟_ Nat-Eq = Nat._≟_
  Eq._==_ Nat-Eq = Natᵇ._==_

  Fin-Eq : {n : ℕ} → Eq (Fin n)
  Eq._≟_ Fin-Eq = Fin._≟_
  Eq._==_ Fin-Eq = fin-eq
    where
      fin-eq : {n : ℕ} → Fin n → Fin n → Bool
      fin-eq zero zero = true
      fin-eq zero (suc _) = false
      fin-eq (suc _) zero = false
      fin-eq (suc x) (suc y) = fin-eq x y

  String-Eq : Eq String
  Eq._≟_ String-Eq = String._≟_
  Eq._==_ String-Eq = Stringᵇ.primStringEquality

  List-Eq : {A : Set} {{_ : Eq A}} → Eq (List A)
  Eq._≟_ List-Eq = ListProps.≡-dec _≟_
  Eq._==_ List-Eq = list-eq
    where
      list-eq : {A : Set} {{_ : Eq A}} → (x y : List A) → Bool
      list-eq [] [] = true
      list-eq [] (y ∷ _) = false
      list-eq (x ∷ _) [] = false
      list-eq (x ∷ xs) (y ∷ ys) = (x == y) ∧ list-eq xs ys

  Vec-Eq : {A : Set} {{_ : Eq A}} {n : ℕ} → Eq (Vec A n)
  Eq._≟_ Vec-Eq = VecProps.≡-dec _≟_
  Eq._==_ Vec-Eq = v-eq
    where
      v-eq : {A : Set} {{_ : Eq A}} {n : ℕ} → Vec A n → Vec A n → Bool
      v-eq [] [] = true
      v-eq (x ∷ xs) (y ∷ ys) = (x == y) ∧ v-eq xs ys

  Maybe-Eq : {A : Set} {{_ : Eq A}} → Eq (Maybe A)
  Eq._≟_ Maybe-Eq = MaybeProps.≡-dec _≟_
  Eq._==_ Maybe-Eq = λ where
    nothing nothing → true
    nothing (just _) → false
    (just _) nothing → false
    (just x) (just y) → x == y

  LoginToken-Eq : Eq LoginToken
  Eq._≟_ LoginToken-Eq = token-eq
    where
      token-injective : {x y : ℕ} → token x ≡ token y → x ≡ y
      token-injective refl = refl

      token-eq : (x y : LoginToken) → Dec (x ≡ y)
      token-eq (token x) (token y) with Nat._≟_ x y
      ... | yes x≡y = yes (cong token x≡y)
      ... | no x≢y  = no λ p → x≢y (token-injective p)
  Eq._==_ LoginToken-Eq = λ where (token x) (token y) → x == y

  TweetId-Eq : Eq TweetId
  Eq._≟_ TweetId-Eq = tweet-eq
    where
      tweet-injective : {x y : ℕ} → tweet-id x ≡ tweet-id y → x ≡ y
      tweet-injective refl = refl

      tweet-eq : (x y : TweetId) → Dec (x ≡ y)
      tweet-eq (tweet-id x) (tweet-id y) with Nat._≟_ x y
      ... | yes x≡y = yes (cong tweet-id x≡y)
      ... | no x≢y  = no λ p → x≢y (tweet-injective p)
  Eq._==_ TweetId-Eq = λ where (tweet-id x) (tweet-id y) → x == y
