module Monad where

open import Data.Maybe hiding (_>>=_; map)
open import Data.List hiding (map; replicate)
open import Data.Vec hiding (map; _++_)
open import Data.Nat

Nat = ℕ

record Monad (F : Set → Set) : Set₁ where
  field
    return : {a : Set}   → a         → F a
    _>>=_  : {a b : Set} → F a       → (a → F b) → F b
    _<$>_  : {a b : Set} → (a → b)   → F a       → F b
    _<*>_  : {a b : Set} → F (a → b) → F a       → F b
open Monad {{...}}

_>>_ : {F : Set → Set} {{ r : Monad F }} {a b : Set} → F a → F b → F b
x >> y = do
  _ ← x
  y ← y
  return y

_=<<_ : {F : Set → Set} {{ r : Monad F }} {a b : Set} → (a → F b) → F a → F b
f =<< x = x >>= f

map : {F : Set → Set} {{ r : Monad F }} {a b : Set} → (a → b) → F a → F b
map = _<$>_

instance
  Maybe-Monad : Monad Maybe
  Monad.return Maybe-Monad = just
  Monad._>>=_ Maybe-Monad = λ where
    (just x) f → f x
    nothing _ → nothing
  Monad._<$>_ Maybe-Monad = λ where
    f (just x) → just (f x)
    _ nothing → nothing
  Monad._<*>_ Maybe-Monad = λ where
    (just f) (just x) → just (f x)
    (just _) nothing → nothing
    nothing _ → nothing

  List-Monad : Monad (λ a → List a)
  Monad.return List-Monad = λ x → x ∷ []
  Monad._>>=_ List-Monad = λ where
    [] f → []
    (x ∷ xs) f → f x ++ Monad._>>=_ List-Monad xs f
  Monad._<$>_ List-Monad = lmap
    where
      lmap : {a b : Set} → (a → b) → List a → List b
      lmap f [] = []
      lmap f (x ∷ xs) = f x ∷ lmap f xs
  Monad._<*>_ List-Monad = λ where
    [] _ → []
    (f ∷ fs) xs → Monad._<$>_ List-Monad f xs ++ Monad._<*>_ List-Monad fs xs


  Vec-Monad : {n : Nat} → Monad (λ a → Vec a n)
  Monad.return (Vec-Monad {n}) = replicate n
  Monad._>>=_ (Vec-Monad {n}) = bind-vec {n}
    where
      v-head : {n : Nat} {a : Set} → Vec a (suc n) → a
      v-head (x ∷ _) = x

      v-tail : {n : Nat} {a : Set} → Vec a (suc n) → Vec a n
      v-tail (_ ∷ xs) = xs

      bind-vec : {n : Nat} {a b : Set} → Vec a n → (a → Vec b n) → Vec b n
      bind-vec [] f = []
      bind-vec (x ∷ xs) f = v-head (f x) ∷ bind-vec xs (λ y → v-tail (f y))
  Monad._<$>_ (Vec-Monad {n}) = v-map
    where
      v-map : {n : Nat} → {a b : Set} → (a → b) → Vec a n → Vec b n
      v-map f [] = []
      v-map f (x ∷ xs) = f x ∷ v-map f xs
  Monad._<*>_ (Vec-Monad {n}) = v-ap
    where
      v-ap : {n : Nat} → {a b : Set} → Vec (a → b) n → Vec a n → Vec b n
      v-ap [] [] = []
      v-ap (f ∷ fs) (x ∷ xs) = f x ∷ v-ap fs xs
