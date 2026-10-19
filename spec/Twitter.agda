module Twitter where

open import Agda.Builtin.String
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Data.Vec
open import Data.Fin
open import Data.Nat
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Relation.Binary.Bundles using (StrictTotalOrder)
import Relation.Binary.Construct.On as On
open import Interface

_×_ : Set → Set → Set
a × b = Σ a (λ _ → b)

infixr 2 _×_

Nat : Set
Nat = ℕ

data UserId (n : Nat): Set where
  uid : Fin n → UserId n

LoginToken< : StrictTotalOrder _ _ _
LoginToken< = On.strictTotalOrder <-strictTotalOrder tokenIdx
  where
    tokenIdx : LoginToken → Nat
    tokenIdx (token n) = n

import Data.Tree.AVL.Map LoginToken< as TokenMap

LoginTokenMap : Set → Set
LoginTokenMap V = TokenMap.Map V

data Privacy : Set where
  everyone       : Privacy
  followers-only : Privacy
  approved-only  : Privacy
  removed        : Privacy

record State (user-count : Nat) (tweet-count : Nat) : Set where
  constructor state
  field
    users               : Vec (String × Privacy × List (Fin user-count)) user-count
    tweets              : Vec (UserId user-count × String × Privacy) tweet-count
    running-tweet-count : Nat
    active-logins       : LoginTokenMap (UserId user-count)

record ValidState (n : Nat) (m : Nat) : Set where
  constructor VS
  field
    s : State n m
    -- Followed by proofs of various aspects
    -- * Tweets don't disappear
    -- * All authors exist
    -- * All likers exist
    -- * All keys in tweets are less than tweet-count

get-id : {n m : Nat} → State n m → LoginToken → Maybe (UserId n)
get-id (state users tweets running-tweet-count active-logins) t = TokenMap.lookup active-logins t

event-loop : {n m : Nat} → State n m → Action → Σ (Nat × Nat) (λ (n' , m') → State n' m' × Response)
event-loop {n} {m} s@(state users tweets running-tweet-count active-logins) (tweet login-token text) with get-id s login-token
... | just (uid user-id) =
  let _ , default-privacy , _ = lookup users user-id
      tweet = (uid user-id) , text , default-privacy
      tweets' = tweet ∷ tweets
      state' = state users tweets' (suc running-tweet-count) active-logins
  in (n , suc m) , state' , ok
... | nothing = (n , m) , s , outdated-login-token
event-loop s (delete-tweet x x₁) = (_ , _) , s , ok
event-loop s (like x x₁) = (_ , _) , s , ok
event-loop s (unlike x x₁) = (_ , _) , s , ok
event-loop s (read x x₁) = (_ , _) , s , ok
event-loop s (timeline x) = (_ , _) , s , ok
event-loop s (search x x₁) = (_ , _) , s , ok
event-loop s (login username passwd) = (_ , _) , s , ok
event-loop s (logout login-token) = (_ , _) , s , ok
