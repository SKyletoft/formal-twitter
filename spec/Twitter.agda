module Twitter where

open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.String using (String)
open import Data.Vec as Vec hiding (map)
open import Data.Vec using (Vec; []; _∷_)
open import Equality
open import Function using (case_of_; _$_; _∘_)
open import Helpers
open import Interface
open import Monad as Monad_
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

import Relation.Binary.Construct.On
import Data.String.Properties as StringProps
import Data.Tree.AVL.Map (Relation.Binary.Construct.On.strictTotalOrder <-strictTotalOrder (LoginToken.t)) as TokenMap
import Data.Tree.AVL.Map StringProps.<-strictTotalOrder-≈ as StringMapModule

open Monad {{...}}
open Eq {{...}}

record UserId (n : Nat): Set where
  constructor uid
  field
    i : Fin n

instance
  UserId-Eq : {n : Nat} → Eq (UserId n)
  Eq._≟_ UserId-Eq = userId-eq
    where
    uid-injective : {n : Nat} {i j : Fin n} → uid i ≡ uid j → i ≡ j
    uid-injective refl = refl

    userId-eq : {n : Nat} → (x y : UserId n) → Dec (x ≡ y)
    userId-eq (uid i) (uid j) with i ≟ j
    ... | yes i≡j = yes (cong uid i≡j)
    ... | no i≢j  = no λ p → i≢j (uid-injective p)
  Eq._==_ UserId-Eq = λ where (uid i) (uid j) → i == j


LoginTokenMap : Set → Set
LoginTokenMap V = TokenMap.Map V

StringMap : Set → Set
StringMap V = StringMapModule.Map V

data Privacy : Set where
  everyone       : Privacy
  followers-only : Privacy
  removed        : Privacy

instance
  Privacy-Eq : Eq Privacy
  Eq._≟_ Privacy-Eq = λ where
    everyone       everyone       → yes refl
    everyone       followers-only → no λ()
    everyone       removed        → no λ()
    followers-only everyone       → no λ()
    followers-only followers-only → yes refl
    followers-only removed        → no λ()
    removed        everyone       → no λ()
    removed        followers-only → no λ()
    removed        removed        → yes refl
  Eq._==_ Privacy-Eq = λ where
    everyone       everyone       → true
    followers-only followers-only → true
    removed        removed        → true
    _              _              → false

record User (user-count : Nat) : Set where
  constructor user
  field
    name            : String
    default-privacy : Privacy
    follows         : List (UserId user-count)
    followers       : List (UserId user-count)

record Tweet (user-count : Nat) (tweet-count : Nat) : Set where
  constructor tweet
  field
    id         : Fin tweet-count
    poster     : UserId user-count
    text       : String
    visibility : Privacy
    replies    : List TweetId
    liked-by   : List (UserId user-count)

weaken-count-tweet : {n m : Nat} → Tweet n m → Tweet n (suc m)
weaken-count-tweet (tweet id poster text visibility replies liked-by) =
  tweet (weaken id) poster text visibility replies liked-by

record State (user-count : Nat) (tweet-count : Nat) : Set where
  constructor state
  field
    users               : Vec (User user-count) user-count
    tweets              : Vec (Tweet user-count tweet-count) tweet-count
    running-tweet-count : Nat
    active-logins       : LoginTokenMap (UserId user-count)
    credentials         : StringMap (String × UserId user-count)

record ValidState (n : Nat) (m : Nat) : Set where
  constructor VS
  field
    s : State n m
    -- Followed by proofs of various aspects
    -- * Tweets don't disappear
    -- * All authors exist
    -- * All likers exist
    -- * All followers exist
    -- * All keys in tweets are less than tweet-count
    -- * Follows and followers are consistent

get-id : {n m : Nat} → State n m → LoginToken → Maybe (UserId n)
get-id (state users tweets running-tweet-count active-logins _) t = TokenMap.lookup active-logins t

post-tweet-helper : {n m : Nat} → State n m → Tweet n (suc m) → State n (suc m)
post-tweet-helper (state users tweets running-tweet-count active-logins credentials) t
  = state users (map weaken-count-tweet tweets ::: t) (suc running-tweet-count) active-logins credentials

event-loop : {n m : Nat} → State n m → Action → Σ (Nat × Nat) (λ (n' , m') → State n' m' × Response)
event-loop {n} {m} s (post-tweet login-token text) with get-id s login-token
... | just (uid user-id) =
  let (user _  default-privacy  _ _) = Vec.lookup (State.users s) user-id
      tweet = tweet (to-fin m) (uid user-id) text default-privacy [] []
      state' = post-tweet-helper s tweet
  in (n , suc m) , state' , tweet-id (tweet-id m)
... | nothing = (n , m) , s , outdated-login-token
-- event-loop s (delete-tweet x x₁) = {!!}
-- event-loop s (like x x₁) = {!!}
-- event-loop s (unlike x x₁) = {!!}
event-loop {n} {m} s (get-tweet tk (tweet-id twt)) with bounds-check {m} twt
... | just (twt) =
  let (tweet _ (uid poster) txt privacy replies _) = Vec.lookup (State.tweets s) twt
      (user poster-name _ _ followers) = Vec.lookup (State.users s) poster
      positive-response = _ , s , tweet poster-name txt m replies
      negative-response = _ , s , permission-error
  in case privacy , get-id s =<< tk of
      \{ (followers-only , just u)  → if (any? (_≟ u)) followers
            then positive-response
            else negative-response
       ; (followers-only , nothing) → negative-response
       ; (everyone , _)             → positive-response
       ; (removed , _)              → negative-response
       }
... | nothing =
  _ , s , permission-error -- Having an explicit not found leaks the existance of private tweets
event-loop {n} {m} s (timeline tk len) =
  let filter-tweets : (Tweet n m → Bool) → Σ (Nat × Nat) (λ (n' , m') → State n' m' × Response)
      filter-tweets f =
        let tweets
              = Data.List.take len
              ∘ map (tweet-id ∘ to-nat ∘ Tweet.id)
              ∘ Data.List.filterᵇ f
              ∘ Data.Vec.toList
              ∘ State.tweets
              $ s
        in _ , s , timeline tweets
  in case map (get-id s) tk of
    \{ (just (just u)) → filter-tweets (\{ (tweet _ _ _ everyone _ _) → true
                                         ; (tweet _ _ _ removed _ _) → false
                                         ; (tweet _ (uid poster) _ followers-only _ _)
                                            → member? u
                                            ∘ User.followers
                                            ∘ Vec.lookup (State.users s)
                                            $ poster
                                         })
     ; nothing → filter-tweets ((_== everyone) ∘ Tweet.visibility)
     ; (just nothing) → _ , s , outdated-login-token
     }
event-loop s (login username passwd) with StringMapModule.lookup (State.credentials s) username
... | (just (correct-passwd , u)) = if passwd ≟ correct-passwd
        then _ , s , session-token {!!}
        else (_ , s , login-error)
... | nothing = _ , s , login-error
-- event-loop s (logout login-token) = {!!}
event-loop s (signup _ _) = {!!}
-- event-loop s (delete-account _) = {!!}
