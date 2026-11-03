module Twitter
  (SessionId PostId : Set)
  where

open import Interface

open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.String

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Negation.Core        using (¬_)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no)
open import Data.Empty                            using (⊥; ⊥-elim)

--------------------------------------------------------------------------------
--                                  HELPERS                                   --
--------------------------------------------------------------------------------

variable a b c : Set

length : List a → Nat
length []       = zero
length (_ ∷ xs) = suc (length xs)

infix 4 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

contains : {a : Set} → ((x y : a) → Dec (x ≡ y)) → (x : a) → (xs : List a) → Dec (x ∈ xs)
contains _≟_ x [] = no λ ()
contains _≟_ x (y ∷ ys) with x ≟ y
... | yes refl = yes here
... | no x≢y with contains _≟_ x ys
...   | yes p = yes (there p)
...   | no x∉ys = no λ { here → x≢y refl ; (there p) → x∉ys p }

--------------------------------------------------------------------------------
--                                STATE TYPES                                 --
--------------------------------------------------------------------------------

data Visibility : Set where
  everyone       : Visibility
  followers-only : Visibility

data PostStatus : Set where
  live    : PostStatus
  deleted : PostStatus

record Account : Set where
  constructor account
  field
    password           : String
    default-visibility : Visibility

record Post : Set where
  constructor post
  field
    author     : String
    text       : String
    visibility : Visibility
    status     : PostStatus
    likes      : Nat
    replies    : List PostId

data SessionStatus : Set where
  unused  : SessionStatus
  active  : (username : String) → SessionStatus
  revoked : SessionStatus

record World : Set₁ where
  constructor world
  field
    account-at   : (username : String) → Maybe Account
    session-at   : SessionId           → SessionStatus
    post-at      : PostId              → Maybe Post
    follows      : String              → String → Set
    newest-first : List PostId

    only-valid-sessions :
      ∀ {sid username acc} →
      session-at sid ≡ active username →
      account-at username ≡ just acc
    only-valid-posts :
      ∀ {pid post} →
      pid ∈ newest-first →
      post-at pid ≡ just post

data Command : Set where
  publish       : SessionId       → String → Command
  read-post     : Maybe SessionId → PostId → Command
  read-timeline : Maybe SessionId → Nat    → Command
  authenticate  : String          → String → Command
  register      : String          → String → Command

data Result : Set where
  success           : Result
  denied            : Result
  expired           : Result
  login-failed      : Result
  signup-failed     : Result
  returned-timeline : List PostId → Result
  issued-session    : SessionId → Result
  created-post      : PostId → Result
  returned-post :
    String →
    String →
    Nat →
    List PostId →
    Result

--------------------------------------------------------------------------------
--                                TRANSITIONS                                 --
--------------------------------------------------------------------------------

data Step : World → Command → World → Result → Set₁ where
  successful-post :
    ∀ {sid txt before after username user pid} →
    World.session-at before sid ≡ active username →
    World.account-at before username ≡ just user →
    World.post-at before pid ≡ nothing →
    World.post-at after pid ≡ just (post username txt (Account.default-visibility user) live zero []) →
    Step before (publish sid txt) after success
