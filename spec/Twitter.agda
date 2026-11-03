module Twitter
  (SessionId PostId : Set)
  where

open import Interface

open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.String

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Negation.Core        using (¬_)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no)
open import Data.Empty                            using (⊥; ⊥-elim)
open import Data.Product                          using (∃-syntax)

--------------------------------------------------------------------------------
--                                  HELPERS                                   --
--------------------------------------------------------------------------------

variable a b c : Set

length : List a → Nat
length []       = zero
length (_ ∷ xs) = suc (length xs)

infix 4 _∈_ _∉_
data _∈_ (x : a) : List a → Set where
  here  : ∀ {xs}            → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

_∉_ : (x : a) → List a → Set
x ∉ y = ¬ (x ∈ y)

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
      ∀ {sid username} →
      session-at sid ≡ active username →
      ∃[ acc ] account-at username ≡ just acc
    only-valid-posts :
      ∀ {pid} →
      pid ∈ newest-first →
      ∃[ post ] post-at pid ≡ just post

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
--                                 PREDICATES                                 --
--------------------------------------------------------------------------------

ValidSession : World → World → SessionId → String → Set₁
ValidSession before after sid username =
  World.session-at before sid      ≡ World.session-at after sid →
  World.account-at before username ≡ World.account-at after username →
  Set

PostIsNew : World → World → PostId → Post → Set₁
PostIsNew before after pid new-post =
  World.post-at before pid ≡ nothing →
  World.post-at after pid  ≡ just new-post →
  Set

new-post : String → String → Account → Post
new-post username txt user =
  (post username txt (Account.default-visibility user) live zero [])

--------------------------------------------------------------------------------
--                                TRANSITIONS                                 --
--------------------------------------------------------------------------------

data Step : World → Command → World → Result → Set₁ where

  successful-post :
    ∀ {sid txt before after username user pid acc other-pids u1 u2 s} →
    ValidSession before after sid username →
    PostIsNew before after pid (new-post username txt user) →
    -- PostId added
    pid ∷ World.newest-first before ≡ World.newest-first after →
    -- Everything else unchanged
    pid ≢ other-pids →
    World.post-at before other-pids ≡ World.post-at after other-pids →
    World.account-at before acc     ≡ World.account-at after acc →
    World.session-at before s       ≡ World.session-at after s →
    World.follows before u1 u2      ≡ World.follows after u1 u2 →
    Step before (publish sid txt) after success

  failed-access :
    ∀ {before after sid username cmd} →
    ¬ ValidSession before after sid username →
    Step before cmd after expired
