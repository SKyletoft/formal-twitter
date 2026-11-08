module Twitter
  (SessionId PostId : Set)
  where

open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.String

open import Data.Empty                            using (⊥; ⊥-elim)
open import Data.List                             using (List; take; filter)
open import Data.Product                          using (∃-syntax)
open import Function                              using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no)
open import Relation.Nullary.Negation.Core        using (¬_)

--------------------------------------------------------------------------------
--                               PROOF-HELPERS                                --
--------------------------------------------------------------------------------

private variable a b c : Set

length : List a → Nat
length []       = zero
length (_ ∷ xs) = suc (length xs)

infix 4 _∈_ _∉_
data _∈_ (x : a) : List a → Set where
  here  : ∀ {xs}            → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

_∉_ : (x : a) → List a → Set
x ∉ y = ¬ (x ∈ y)

contains : ((x y : a) → Dec (x ≡ y)) → (x : a) → (xs : List a) → Dec (x ∈ xs)
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
    (author : String) →
    (text : String) →
    (likes : Nat) →
    (replies : List PostId) →
    Result

--------------------------------------------------------------------------------
--                                 PREDICATES                                 --
--------------------------------------------------------------------------------

record ValidSession
    (world : World)
    (sid : SessionId)
    (acc : Account)
    (user : String) : Set₁
  where
  field
    session-unchanged : World.session-at world sid  ≡ active user
    account-unchanged : World.account-at world user ≡ just acc

record PostIsNew
    (world : World)
    (pid : PostId)
    (new-post : Post) : Set₁
  where
  field
    was-absent : World.post-at world pid ≡ nothing
    is-present : World.post-at world pid  ≡ just new-post

data CanReadPost
    (world : World)
    (sid : SessionId)
    (pid : PostId) : Set₁
  where
  post-is-private :
    ∀ {author txt likes replies acc user} →
    ValidSession world sid acc user →
    World.post-at world pid ≡ just (post author txt followers-only live likes replies) →
    World.follows world user author →
    CanReadPost world sid pid
  post-is-public :
    ∀ {author txt likes replies acc user} →
    ValidSession world sid acc user →
    World.post-at world pid ≡ just (post author txt everyone live likes replies) →
    CanReadPost world sid pid

--------------------------------------------------------------------------------
--                                  HELPERS                                   --
--------------------------------------------------------------------------------

new-post : String → String → Account → Post
new-post username txt user =
  post username txt (Account.default-visibility user) live zero []

--------------------------------------------------------------------------------
--                                TRANSITIONS                                 --
--------------------------------------------------------------------------------

data Step : World → Command → World → Result → Set₁ where

  successful-post :
    ∀ {before after sid txt username user pid acc} →
    ValidSession before sid acc username →
    PostIsNew before pid (new-post username txt user) →
    pid ∷ World.newest-first before ≡ World.newest-first after →
    -- Everything else unchanged
    ∀ {other-pids u1 u2 s} →
    pid ≢ other-pids →
    World.post-at before other-pids ≡ World.post-at after other-pids →
    World.account-at before u1      ≡ World.account-at after u1 →
    World.session-at before s       ≡ World.session-at after s →
    World.follows before u1 u2      ≡ World.follows after u1 u2 →
    Step before (publish sid txt) after (created-post pid)

  failed-access :
    ∀ {before sid username acc cmd} →
    ¬ ValidSession before sid acc username →
    Step before cmd before expired

  create-account :
    ∀ {before after username passwd} →
    World.account-at before username ≡ nothing →
    World.account-at after username  ≡ just (account passwd everyone) →
    -- Everything else unchanged
    ∀ {sid pid u1 u2} →
    username ≢ u1 →
    username ≢ u2 →
    World.account-at before u1  ≡ World.account-at after u1 →
    World.session-at before sid ≡ World.session-at after sid →
    World.post-at before pid    ≡ World.post-at after pid →
    World.follows before u1 u2  ≡ World.follows after u1 u2 →
    World.newest-first before   ≡ World.newest-first after →
    Step before (register username passwd) after success

  failed-create-account :
    ∀ { before username passwd } →
    World.account-at before username ≢ nothing →
    Step before (register username passwd) before signup-failed

  login :
    ∀ {before after username passwd sid user} →
    World.session-at before sid      ≡ unused →
    World.session-at after sid       ≡ active username →
    World.account-at before username ≡ just user →
    Account.password user            ≡ passwd →
    -- Everything else unchanged
    ∀ {other-sid pid u1 u2} →
    sid ≢ other-sid →
    World.session-at before other-sid ≡ World.session-at after other-sid →
    World.account-at before u1        ≡ World.account-at after u1 →
    World.post-at before pid          ≡ World.post-at after pid →
    World.follows before u1 u2        ≡ World.follows after u1 u2 →
    World.newest-first before         ≡ World.newest-first after →
    ValidSession after sid user username →
    Step before (authenticate username passwd) after (issued-session sid)

  failed-login-1 :
    ∀ {before username passwd} →
    World.account-at before username ≡ nothing →
    Step before (authenticate username passwd) before login-failed

  failed-login-2 :
    ∀ {before username passwd user} →
    World.account-at before username ≡ just user →
    Account.password user            ≢ passwd →
    Step before (authenticate username passwd) before login-failed

  cant-read-post :
    ∀ {before pid sid author txt likes replies acc user} →
    ValidSession before sid acc user →
    World.post-at before pid ≡ just (post author txt followers-only live likes replies) →
    ¬ (World.follows before user author) →
    Step before (read-post (just sid) pid) before denied

  read-post-logged-in :
    ∀ {before pid sid author txt likes replies} →
    CanReadPost before sid pid →
    Step before (read-post (just sid) pid) before (returned-post author txt likes replies)

  read-post-anonymously :
    ∀ {before pid author txt likes replies} →
    World.post-at before pid ≡ just (post author txt everyone live likes replies) →
    Step before (read-post nothing pid) before (returned-post author txt likes replies)

  -- get-private-timeline :
  --   ∀ {before n sid acc user} →
  --     let response = returned-timeline (take n ∘ filter (λ where
  --                                                           c → {!!}
  --                                                         ) ∘ World.newest-first $ before)
  --     in ValidSession before sid acc user →
  --        Step before (read-timeline (just sid) n) before response

  get-public-timeline :
    ∀ {before n} →
    Step before (read-timeline nothing n) before (returned-timeline (take n ∘ World.newest-first $ before))
