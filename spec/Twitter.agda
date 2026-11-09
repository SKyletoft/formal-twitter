module Twitter
  (SessionId PostId : Set)
  where

open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

open import Data.Empty                            using (⊥; ⊥-elim)
open import Data.List                             using (List; take; filter)
open import Data.Product                          using (∃-syntax)
open import Data.String                           using (String) renaming (_≟_ to _≟ₛ_)
open import Function                              using (_∘_; _$_; case_of_; case_returning_of_)
open import Relation.Binary.Definitions           using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; trans; sym)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no)
open import Relation.Nullary.Negation.Core        using (¬_)

--------------------------------------------------------------------------------
--                               PROOF-HELPERS                                --
--------------------------------------------------------------------------------

private variable a b c : Set

infix 4 _∈_ _∉_
data _∈_ (x : a) : List a → Set where
  here  : ∀ {xs}            → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

_∉_ : (x : a) → List a → Set
x ∉ y = ¬ (x ∈ y)

infixr 2 _×_
_×_ : Set → Set → Set
a × b = Σ a (λ _ → b)

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
    follows      : String → String     → Bool
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
    (user : String) : Set
  where
  constructor valid-session
  field
    session-unchanged : World.session-at world sid  ≡ active user
    account-unchanged : World.account-at world user ≡ just acc

record PostIsNew
    (before after : World)
    (pid : PostId)
    (new-post : Post) : Set
  where
  constructor post-is-new
  field
    was-absent : World.post-at before pid ≡ nothing
    is-present : World.post-at after pid  ≡ just new-post

data CanReadPost
    (world : World)
    (sid : SessionId)
    (pid : PostId) : Set₁
  where
  post-is-private :
    ∀ {author txt likes replies acc user} →
    ValidSession world sid acc user →
    World.post-at world pid ≡ just (post author txt followers-only live likes replies) →
    World.follows world user author ≡ true →
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

_≟ᵥ_ : DecidableEquality Visibility
everyone       ≟ᵥ everyone       = yes refl
everyone       ≟ᵥ followers-only = no λ ()
followers-only ≟ᵥ everyone       = no λ ()
followers-only ≟ᵥ followers-only = yes refl

_≟ₐ_ : DecidableEquality Account
account password vis ≟ₐ account password₁ vis₁ with password ≟ₛ password₁ with vis ≟ᵥ vis₁
... | yes p | yes v = yes (cong₂ account p v)
... | yes p | no  v = no (λ eq → v (cong Account.default-visibility eq))
... | no  p | yes v = no (λ eq → p (cong Account.password eq))
... | no  p | no  v = no (λ eq → p (cong Account.password eq))

_≟active_ : (s : SessionStatus) (u : String) → Dec (s ≡ active u)
unused  ≟active _ = no λ ()
revoked ≟active _ = no λ ()
active v ≟active u with v ≟ₛ u
... | yes refl = yes refl
... | no  v≢u  = no $ v≢u ∘ λ {refl → refl}

_≟just_ : (m : Maybe Account) (acc : Account) → Dec (m ≡ just acc)
nothing  ≟just _ = no λ ()
just a   ≟just acc with a ≟ₐ acc
... | yes refl = yes refl
... | no a≢acc = no $ a≢acc ∘ λ {refl → refl}

is-valid-session :
  (w : World) →
  (sid : SessionId) →
  (acc : Account) →
  (user : String) →
  Dec (ValidSession w sid acc user)
is-valid-session w sid acc user
  with World.session-at w sid ≟active user
     | World.account-at w user ≟just acc
... | yes s | yes a = yes $ valid-session s a
... | yes _ | no a  = no  $ a ∘ ValidSession.account-unchanged
... | no s  | _     = no  $ s ∘ ValidSession.session-unchanged

can-have-valid-session :
  (w : World) (sid : SessionId) (pid : PostId) →
  Dec (∃[ acc ] ∃[ user ] ValidSession w sid acc user)
can-have-valid-session w sid pid
  with World.session-at w sid in p
... | unused  = no $ (λ ()) ∘ trans (sym p) ∘ ValidSession.session-unchanged ∘ snd ∘ snd
... | revoked = no $ (λ ()) ∘ trans (sym p) ∘ ValidSession.session-unchanged ∘ snd ∘ snd
... | active user
  with World.account-at w user in q
... | just acc = yes (acc , user , valid-session p q)
... | nothing  = no λ _ →
      let r = snd ∘ World.only-valid-sessions w $ p
      in (λ ()) $ trans (sym r) q

can-read-post : (w : World) (sid : SessionId) (pid : PostId) → Dec (CanReadPost w sid pid)
can-read-post w sid pid = {!!}

--------------------------------------------------------------------------------
--                                TRANSITIONS                                 --
--------------------------------------------------------------------------------

data Step : World → Command → World → Result → Set₁ where

  successful-post :
    ∀ {before after sid txt username user pid acc} →
    ValidSession before sid acc username →
    PostIsNew before after pid (new-post username txt user) →
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
    World.follows before user author ≡ false →
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
    Step before (read-timeline nothing n) before (returned-timeline ∘ take n ∘ World.newest-first $ before)
