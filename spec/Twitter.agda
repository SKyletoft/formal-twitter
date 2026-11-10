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
open import Data.String                           using (String)
                                                  renaming (_≟_ to _≟ₛ_)
open import Function                              using (_∘_; _$_)
open import Relation.Binary.Definitions           using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong;
                                                         cong₂; trans; sym)
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
    parent     : Maybe PostId

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
    only-valid-replies :
      ∀ {parent child pauthor ptxt pvis pstatus plikes preplies pparent} →
      ∀ {cauthor ctxt cvis cstatus clikes creplies} →
      child ∈ preplies →
      post-at parent ≡ just (post pauthor
                                  ptxt
                                  pvis
                                  pstatus
                                  plikes
                                  preplies
                                  pparent) →
      post-at child  ≡ just (post cauthor
                                  ctxt
                                  cvis
                                  cstatus
                                  clikes
                                  creplies
                                  (just parent)) →
      Set

data Command : Set where
  publish       : SessionId       → String → Maybe PostId → Command
  delete        : SessionId       → PostId → Command
  read-post     : Maybe SessionId → PostId → Command
  read-timeline : Maybe SessionId → Nat    → Command
  authenticate  : String          → String → Command
  register      : String          → String → Command
  follow        : SessionId       → String → Command
  unfollow      : SessionId       → String → Command
  like          : SessionId       → PostId → Command
  unlike        : SessionId       → PostId → Command

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
    ∀ {author txt likes replies acc user parent} →
    ValidSession world sid acc user →
    World.post-at world pid ≡ just (post author
                                         txt
                                         followers-only
                                         live
                                         likes
                                         replies
                                         parent) →
    World.follows world user author ≡ true →
    CanReadPost world sid pid
  post-is-public :
    ∀ {author txt likes replies acc user parent} →
    ValidSession world sid acc user →
    World.post-at world pid ≡ just (post author
                                         txt
                                         everyone
                                         live
                                         likes
                                         replies
                                         parent) →
    CanReadPost world sid pid

--------------------------------------------------------------------------------
--                                  HELPERS                                   --
--------------------------------------------------------------------------------

extract-sid : Command → Maybe SessionId
extract-sid (publish sid _ _)      = just sid
extract-sid (delete sid _)         = just sid
extract-sid (read-post msid _)     = msid
extract-sid (read-timeline msid _) = msid
extract-sid (authenticate _ _)     = nothing
extract-sid (register _ _)         = nothing
extract-sid (follow sid _)         = just sid
extract-sid (unfollow sid _)       = just sid
extract-sid (like sid _)           = just sid
extract-sid (unlike sid _)         = just sid

new-post : String → String → Account → Post
new-post username txt user =
  post username txt (Account.default-visibility user) live zero [] nothing

new-reply : String → String → Account → PostId → Post → Post
new-reply username txt user parent-id (post _ _ everyone _ _ _ _) =
  post username txt (Account.default-visibility user) live zero [] (just parent-id)
new-reply username txt user parent-id (post _ _ followers-only _ _ _ _) =
  post username txt followers-only live zero [] (just parent-id)

_≟ᵥ_ : DecidableEquality Visibility
everyone       ≟ᵥ everyone       = yes refl
followers-only ≟ᵥ followers-only = yes refl
everyone       ≟ᵥ followers-only = no λ ()
followers-only ≟ᵥ everyone       = no λ ()

_≟ₐ_ : DecidableEquality Account
account password vis ≟ₐ account password₁ vis₁
  with password ≟ₛ password₁
     | vis      ≟ᵥ vis₁
... | yes p | yes v = yes $ cong₂ account p v
... | yes p | no  v = no $ v ∘ cong Account.default-visibility
... | no  p | yes v = no $ p ∘ cong Account.password
... | no  p | no  v = no $ p ∘ cong Account.password

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

just-injective   : ∀ {x y : a} → just x ≡ just y → x ≡ y ; just-injective refl = refl
active-injective : ∀ {u v} → active u ≡ active v → u ≡ v ; active-injective refl = refl

is-valid-session :
  (w : World) →
  (sid : SessionId) →
  (acc : Account) →
  (user : String) →
  Dec (ValidSession w sid acc user)
is-valid-session w sid acc user
  with World.session-at w sid  ≟active user
     | World.account-at w user ≟just   acc
... | yes s | yes a = yes $ valid-session s a
... | yes _ | no a  = no  $ a ∘ ValidSession.account-unchanged
... | no s  | _     = no  $ s ∘ ValidSession.session-unchanged

can-have-valid-session :
  (w : World) (sid : SessionId) (pid : PostId) →
  Dec (∃[ acc ] ∃[ user ] ValidSession w sid acc user)
can-have-valid-session w sid pid
  with World.session-at w sid in p
... | unused  = no $ (λ ())
                   ∘ trans (sym p)
                   ∘ ValidSession.session-unchanged
                   ∘ snd
                   ∘ snd
... | revoked = no $ (λ ())
                   ∘ trans (sym p)
                   ∘ ValidSession.session-unchanged
                   ∘ snd
                   ∘ snd
... | active user
  with World.account-at w user in q
... | just acc = yes (acc , user , valid-session p q)
... | nothing  = no $ λ _ →
      let r = snd ∘ World.only-valid-sessions w $ p
      in (λ ()) $ trans (sym r) q

can-read-post :
  (w : World) →
  (sid : SessionId) →
  (pid : PostId) →
  Dec (CanReadPost w sid pid)
can-read-post w sid pid with can-have-valid-session w sid pid
... | no ¬vs = no λ
        { (post-is-private vs _ _) → ¬vs (_ , _ , vs)
        ; (post-is-public vs _)    → ¬vs (_ , _ , vs)
        }
... | yes (_ , user , vs)
  with World.post-at w pid in p
... | nothing = no λ
        { (post-is-private _ r _) → (λ ()) ∘ trans (sym r) $ p
        ; (post-is-public _ r)    → (λ ()) ∘ trans (sym r) $ p
        }
... | just (post _ _ _ deleted _ _ _) = no λ
        { (post-is-private _ r _) → (λ ())
                                  ∘ cong Post.status
                                  ∘ just-injective
                                  ∘ trans (sym r)
                                  $ p
        ; (post-is-public _ r)    → (λ ())
                                  ∘ cong Post.status
                                  ∘ just-injective
                                  ∘ trans (sym r)
                                  $ p
        }
... | just (post author text everyone live likes replies parent) =
        yes $ post-is-public vs p
... | just (post author text followers-only live likes replies parent)
  with World.follows w user author in q
... | true  = yes $ post-is-private vs p q
... | false = no λ
        { (post-is-private {author} vs' r f) →
            let e1 = cong (λ u → World.follows w u author)
                   ∘ active-injective
                   ∘ trans (sym (ValidSession.session-unchanged vs'))
                   ∘ ValidSession.session-unchanged
                   $ vs
                e2 = cong (World.follows w user ∘ Post.author)
                   ∘ just-injective
                   ∘ trans (sym r)
                   $ p
            in (λ ()) ∘ trans (sym q) ∘ trans (sym e2) ∘ trans (sym e1) $ f
        ; (post-is-public _ r) → (λ ())
                               ∘ cong Post.visibility
                               ∘ just-injective
                               ∘ trans (sym r)
                               $ p
        }

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
    Step before (publish sid txt nothing) after (created-post pid)

  successful-reply :
    ∀ {before after sid txt username user pid acc ppid ppost} →
    ValidSession before sid acc username →
    PostIsNew before after pid (new-reply username txt user ppid ppost) →
    pid ∷ World.newest-first before ≡ World.newest-first after →
    -- Parent tweet has a new reply
    ∀ {ppid ptxt pauthor pvisibility plikes preplies pparent} →
    CanReadPost before sid ppid →
    ppost ≡ (post pauthor ptxt pvisibility live plikes preplies pparent) →
    World.post-at before ppid ≡ just ppost →
    World.post-at after  ppid ≡ just (post pauthor
                                           ptxt
                                           pvisibility
                                           live
                                           plikes
                                           (pid ∷ preplies)
                                           pparent) →
    -- Everything else unchanged
    ∀ {other-pids u1 u2 s} →
    pid ≢ other-pids →
    pid ≢ ppid →
    ppid ≢ other-pids →
    World.post-at before other-pids ≡ World.post-at after other-pids →
    World.account-at before u1      ≡ World.account-at after u1 →
    World.session-at before s       ≡ World.session-at after s →
    World.follows before u1 u2      ≡ World.follows after u1 u2 →
    Step before (publish sid txt (just ppid)) after (created-post pid)

  failed-access :
    ∀ {before sid username acc cmd} →
    extract-sid cmd ≡ just sid →
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
    ∀ {before pid sid author txt likes replies acc user parent} →
    ValidSession before sid acc user →
    World.post-at before pid ≡ just (post author txt followers-only live likes replies parent) →
    World.follows before user author ≡ false →
    Step before (read-post (just sid) pid) before denied

  read-post-logged-in :
    ∀ {before pid sid author txt likes replies} →
    CanReadPost before sid pid →
    Step before (read-post (just sid) pid) before (returned-post author txt likes replies)

  read-post-anonymously :
    ∀ {before pid author txt likes replies parent} →
    World.post-at before pid ≡ just (post author txt everyone live likes replies parent) →
    Step before (read-post nothing pid) before (returned-post author txt likes replies)

  get-private-timeline :
    ∀ {before n sid acc user} →
    ValidSession before sid acc user →
    Step before (read-timeline (just sid) n) before
      ∘ returned-timeline
      ∘ take n
      ∘ filter (can-read-post before sid)
      ∘ World.newest-first
      $ before

  get-public-timeline :
    ∀ {before n} →
    Step before (read-timeline nothing n) before (returned-timeline ∘ take n ∘ World.newest-first $ before)
