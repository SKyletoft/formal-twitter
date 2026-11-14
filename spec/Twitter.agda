open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

open import Data.Empty                            using (⊥; ⊥-elim)
open import Data.List                             using (List; []; _∷_; length;
                                                         take; filter; filterᵇ)
open import Data.Product                          using (∃-syntax; proj₁; proj₂)
open import Data.String                           using (String)
                                                  renaming (_≟_ to _≟ₛ_)
open import Data.Unit                             using (⊤; tt)
open import Function                              using (_∘_; _$_)
open import Level                                 using (_⊔_)
open import Relation.Binary.Definitions           using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong;
                                                         cong₂; trans; sym)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no)
open import Relation.Nullary.Negation.Core        using (¬_)

open import Helpers

module Twitter
  (SessionId PostId : Set)
  (new-sid : CreateNew SessionId)
  (new-pid : CreateNew PostId)
  (_≟ₚ_ : DecidableEquality PostId)
  (_≟ₛᵢ_ : DecidableEquality SessionId)
  where

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
    likes      : List String
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
      ∀ {parent-pid parent-post child-pid} →
      child-pid ∈ Post.replies parent-post →
      post-at parent-pid ≡ just parent-post →
      ∃[ child-post ]
        post-at child-pid        ≡ just child-post
        ∧ Post.parent child-post ≡ just parent-pid
    no-duplicate-replies :
      ∀ {pid post} →
      post-at pid ≡ just post →
      uniq (Post.replies post)
    no-duplicate-likes :
      ∀ {pid post} →
      post-at pid ≡ just post →
      uniq (Post.likes post)
    no-duplicate-posts :
      uniq newest-first

data Command : Set where
  publish                : SessionId       → String → Maybe PostId → Command
  delete                 : SessionId       → PostId → Command
  read-post              : Maybe SessionId → PostId → Command
  read-personal-timeline : SessionId       → Nat    → Command
  read-global-timeline   : Maybe SessionId → Nat    → Command
  authenticate           : String          → String → Command
  revoke-token           : SessionId                → Command
  register               : String          → String → Command
  follow                 : SessionId       → String → Command
  unfollow               : SessionId       → String → Command
  like                   : SessionId       → PostId → Command
  unlike                 : SessionId       → PostId → Command
  time-passes            :                            Command
  -- collect-dead-posts     :                            Command

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
    ∀ {acc user post} →
    ValidSession world sid acc user →
    World.post-at world pid ≡ just post →
    Post.visibility post    ≡ followers-only →
    Post.status post        ≡ live →
    World.follows world user (Post.author post) ≡ true →
    CanReadPost world sid pid
  post-is-public :
    ∀ {acc user post} →
    ValidSession world sid acc user →
    World.post-at world pid ≡ just post →
    Post.visibility post    ≡ everyone →
    Post.status post        ≡ live →
    CanReadPost world sid pid

--------------------------------------------------------------------------------
--                                  HELPERS                                   --
--------------------------------------------------------------------------------

extract-sid : Command → Maybe SessionId
extract-sid (publish sid _ _)              = just sid
extract-sid (delete sid _)                 = just sid
extract-sid (read-post msid _)             = msid
extract-sid (read-personal-timeline sid _) = just sid
extract-sid (read-global-timeline msid _)  = msid
extract-sid (authenticate _ _)             = nothing
extract-sid (revoke-token sid)             = just sid
extract-sid (register _ _)                 = nothing
extract-sid (follow sid _)                 = just sid
extract-sid (unfollow sid _)               = just sid
extract-sid (like sid _)                   = just sid
extract-sid (unlike sid _)                 = just sid
extract-sid time-passes                    = nothing
-- extract-sid collect-dead-posts             = nothing

new-post : String → String → Account → Post
new-post username txt user =
  post username txt (Account.default-visibility user) live [] [] nothing

new-reply : String → String → Account → PostId → Post → Post
new-reply username txt user parent-id (post _ _ everyone _ _ _ _) =
  post username txt (Account.default-visibility user) live [] [] (just parent-id)
new-reply username txt user parent-id (post _ _ followers-only _ _ _ _) =
  post username txt followers-only live [] [] (just parent-id)

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
  (w : World) (sid : SessionId) →
  Dec (∃[ acc ] ∃[ user ] ValidSession w sid acc user)
can-have-valid-session w sid
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
      in (λ ()) ∘ trans (sym r) $ q

can-read-post :
  (w : World) →
  (sid : SessionId) →
  (pid : PostId) →
  Dec (CanReadPost w sid pid)
can-read-post w sid pid with can-have-valid-session w sid
... | no ¬vs = no λ
        { (post-is-private vs _ _ _ _) → ¬vs (_ , _ , vs)
        ; (post-is-public vs _ _ _)    → ¬vs (_ , _ , vs)
        }
... | yes (_ , user , vs)
  with World.post-at w pid in p
... | nothing = no λ
        { (post-is-private _ r _ _ _) → (λ ()) ∘ trans (sym r) $ p
        ; (post-is-public _ r _ _)    → (λ ()) ∘ trans (sym r) $ p
        }
... | just (post _ _ _ deleted _ _ _) = no λ
        { (post-is-private _ r _ s _) → (λ ())
                                        ∘ trans (sym s)
                                        ∘ cong Post.status
                                        ∘ just-injective
                                        ∘ trans (sym r)
                                        $ p
        ; (post-is-public _ r _ s) → (λ ())
                                     ∘ trans (sym s)
                                     ∘ cong Post.status
                                     ∘ just-injective
                                     ∘ trans (sym r)
                                     $ p
        }
... | just (post _ _ everyone live _ _ _) =
        yes $ post-is-public vs p refl refl
... | just (post author text followers-only live likes replies parent)
  with World.follows w user author in q
... | true  = yes $ post-is-private vs p refl refl q
... | false = no λ
        { (post-is-private {post = pst} vs' r _ _ f) →
            let e1 = cong (λ u → World.follows w u (Post.author pst))
                   ∘ active-injective
                   ∘ trans (sym (ValidSession.session-unchanged vs'))
                   ∘ ValidSession.session-unchanged
                   $ vs
                e2 = cong (World.follows w user ∘ Post.author)
                   ∘ just-injective
                   ∘ trans (sym r)
                   $ p
            in (λ ()) ∘ trans (sym q) ∘ trans (sym e2) ∘ trans (sym e1) $ f
        ; (post-is-public _ r v _) →
              (λ ())
              ∘ trans (sym v)
              ∘ cong Post.visibility
              ∘ just-injective
              ∘ trans (sym r)
              $ p
        }

is-post-public :
  (w : World) →
  (pid : PostId) →
  Dec (∃[ post ]
       World.post-at w pid    ≡ just post
       ∧ Post.visibility post ≡ everyone
       ∧ Post.status post     ≡ live)
is-post-public w pid with World.post-at w pid in p
... | just (post author text everyone live likes replies parent) =
        yes (post author text everyone live likes replies parent , refl , refl , refl)
... | just (post _ _ followers-only _ _ _ _) = no λ
        { (pst , eq , vis , _) → (λ ()) ∘ trans (cong Post.visibility ∘ just-injective $ eq) $ vis }
... | just (post _ _ _ deleted _ _ _) = no λ
        { (pst , eq , _ , sts) → (λ ()) ∘ trans (cong Post.status ∘ just-injective $ eq) $ sts }
... | nothing = no λ
        { (pst , eq , _ , _) → (λ ()) $ eq }

-- is-alive : {p : Post} → (w : World) → (pid : PostId) → {World.post-at w pid ≡ just p} → Dec (Post.status p ≡ live)
-- is-alive = {!!}

return-post : Post → Result
return-post (post author txt _ _ likes replies _) =
  returned-post author txt (length likes) replies

follows-post-author : World → String → PostId → Bool
follows-post-author w user pid with World.post-at w pid
... | just p  = World.follows w user ∘ Post.author $ p
... | nothing = false

add-follower : (String → String → Bool) → String → String → String → String → Bool
add-follower followers follower followee x y with follower ≟ₛ x | followee ≟ₛ y
... | yes _ | yes _ = true
... | _     | _     = followers x y

remove-follower : (String → String → Bool) → String → String → String → String → Bool
remove-follower followers follower followee x y with follower ≟ₛ x | followee ≟ₛ y
... | yes _ | yes _ = false
... | _     | _     = followers x y

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
    ∀ {ppid ptxt pauthor pvisibility plikes preplies pparent ppost'} →
    CanReadPost before sid ppid →
    ppost  ≡ post pauthor ptxt pvisibility live plikes preplies         pparent →
    ppost' ≡ post pauthor ptxt pvisibility live plikes (pid ∷ preplies) pparent →
    World.post-at before ppid ≡ just ppost →
    World.post-at after  ppid ≡ just ppost' →
    -- Everything else unchanged
    ∀ {other-pids u1 u2 s} →
    pid  ≢ other-pids →
    pid  ≢ ppid →
    ppid ≢ other-pids →
    World.post-at before other-pids ≡ World.post-at after other-pids →
    World.account-at before u1      ≡ World.account-at after u1 →
    World.session-at before s       ≡ World.session-at after s →
    World.follows before u1 u2      ≡ World.follows after u1 u2 →
    Step before (publish sid txt (just ppid)) after (created-post pid)

  delete-post :
    ∀ {before after pid sid acc user post post'} →
    ValidSession before sid acc user →
    World.post-at before pid ≡ just post →
    World.post-at after pid  ≡ just post' →
    Post.author post         ≡ user →
    -- Rest of post unchanged
    Post.author post         ≡ Post.author post' →
    Post.text post           ≡ Post.text post' →
    Post.likes post          ≡ Post.likes post' →
    Post.replies post        ≡ Post.replies post' →
    Post.status post'        ≡ deleted →
    -- Everything else unchanged
    ∀ {other-pids u1 u2 s} →
    pid ≢ other-pids →
    World.post-at before other-pids ≡ World.post-at after other-pids →
    World.account-at before u1      ≡ World.account-at after u1 →
    World.session-at before s       ≡ World.session-at after s →
    World.follows before u1 u2      ≡ World.follows after u1 u2 →
    Step before (delete sid pid) after success

  failed-delete-non-existant-post :
    ∀ {before pid sid acc user} →
    ValidSession before sid acc user →
    World.post-at before pid ≡ nothing →
    Step before (delete sid pid) before denied

  failed-delete-not-author :
    ∀ {before pid sid acc user post} →
    ValidSession before sid acc user →
    World.post-at before pid ≡ just post →
    Post.author post         ≢ user →
    Step before (delete sid pid) before denied

  failed-access :
    ∀ {before cmd} →
    (∀ {sid} → extract-sid cmd ≡ just sid →
      ¬ (∃[ acc ] ∃[ username ] ValidSession before sid acc username)) →
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

  cant-read-post-public :
    ∀ {before pid sid acc user} →
    ValidSession before sid acc user →
    World.post-at before pid ≡ nothing →
    Step before (read-post (just sid) pid) before denied

  cant-read-post-private :
    ∀ {before pid sid author acc user post} →
    ValidSession before sid acc user →
    World.post-at before pid         ≡ just post →
    Post.visibility post             ≡ followers-only →
    Post.author post                 ≡ author →
    World.follows before user author ≡ false →
    Step before (read-post (just sid) pid) before denied

  cant-read-post-private-deleted :
    ∀ {before pid sid acc user post} →
    ValidSession before sid acc user →
    World.post-at before pid ≡ just post →
    Post.status post         ≡ deleted →
    Step before (read-post (just sid) pid) before denied

  read-post-logged-in :
    ∀ {before pid sid post author txt likes replies} →
    CanReadPost before sid pid →
    World.post-at before pid ≡ just post →
    Post.author post         ≡ author →
    Post.text post           ≡ txt →
    length (Post.likes post) ≡ likes →
    Post.replies post        ≡ replies →
    Step before (read-post (just sid) pid) before (returned-post author txt likes replies)

  read-post-anonymously :
    ∀ {before pid p} →
    World.post-at before pid ≡ just p →
    Post.visibility p        ≡ everyone →
    Post.status p            ≡ live →
    Step before (read-post nothing pid) before (return-post p)

  get-personal-timeline :
    ∀ {before n sid acc user} →
    ValidSession before sid acc user →
    Step before (read-personal-timeline sid n) before
      ∘ returned-timeline
      ∘ take n
      ∘ filterᵇ (follows-post-author before user)
      ∘ filter (can-read-post before sid)
      ∘ World.newest-first
      $ before

  get-private-global-timeline :
    ∀ {before n sid acc user} →
    ValidSession before sid acc user →
    Step before (read-global-timeline (just sid) n) before
      ∘ returned-timeline
      ∘ take n
      ∘ filter (can-read-post before sid)
      ∘ World.newest-first
      $ before

  get-public-global-timeline :
    ∀ {before n} →
    Step before (read-global-timeline nothing n) before
      ∘ returned-timeline
      ∘ take n
      ∘ filter (is-post-public before)
      ∘ World.newest-first
      $ before

  like-post :
    ∀ {before after sid pid acc user post post'} →
    ValidSession before sid acc user →
    CanReadPost before sid pid →
    World.post-at before pid ≡ just post →
    World.post-at after pid  ≡ just post' →
    user ∈ Post.likes post' →
    -- Rest of post unchanged
    Post.author post     ≡ Post.author post' →
    Post.text post       ≡ Post.text post' →
    Post.visibility post ≡ Post.visibility post' →
    Post.status post     ≡ Post.status post' →
    Post.replies post    ≡ Post.replies post' →
    Post.parent post     ≡ Post.parent post' →
    (∀ {user'} → user ≢ user' →
      ((user' ∈ Post.likes post) ≡ (user' ∈ Post.likes post')) ∧
        ((user' ∉ Post.likes post) ≡ (user' ∉ Post.likes post'))
    ) →
    -- Everything else unchanged
    ∀ {other-pids} →
    pid ≢ other-pids →
    World.account-at before         ≡ World.account-at after →
    World.session-at before         ≡ World.session-at after  →
    World.post-at before other-pids ≡ World.post-at after other-pids →
    World.follows before            ≡ World.follows after →
    World.newest-first before       ≡ World.newest-first after →
    Step before (like sid pid) after success

  failed-like-post :
    ∀ {before sid pid acc user} →
    ValidSession before sid acc user →
    ¬ CanReadPost before sid pid →
    Step before (like sid pid) before denied

  unlike-post :
    ∀ {before after sid pid acc user post post'} →
    ValidSession before sid acc user →
    CanReadPost before sid pid →
    World.post-at before pid ≡ just post' →
    World.post-at after pid  ≡ just post →
    user ∉ Post.likes post →
    -- Rest of post unchanged
    Post.author post'     ≡ Post.author post →
    Post.text post'       ≡ Post.text post →
    Post.visibility post' ≡ Post.visibility post →
    Post.status post'     ≡ Post.status post →
    Post.replies post'    ≡ Post.replies post →
    Post.parent post'     ≡ Post.parent post →
    ∀ {user'} →
    user ≢ user' →
    (user' ∈ Post.likes post') ≡ (user' ∈ Post.likes post) →
    -- Everything else unchanged
    ∀ {other-pids} →
    pid ≢ other-pids →
    World.post-at before other-pids ≡ World.post-at after other-pids →
    World.account-at before         ≡ World.account-at after →
    World.session-at before         ≡ World.session-at after  →
    World.follows before            ≡ World.follows after →
    World.newest-first before       ≡ World.newest-first after →
    Step before (unlike sid pid) after success

  failed-unlike-post :
    ∀ {before sid pid acc user} →
    ValidSession before sid acc user →
    ¬ CanReadPost before sid pid →
    Step before (unlike sid pid) before denied

  follow-user :
    ∀ {before after sid acc follower followee} →
    ValidSession before sid acc follower →
    World.follows after ≡ add-follower (World.follows before) follower followee →
    -- Everything else unchanged
    World.account-at before   ≡ World.account-at after →
    World.session-at before   ≡ World.session-at after →
    World.post-at before      ≡ World.post-at after →
    World.newest-first before ≡ World.newest-first after →
    Step before (follow sid followee) after success

  unfollow-user :
    ∀ {before after sid acc follower followee} →
    ValidSession before sid acc follower →
    World.follows after ≡ remove-follower (World.follows before) follower followee →
    -- Everything else unchanged
    World.account-at before   ≡ World.account-at after →
    World.session-at before   ≡ World.session-at after →
    World.post-at before      ≡ World.post-at after →
    World.newest-first before ≡ World.newest-first after →
    Step before (unfollow sid followee) after success

  logout :
    ∀ {before after sid user} →
    World.session-at before sid ≡ active user →
    World.session-at after sid  ≡ revoked →
    -- Everything else unchanged
    ∀ {other-sid} →
    sid ≢ other-sid →
    World.session-at before other-sid ≡ World.session-at after other-sid →
    World.account-at before           ≡ World.account-at after →
    World.post-at before              ≡ World.post-at after →
    World.follows before              ≡ World.follows after →
    World.newest-first before         ≡ World.newest-first after →
    Step before (revoke-token sid) after success

  session-timeout :
    ∀ {before after} →
    (∀ {sid user} → World.session-at before sid ≡ active user →
    World.session-at after sid  ≡ revoked) →
    -- Everything else unchanged
    (∀ {sid} →
      World.session-at before sid ≡ World.session-at after sid →
      World.account-at before     ≡ World.account-at after →
      World.post-at before        ≡ World.post-at after →
      World.follows before        ≡ World.follows after →
      World.newest-first before   ≡ World.newest-first after) →
    Step before time-passes after success

  -- reap-tombstones :
  --   ∀ {before after pid other-pid post other-post} →
  --   World.post-at before pid      ≡ just post →
  --   Post.status post              ≡ deleted →
  --   World.post-at after pid       ≡ nothing →
  --   World.post-at after other-pid ≡ just other-post →
  --   Post.status other-post        ≢ deleted →
  --   World.newest-first after      ≡ (filter (λ mpid → is-alive before mpid {{!!}}) ∘ World.newest-first $ before) →
  --   -- Everything else unchanged
  --   ∀ {live-pid live-post} →
  --   World.post-at before live-pid ≡ just live-post →
  --   Post.status live-post         ≡ live →
  --   World.post-at after live-pid  ≡ just live-post →
  --   World.account-at before       ≡ World.account-at after →
  --   World.session-at before       ≡ World.session-at after →
  --   World.follows before          ≡ World.follows after →
  --   Step before collect-dead-posts after success
