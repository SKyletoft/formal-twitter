open import Agda.Builtin.Bool                     using (Bool; true; false)
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat                      using (Nat)
open import Data.Empty                            using (⊥; ⊥-elim)
open import Data.List                             using (List; []; _∷_; length)
open import Data.Product                          using (_,_; proj₁; proj₂; ∃-syntax)
open import Data.String                           using (String; _≟_)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Data.Unit                             using (⊤; tt)
open import Relation.Binary.Definitions           using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym;
                                                         subst; trans)
open import Relation.Nullary.Decidable.Core        using (Dec; yes; no)
open import Relation.Nullary.Negation.Core        using (¬_)

open import Helpers

module ImplProofs
  (SessionId PostId : Set)
  (new-sid : CreateNew SessionId)
  (new-pid : CreateNew PostId)
  (_≟ₚ_ : DecidableEquality PostId)
  (_≟ₛᵢ_ : DecidableEquality SessionId)
  where

open import Twitter SessionId PostId new-sid new-pid _≟ₚ_ _≟ₛᵢ_

--------------------------------------------------------------------------------
-- Small helpers about membership and session statuses.
--------------------------------------------------------------------------------

-- A membership in a cons can be decomposed into the head or the tail.
∈-cons : {a : Set} {x y : a} {xs : List a} → x ∈ (y ∷ xs) → (x ≡ y) ⊎ (x ∈ xs)
∈-cons here       = inj₁ refl
∈-cons (there p)  = inj₂ p

∉-head : {a : Set} {x y : a} {xs : List a} → x ∉ (y ∷ xs) → x ≢ y
∉-head {x = x} {y} {xs} ¬p eq = ¬p (subst (λ z → x ∈ (z ∷ xs)) eq here)

∉-tail : {a : Set} {x y : a} {xs : List a} → x ∉ (y ∷ xs) → x ∉ xs
∉-tail ¬p = λ p → ¬p (there p)

-- Absence from a list and membership of another element are incompatible.
∈-not-eq : {a : Set} {x y : a} {xs : List a} → x ∉ xs → y ∈ xs → x ≢ y
∈-not-eq {x = x} {y} {xs} ¬p mem eq = ¬p (subst (λ z → z ∈ xs) (sym eq) mem)

≢-swap : {a : Set} {x y : a} → x ≢ y → y ≢ x
≢-swap ¬p = λ p → ¬p (sym p)

just-inj : {a : Set} {x y : a} → just x ≡ just y → x ≡ y
just-inj refl = refl

active≢unused : ∀ {u} → active u ≢ unused
active≢unused = λ ()

revoked≢unused : revoked ≢ unused
revoked≢unused = λ ()

unused≢active : ∀ {u} → unused ≢ active u
unused≢active = λ ()

revoked≢active : ∀ {u} → revoked ≢ active u
revoked≢active = λ ()

active-inj : ∀ {u v} → active u ≡ active v → u ≡ v
active-inj refl = refl

--------------------------------------------------------------------------------
-- Session tables: a session map with one entry overwritten.
--------------------------------------------------------------------------------

set-session : (SessionId → SessionStatus) → SessionId → SessionStatus
            → (SessionId → SessionStatus)
set-session f sid v s with s ≟ₛᵢ sid
... | yes _ = v
... | no  _ = f s

set-session-same : ∀ {f sid v} → set-session f sid v sid ≡ v
set-session-same {f} {sid} {v} with sid ≟ₛᵢ sid
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

set-session-other : ∀ {f sid v s} → s ≢ sid → set-session f sid v s ≡ f s
set-session-other {f} {sid} {v} {s} ¬e with s ≟ₛᵢ sid
... | yes p = ⊥-elim (¬e p)
... | no  _ = refl

-- `set-session` when the session is known to be `sid`.
set-session-same-at : ∀ {f sid v s} → s ≡ sid → set-session f sid v s ≡ v
set-session-same-at refl = set-session-same

--------------------------------------------------------------------------------
-- Account tables: an account map with one entry overwritten.
--------------------------------------------------------------------------------

set-account : (String → Maybe Account) → String → Maybe Account
            → (String → Maybe Account)
set-account f u v x with x ≟ u
... | yes _ = v
... | no  _ = f x

set-account-same : ∀ {f u v} → set-account f u v u ≡ v
set-account-same {f} {u} {v} with u ≟ u
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

set-account-other : ∀ {f u v x} → x ≢ u → set-account f u v x ≡ f x
set-account-other {f} {u} {v} {x} ¬e with x ≟ u
... | yes p = ⊥-elim (¬e p)
... | no  _ = refl

--------------------------------------------------------------------------------
-- Membership of the used-session list.
--------------------------------------------------------------------------------

∈?-sids : (x : SessionId) (xs : List SessionId) → Dec (x ∈ xs)
∈?-sids x [] = no (λ ())
∈?-sids x (y ∷ ys) with x ≟ₛᵢ y
... | yes refl = yes here
... | no ¬p with ∈?-sids x ys
...   | yes mem = yes (there mem)
...   | no ¬mem = no (λ m → aux (∈-cons m))
  where
    aux : (x ≡ y) ⊎ (x ∈ ys) → ⊥
    aux (inj₁ e) = ¬p e
    aux (inj₂ q) = ¬mem q

-- Every session that is not `unused` is listed in `used-session-ids`: the
-- "out" half of `only-used-sids` (Twitter.agda:82-86) is the contrapositive.
non-unused-session-used :
  (before : World) {sid : SessionId} →
  World.session-at before sid ≢ unused →
  sid ∈ World.used-session-ids before
non-unused-session-used before {sid} ¬unused
  with ∈?-sids sid (World.used-session-ids before)
... | yes mem = mem
... | no ¬mem = ⊥-elim (¬unused (proj₂ (World.only-used-sids before) ¬mem))

active-session-used :
  (before : World) {sid : SessionId} {user : String} →
  World.session-at before sid ≡ active user →
  sid ∈ World.used-session-ids before
active-session-used before {user = user} eq =
  non-unused-session-used before (λ p → active≢unused (trans (sym eq) p))

--------------------------------------------------------------------------------
-- Rebuilding a world that changes exactly one component.
--
-- Each rebuilder keeps every field of `before` but one, and re-discharges the
-- `World` invariants (Twitter.agda:64-116).  The individual obligations are
-- separated out so that the rebuilders -- and the theorems at the end -- stay
-- readable.
--------------------------------------------------------------------------------

-- `registered-world`: `username` now maps to `account passwd everyone`; the
-- session table is untouched, so `only-valid-sessions` has to look the user up
-- in the new account map.
registered-valid :
  (before : World) (username passwd : String) {sid : SessionId} {u : String} →
  World.session-at before sid ≡ active u →
  ∃[ acc ] set-account (World.account-at before) username
             (just (account passwd everyone)) u ≡ just acc
registered-valid before username passwd {sid} {u} eq = decide (u ≟ username)
  where
    accs = World.account-at before

    decide : Dec (u ≡ username) →
             ∃[ acc ] set-account accs username
                        (just (account passwd everyone)) u ≡ just acc
    decide (yes p) =
      (account passwd everyone ,
       trans (cong (λ z → set-account accs username
                            (just (account passwd everyone)) z) p)
             (set-account-same {f = accs} {u = username}
                               {v = just (account passwd everyone)}))
    decide (no ¬p)
      with World.only-valid-sessions before {sid = sid} {username = u} eq
    ... | acc , acc-eq =
      acc , trans (set-account-other {f = accs} {u = username}
                                     {v = just (account passwd everyone)}
                                     {x = u} ¬p) acc-eq

registered-world : (before : World) (username passwd : String) → World
registered-world before username passwd = record
  { account-at          = set-account (World.account-at before) username
                            (just (account passwd everyone))
  ; session-at          = World.session-at before
  ; post-at             = World.post-at before
  ; follows             = World.follows before
  ; newest-first        = World.newest-first before
  ; used-post-ids       = World.used-post-ids before
  ; used-session-ids    = World.used-session-ids before
  ; only-used-pids      = World.only-used-pids before
  ; only-used-sids      = World.only-used-sids before
  ; only-valid-sessions = registered-valid before username passwd
  ; only-valid-posts    = World.only-valid-posts before
  ; only-valid-replies  = World.only-valid-replies before
  ; no-duplicate-replies = World.no-duplicate-replies before
  ; no-duplicate-likes   = World.no-duplicate-likes before
  ; no-duplicate-posts   = World.no-duplicate-posts before
  }

-- `logged-in-world`: `sid` becomes `active username` and is recorded as used.
logged-in-used :
  (before : World) (sid : SessionId) (username : String) {s : SessionId} →
  (s ∈ (sid ∷ World.used-session-ids before) →
     set-session (World.session-at before) sid (active username) s ≢ unused)
  ∧ (s ∉ (sid ∷ World.used-session-ids before) →
     set-session (World.session-at before) sid (active username) s ≡ unused)
logged-in-used before sid username {s} = in-part , out-part
  where
    sess = World.session-at before
    v    = active username

    in-part : s ∈ (sid ∷ World.used-session-ids before) →
              set-session sess sid v s ≢ unused
    in-part mem = aux (∈-cons mem)
      where
        aux : (s ≡ sid) ⊎ (s ∈ World.used-session-ids before) →
              set-session sess sid v s ≢ unused
        aux (inj₁ refl) eq =
          active≢unused (trans (sym (set-session-same {f = sess} {sid = sid}
                                                      {v = v})) eq)
        aux (inj₂ mem') = decide-mem mem'
          where
            decide-mem : s ∈ World.used-session-ids before →
                         set-session sess sid v s ≢ unused
            decide-mem mem'' = decide (s ≟ₛᵢ sid)
              where
                decide : Dec (s ≡ sid) → set-session sess sid v s ≢ unused
                decide (yes p) eq =
                  active≢unused (trans (sym (set-session-same-at
                    {f = sess} {sid = sid} {v = v} {s = s} p)) eq)
                decide (no ¬p) eq =
                  proj₁ (World.only-used-sids before) mem''
                    (trans (sym (set-session-other
                      {f = sess} {sid = sid} {v = v} {s = s} ¬p)) eq)

    out-part : s ∉ (sid ∷ World.used-session-ids before) →
               set-session sess sid v s ≡ unused
    out-part ¬mem =
      trans (set-session-other {f = sess} {sid = sid} {v = v} {s = s}
                               (∉-head ¬mem))
            (proj₂ (World.only-used-sids before) (∉-tail ¬mem))

logged-in-valid :
  (before : World) (sid : SessionId) (username : String) (acc : Account) →
  World.account-at before username ≡ just acc →
  {s : SessionId} {u : String} →
  set-session (World.session-at before) sid (active username) s ≡ active u →
  ∃[ a ] World.account-at before u ≡ just a
logged-in-valid before sid username acc acc-eq {s} {u} eq = decide (s ≟ₛᵢ sid)
  where
    sess = World.session-at before

    decide : Dec (s ≡ sid) → ∃[ a ] World.account-at before u ≡ just a
    decide (yes p) =
      acc , subst (λ z → World.account-at before z ≡ just acc)
                  (active-inj (trans (sym (set-session-same-at
                    {f = sess} {sid = sid} {v = active username} {s = s} p)) eq))
                  acc-eq
    decide (no ¬p) =
      World.only-valid-sessions before {sid = s} {username = u}
        (trans (sym (set-session-other
          {f = sess} {sid = sid} {v = active username} {s = s} ¬p)) eq)

logged-in-world :
  (before : World) (sid : SessionId) (username : String) (acc : Account) →
  World.account-at before username ≡ just acc → World
logged-in-world before sid username acc acc-eq = record
  { account-at          = World.account-at before
  ; session-at          = set-session (World.session-at before) sid (active username)
  ; post-at             = World.post-at before
  ; follows             = World.follows before
  ; newest-first        = World.newest-first before
  ; used-post-ids       = World.used-post-ids before
  ; used-session-ids    = sid ∷ World.used-session-ids before
  ; only-used-pids      = World.only-used-pids before
  ; only-used-sids      = logged-in-used before sid username
  ; only-valid-sessions = logged-in-valid before sid username acc acc-eq
  ; only-valid-posts    = World.only-valid-posts before
  ; only-valid-replies  = World.only-valid-replies before
  ; no-duplicate-replies = World.no-duplicate-replies before
  ; no-duplicate-likes   = World.no-duplicate-likes before
  ; no-duplicate-posts   = World.no-duplicate-posts before
  }

-- `logged-out-world`: `sid` becomes `revoked`; the used-session list is
-- untouched, so `sid` must already be listed (a revoked session is not
-- `unused`, hence `only-used-sids` already lists it).
logged-out-used :
  (before : World) (sid : SessionId) → sid ∈ World.used-session-ids before →
  {s : SessionId} →
  (s ∈ World.used-session-ids before →
     set-session (World.session-at before) sid revoked s ≢ unused)
  ∧ (s ∉ World.used-session-ids before →
     set-session (World.session-at before) sid revoked s ≡ unused)
logged-out-used before sid sid-in {s} = in-part , out-part
  where
    sess = World.session-at before

    in-part : s ∈ World.used-session-ids before →
              set-session sess sid revoked s ≢ unused
    in-part mem = decide (s ≟ₛᵢ sid)
      where
        decide : Dec (s ≡ sid) → set-session sess sid revoked s ≢ unused
        decide (yes p) eq =
          revoked≢unused (trans (sym (set-session-same-at
            {f = sess} {sid = sid} {v = revoked} {s = s} p)) eq)
        decide (no ¬p) eq =
          proj₁ (World.only-used-sids before) mem
            (trans (sym (set-session-other
              {f = sess} {sid = sid} {v = revoked} {s = s} ¬p)) eq)

    out-part : s ∉ World.used-session-ids before →
               set-session sess sid revoked s ≡ unused
    out-part ¬mem =
      trans (set-session-other {f = sess} {sid = sid} {v = revoked} {s = s}
                               (∈-not-eq ¬mem sid-in))
            (proj₂ (World.only-used-sids before) ¬mem)

logged-out-valid :
  (before : World) (sid : SessionId) {s : SessionId} {u : String} →
  set-session (World.session-at before) sid revoked s ≡ active u →
  ∃[ a ] World.account-at before u ≡ just a
logged-out-valid before sid {s} {u} eq = decide (s ≟ₛᵢ sid)
  where
    decide : Dec (s ≡ sid) → ∃[ a ] World.account-at before u ≡ just a
    decide (yes p) =
      ⊥-elim (revoked≢active (trans (sym (set-session-same-at
        {f = World.session-at before} {sid = sid} {v = revoked} {s = s} p)) eq))
    decide (no ¬p) =
      World.only-valid-sessions before {sid = s} {username = u}
        (trans (sym (set-session-other
          {f = World.session-at before} {sid = sid} {v = revoked}
          {s = s} ¬p)) eq)

logged-out-world :
  (before : World) (sid : SessionId) → sid ∈ World.used-session-ids before → World
logged-out-world before sid sid-in = record
  { account-at          = World.account-at before
  ; session-at          = set-session (World.session-at before) sid revoked
  ; post-at             = World.post-at before
  ; follows             = World.follows before
  ; newest-first        = World.newest-first before
  ; used-post-ids       = World.used-post-ids before
  ; used-session-ids    = World.used-session-ids before
  ; only-used-pids      = World.only-used-pids before
  ; only-used-sids      = logged-out-used before sid sid-in
  ; only-valid-sessions = logged-out-valid before sid
  ; only-valid-posts    = World.only-valid-posts before
  ; only-valid-replies  = World.only-valid-replies before
  ; no-duplicate-replies = World.no-duplicate-replies before
  ; no-duplicate-likes   = World.no-duplicate-likes before
  ; no-duplicate-posts   = World.no-duplicate-posts before
  }

--------------------------------------------------------------------------------
-- P1: register (Twitter.agda:470-488)
--------------------------------------------------------------------------------

-- A fresh username produces `success` and stores the account with the given
-- password and visibility `everyone`, on any world.  `before`'s invariants
-- (Twitter.agda:64-116) are what makes the after-world well formed: sessions
-- may keep pointing at any other account, because `registered-world` leaves
-- every other username untouched.
register-success :
  ∀ (before : World) {username passwd : String} →
  World.account-at before username ≡ nothing →
  Step before (register username passwd) (registered-world before username passwd) success
register-success before {username} {passwd} absent = create-account
  {before   = before}
  {after    = registered-world before username passwd}
  {username = username}
  {passwd   = passwd}
  absent
  (set-account-same {f = World.account-at before} {u = username}
                    {v = just (account passwd everyone)})
  (λ {sid} {pid} {u1} {u2} ¬u1 ¬u2 →
       sym (set-account-other {f = World.account-at before} {u = username}
                              {v = just (account passwd everyone)} {x = u1}
                              (≢-swap ¬u1))
     , refl , refl , refl , refl)

-- Registering a taken username fails and leaves the world untouched.
register-duplicate :
  ∀ (before : World) {username passwd : String} →
  World.account-at before username ≢ nothing →
  Step before (register username passwd) before signup-failed
register-duplicate before {username} {passwd} taken =
  failed-create-account {before = before} {username = username} {passwd = passwd} taken

--------------------------------------------------------------------------------
-- P2: authenticate (Twitter.agda:490-516)
--------------------------------------------------------------------------------

-- Logging in with the right password issues a session for the account, keeps
-- every other session, account, post and follow exactly as it was, and yields
-- a `ValidSession` (Twitter.agda:147-156) for the new session.
login-success :
  ∀ (before : World) {username passwd : String} {sid : SessionId} {acc : Account}
  (unused-eq : World.session-at before sid ≡ unused)
  (acc-eq : World.account-at before username ≡ just acc) →
  Account.password acc ≡ passwd →
  Step before (authenticate username passwd)
       (logged-in-world before sid username acc acc-eq) (issued-session sid)
login-success before {username} {passwd} {sid} {acc} unused-eq acc-eq pw = login
  {before   = before}
  {after    = logged-in-world before sid username acc acc-eq}
  {username = username}
  {passwd   = passwd}
  {sid      = sid}
  {user     = acc}
  unused-eq
  (set-session-same {f = World.session-at before} {sid = sid} {v = active username})
  acc-eq
  pw
  (λ {other-sid} {pid} {u1} {u2} ¬e →
       sym (set-session-other {f = World.session-at before} {sid = sid}
                              {v = active username} {s = other-sid} (≢-swap ¬e))
     , refl , refl , refl , refl)
  (valid-session (set-session-same {f = World.session-at before} {sid = sid}
                                   {v = active username}) acc-eq)

-- Logging in as a username that does not exist fails.
login-absent :
  ∀ (before : World) {username passwd : String} →
  World.account-at before username ≡ nothing →
  Step before (authenticate username passwd) before login-failed
login-absent before {username} {passwd} absent =
  failed-login-1 {before = before} {username = username} {passwd = passwd} absent

-- Logging in with the wrong password fails and creates no session, on any
-- world that holds `username`.
login-wrong-password :
  ∀ (before : World) {username passwd : String} {user : Account} →
  World.account-at before username ≡ just user →
  Account.password user ≢ passwd →
  Step before (authenticate username passwd) before login-failed
login-wrong-password before {username} {passwd} {user} acc-eq ¬pw =
  failed-login-2 {before = before} {username = username} {passwd = passwd}
                 {user = user} acc-eq ¬pw

--------------------------------------------------------------------------------
-- P3: revoke-token (Twitter.agda:677-689) and P4: failed-access (464-468)
--------------------------------------------------------------------------------

-- An active session becomes revoked and nothing else changes -- no other
-- session, no account, no post and no follow of the arbitrary world.
logout-success :
  ∀ (before : World) {sid : SessionId} {username : String}
  (act : World.session-at before sid ≡ active username) →
  Step before (revoke-token sid)
       (logged-out-world before sid (active-session-used before act)) success
logout-success before {sid} {username} act = logout
  {before = before}
  {after  = logged-out-world before sid (active-session-used before act)}
  {sid    = sid}
  {user   = username}
  act
  (set-session-same {f = World.session-at before} {sid = sid} {v = revoked})
  (λ {other-sid} ¬e →
       sym (set-session-other {f = World.session-at before} {sid = sid}
                              {v = revoked} {s = other-sid} (≢-swap ¬e))
     , refl , refl , refl , refl)

-- There is no valid-session witness for a session that is not active.
no-valid-session :
  (before : World) (sid : SessionId) →
  (∀ {user} → World.session-at before sid ≡ active user → ⊥) →
  ¬ (∃[ acc ] ∃[ username ] ValidSession before sid acc username)
no-valid-session before sid ¬active (acc , user , vs) =
  ¬active (ValidSession.session-unchanged vs)

-- `failed-access`: a command whose session is not active expires the request
-- and leaves the world untouched.
failed-access-inactive :
  (before : World) (cmd : Command) (sid : SessionId) →
  extract-sid cmd ≡ just sid →
  (∀ {user} → World.session-at before sid ≡ active user → ⊥) →
  Step before cmd before expired
failed-access-inactive before cmd sid sid-eq ¬active = failed-access
  (λ {sid'} eq → subst (λ s → ¬ (∃[ acc ] ∃[ username ]
                                   ValidSession before s acc username))
                       (sym (just-inj (trans (sym eq) sid-eq)))
                       (no-valid-session before sid ¬active))

-- Revoking a token that is already revoked expires the request.
logout-expired :
  ∀ (before : World) (sid : SessionId) →
  World.session-at before sid ≡ revoked →
  Step before (revoke-token sid) before expired
logout-expired before sid rev-eq =
  failed-access-inactive before (revoke-token sid) sid refl
    (λ {u} eq → revoked≢active (trans (sym rev-eq) eq))

-- Revoking a token that was never issued expires the request.
logout-unused :
  ∀ (before : World) (sid : SessionId) →
  World.session-at before sid ≡ unused →
  Step before (revoke-token sid) before expired
logout-unused before sid unused-eq =
  failed-access-inactive before (revoke-token sid) sid refl
    (λ {u} eq → unused≢active (trans (sym unused-eq) eq))

--------------------------------------------------------------------------------
-- Post tables: a post map with one entry overwritten.
--------------------------------------------------------------------------------

set-post : (PostId → Maybe Post) → PostId → Maybe Post → (PostId → Maybe Post)
set-post f pid v x with x ≟ₚ pid
... | yes _ = v
... | no  _ = f x

set-post-same : ∀ {f pid v} → set-post f pid v pid ≡ v
set-post-same {f} {pid} {v} with pid ≟ₚ pid
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

set-post-same-at : ∀ {f pid v x} → x ≡ pid → set-post f pid v x ≡ v
set-post-same-at refl = set-post-same

set-post-other : ∀ {f pid v x} → x ≢ pid → set-post f pid v x ≡ f x
set-post-other {f} {pid} {v} {x} ¬e with x ≟ₚ pid
... | yes p = ⊥-elim (¬e p)
... | no  _ = refl

just≢nothing : ∀ {a : Set} {x : a} → just x ≢ nothing
just≢nothing = λ ()

nothing≢just : ∀ {a : Set} {x : a} → nothing ≢ just x
nothing≢just = λ ()

∈-nil : ∀ {a : Set} {x : a} → x ∈ [] → ⊥
∈-nil = λ ()

--------------------------------------------------------------------------------
-- Membership of the used-post list, and the pid facts the post rebuilders need.
--------------------------------------------------------------------------------

∈?-pids : (x : PostId) (xs : List PostId) → Dec (x ∈ xs)
∈?-pids x [] = no (λ ())
∈?-pids x (y ∷ ys) with x ≟ₚ y
... | yes refl = yes here
... | no ¬p with ∈?-pids x ys
...   | yes mem = yes (there mem)
...   | no ¬mem = no (λ m → aux (∈-cons m))
  where
    aux : (x ≡ y) ⊎ (x ∈ ys) → ⊥
    aux (inj₁ e) = ¬p e
    aux (inj₂ q) = ¬mem q

-- `only-used-pids` (Twitter.agda:78-81) read as a contrapositive: a post that
-- is present is listed.
present-used :
  (before : World) {pid : PostId} {pst : Post} →
  World.post-at before pid ≡ just pst →
  pid ∈ World.used-post-ids before
present-used before {pid} {pst} eq with ∈?-pids pid (World.used-post-ids before)
... | yes mem = mem
... | no ¬mem =
  ⊥-elim (nothing≢just (trans (sym (proj₂ (World.only-used-pids before) ¬mem)) eq))

-- The `was-absent` half of `PostIsNew` (Twitter.agda:147-156) rules the pid out
-- of `used-post-ids`.
absent-unused :
  (before : World) {pid : PostId} →
  World.post-at before pid ≡ nothing →
  pid ∉ World.used-post-ids before
absent-unused before {pid} eq mem =
  proj₁ (World.only-used-pids before) mem eq

-- ... and out of `newest-first` (`only-valid-posts`, Twitter.agda:92-97).
absent∉newest :
  (before : World) {pid : PostId} →
  World.post-at before pid ≡ nothing →
  pid ∉ World.newest-first before
absent∉newest before {pid} eq mem with World.only-valid-posts before mem
... | pst , peq = ⊥-elim (nothing≢just (trans (sym eq) peq))

-- ... and out of the replies of every post (`only-valid-replies`,
-- Twitter.agda:98-106): a reply's post must exist.
absent∉replies :
  (before : World) {pid ppid : PostId} {ppost : Post} →
  World.post-at before pid ≡ nothing →
  World.post-at before ppid ≡ just ppost →
  pid ∉ Post.replies ppost
absent∉replies before {pid} {ppid} {ppost} eq peq mem
  with World.only-valid-replies before mem peq
... | child-post , ceq , _ =
  ⊥-elim (nothing≢just (trans (sym eq) ceq))

--------------------------------------------------------------------------------
-- `posted-world`: a fresh pid holds `new-post`.
--
-- Invariant obligations are separated out, like the T2a rebuilders.
--------------------------------------------------------------------------------

posted-used :
  (before : World) (pid : PostId) (np : Post) {x : PostId} →
  (x ∈ (pid ∷ World.used-post-ids before) →
     set-post (World.post-at before) pid (just np) x ≢ nothing)
  ∧ (x ∉ (pid ∷ World.used-post-ids before) →
     set-post (World.post-at before) pid (just np) x ≡ nothing)
posted-used before pid np {x} = in-part , out-part
  where
    f = World.post-at before

    in-part : x ∈ (pid ∷ World.used-post-ids before) →
              set-post f pid (just np) x ≢ nothing
    in-part mem = aux (∈-cons mem)
      where
        aux : (x ≡ pid) ⊎ (x ∈ World.used-post-ids before) →
              set-post f pid (just np) x ≢ nothing
        aux (inj₁ refl) eq =
          just≢nothing (trans (sym (set-post-same {f = f} {pid = pid}
                                            {v = just np})) eq)
        aux (inj₂ mem') = decide (x ≟ₚ pid)
          where
            decide : Dec (x ≡ pid) → set-post f pid (just np) x ≢ nothing
            decide (yes p) =
              λ eq' → just≢nothing
                (trans (sym (set-post-same-at {f = f} {pid = pid}
                                              {v = just np} p)) eq')
            decide (no ¬p) =
              λ eq' → proj₁ (World.only-used-pids before) mem'
                (trans (sym (set-post-other {f = f} {pid = pid}
                                            {v = just np} ¬p)) eq')

    out-part : x ∉ (pid ∷ World.used-post-ids before) →
               set-post f pid (just np) x ≡ nothing
    out-part ¬mem =
      trans (set-post-other {f = f} {pid = pid} {v = just np} (∉-head ¬mem))
            (proj₂ (World.only-used-pids before) (∉-tail ¬mem))

posted-valid-posts :
  (before : World) (pid : PostId) (np : Post) →
  World.post-at before pid ≡ nothing →
  {y : PostId} →
  y ∈ (pid ∷ World.newest-first before) →
  ∃[ post ] set-post (World.post-at before) pid (just np) y ≡ just post
posted-valid-posts before pid np absent {y} mem = aux (∈-cons mem)
  where
    f = World.post-at before
    not-new = absent∉newest before {pid} absent

    aux : (y ≡ pid) ⊎ (y ∈ World.newest-first before) →
          ∃[ post ] set-post f pid (just np) y ≡ just post
    aux (inj₁ refl) = np , set-post-same
    aux (inj₂ mem') with World.only-valid-posts before mem'
    ... | pst , peq =
      pst , trans (set-post-other {f = f} {pid = pid} {v = just np}
                                   (≢-swap (∈-not-eq not-new mem'))) peq

posted-replies :
  (before : World) (pid : PostId) (np : Post) →
  World.post-at before pid ≡ nothing →
  Post.replies np ≡ [] →
  {child parent-pid : PostId} {parent-post : Post} →
  child ∈ Post.replies parent-post →
  set-post (World.post-at before) pid (just np) parent-pid ≡ just parent-post →
  ∃[ child-post ]
    set-post (World.post-at before) pid (just np) child ≡ just child-post
    ∧ Post.parent child-post ≡ just parent-pid
    ∧ child ≢ parent-pid
posted-replies before pid np absent np-replies {child} {parent-pid} {parent-post}
               mem peq = decide (parent-pid ≟ₚ pid)
  where
    f = World.post-at before

    decide :
      Dec (parent-pid ≡ pid) →
      ∃[ child-post ]
        set-post f pid (just np) child ≡ just child-post
        ∧ Post.parent child-post ≡ just parent-pid
        ∧ child ≢ parent-pid
    decide (yes p) =
      ⊥-elim (∈-nil (subst (λ q → child ∈ q) np-replies
        (subst (λ q → child ∈ Post.replies q)
               (sym (just-inj (trans (sym (set-post-same-at {f = f} {pid = pid}
                                                      {v = just np} p)) peq)))
               mem)))
    decide (no ¬p) with World.only-valid-replies before mem
                           (trans (sym (set-post-other {f = f} {pid = pid}
                                                       {v = just np} ¬p)) peq)
    ... | child-post , ceq , cp , cn = decide-child (child ≟ₚ pid)
      where
        decide-child :
          Dec (child ≡ pid) →
          ∃[ cp' ]
            set-post f pid (just np) child ≡ just cp'
            ∧ Post.parent cp' ≡ just parent-pid
            ∧ child ≢ parent-pid
        decide-child (yes q) =
          ⊥-elim (nothing≢just (trans (sym (f-absent q)) ceq))
          where
            f-absent : child ≡ pid → f child ≡ nothing
            f-absent refl = absent
        decide-child (no ¬q) =
          child-post , trans (set-post-other {f = f} {pid = pid}
                                           {v = just np} ¬q) ceq
                      , cp , cn

posted-uniq-replies :
  (before : World) (pid : PostId) (np : Post) →
  Post.replies np ≡ [] →
  {y : PostId} {p : Post} →
  set-post (World.post-at before) pid (just np) y ≡ just p →
  uniq (Post.replies p)
posted-uniq-replies before pid np np-replies {y} {p} eq = decide (y ≟ₚ pid)
  where
    f = World.post-at before

    decide : Dec (y ≡ pid) → uniq (Post.replies p)
    decide (yes q) =
      subst (λ r → uniq (Post.replies r))
            (just-inj (trans (sym (set-post-same-at {f = f} {pid = pid}
                                                   {v = just np} q)) eq))
            (subst (λ r → uniq r) (sym np-replies) tt)
    decide (no ¬q) =
      World.no-duplicate-replies before
        (trans (sym (set-post-other {f = f} {pid = pid} {v = just np} ¬q)) eq)

posted-uniq-likes :
  (before : World) (pid : PostId) (np : Post) →
  Post.likes np ≡ [] →
  {y : PostId} {p : Post} →
  set-post (World.post-at before) pid (just np) y ≡ just p →
  uniq (Post.likes p)
posted-uniq-likes before pid np np-likes {y} {p} eq = decide (y ≟ₚ pid)
  where
    f = World.post-at before

    decide : Dec (y ≡ pid) → uniq (Post.likes p)
    decide (yes q) =
      subst (λ r → uniq (Post.likes r))
            (just-inj (trans (sym (set-post-same-at {f = f} {pid = pid}
                                                   {v = just np} q)) eq))
            (subst (λ r → uniq r) (sym np-likes) tt)
    decide (no ¬q) =
      World.no-duplicate-likes before
        (trans (sym (set-post-other {f = f} {pid = pid} {v = just np} ¬q)) eq)

posted-world :
  (before : World) (pid : PostId) (new-post : Post) →
  World.post-at before pid ≡ nothing →
  pid ∉ World.used-post-ids before →
  Post.replies new-post ≡ [] →
  Post.likes new-post ≡ [] →
  World
posted-world before pid new-post absent unused-pid np-replies np-likes = record
  { account-at          = World.account-at before
  ; session-at          = World.session-at before
  ; post-at             = set-post (World.post-at before) pid (just new-post)
  ; follows             = World.follows before
  ; newest-first        = pid ∷ World.newest-first before
  ; used-post-ids       = pid ∷ World.used-post-ids before
  ; used-session-ids    = World.used-session-ids before
  ; only-used-pids      = posted-used before pid new-post
  ; only-used-sids      = World.only-used-sids before
  ; only-valid-sessions = World.only-valid-sessions before
  ; only-valid-posts    = posted-valid-posts before pid new-post absent
  ; only-valid-replies  = posted-replies before pid new-post absent np-replies
  ; no-duplicate-replies = posted-uniq-replies before pid new-post np-replies
  ; no-duplicate-likes   = posted-uniq-likes before pid new-post np-likes
  ; no-duplicate-posts   =
      (absent∉newest before {pid} absent , World.no-duplicate-posts before)
  }

--------------------------------------------------------------------------------
-- P5: publish without a parent -- `successful-post` (Twitter.agda:387-398)
--------------------------------------------------------------------------------

-- A fresh pid holds `new-post username txt acc`, heads `newest-first`, and
-- nothing else in the arbitrary world moves.
post-success :
  ∀ (before : World) {sid : SessionId} {txt username : String}
    {pid : PostId} {acc : Account}
  (vs : ValidSession before sid acc username)
  (absent : World.post-at before pid ≡ nothing)
  (unused-pid : pid ∉ World.used-post-ids before) →
  Step before (publish sid txt nothing)
       (posted-world before pid (new-post username txt acc) absent unused-pid refl refl)
       (created-post pid)
post-success before {sid} {txt} {username} {pid} {acc} vs absent unused-pid =
  successful-post
    {before   = before}
    {after    = posted-world before pid (new-post username txt acc)
                             absent unused-pid refl refl}
    {sid      = sid}
    {txt      = txt}
    {username = username}
    {user     = acc}
    {pid      = pid}
    {acc      = acc}
    vs
    (post-is-new absent set-post-same)
    refl
    (λ {other} ¬e →
         sym (set-post-other {f = World.post-at before} {pid = pid}
                             {v = just (new-post username txt acc)}
                             (≢-swap ¬e))
       , refl , refl , refl)

--------------------------------------------------------------------------------
-- `reply-world`: a fresh child at `pid`, and `ppid`'s post gaining a reply.
--
-- The post table is updated twice, so the invariants are rebuilt once for the
-- child and once for the parent. `pid ∉ used-post-ids` is what keeps
-- `only-used-pids` and `no-duplicate-posts` intact; the old invariants then
-- give `pid ∉ newest-first` and `pid ∉ preplies`.
--------------------------------------------------------------------------------

reply-at :
  (PostId → Maybe Post) → PostId → Post → PostId → Post → PostId → Maybe Post
reply-at f pid child ppid parent x =
  set-post (set-post f pid (just child)) ppid (just parent) x

reply-at-other :
  ∀ {f pid child ppid parent x} →
  x ≢ ppid → x ≢ pid →
  reply-at f pid child ppid parent x ≡ f x
reply-at-other {x = x} ¬pp ¬p =
  trans (set-post-other {x = x} ¬pp) (set-post-other {x = x} ¬p)

reply-at-child :
  ∀ {f pid child ppid parent} →
  pid ≢ ppid →
  reply-at f pid child ppid parent pid ≡ just child
reply-at-child {pid = pid} ¬e =
  trans (set-post-other {x = pid} ¬e) set-post-same

reply-at-parent :
  ∀ {f pid child ppid parent} →
  reply-at f pid child ppid parent ppid ≡ just parent
reply-at-parent = set-post-same

reply-used :
  (before : World) (pid ppid : PostId) (child ppost' : Post) →
  pid ≢ ppid →
  ppid ∈ World.used-post-ids before →
  {x : PostId} →
  (x ∈ (pid ∷ World.used-post-ids before) →
     reply-at (World.post-at before) pid child ppid ppost' x ≢ nothing)
  ∧ (x ∉ (pid ∷ World.used-post-ids before) →
     reply-at (World.post-at before) pid child ppid ppost' x ≡ nothing)
reply-used before pid ppid child ppost' pid≢ppid ppid-used {x} = in-part , out-part
  where
    f = World.post-at before
    At = reply-at f pid child ppid ppost'

    in-part : x ∈ (pid ∷ World.used-post-ids before) → At x ≢ nothing
    in-part mem = aux (∈-cons mem)
      where
        aux : (x ≡ pid) ⊎ (x ∈ World.used-post-ids before) → At x ≢ nothing
        aux (inj₁ refl) eq =
          just≢nothing (trans (sym (reply-at-child {f = f} {pid = pid}
                                                  {child = child} {ppid = ppid}
                                                  {parent = ppost'} pid≢ppid)) eq)
        aux (inj₂ mem') = decide-pp (x ≟ₚ ppid)
          where
            decide-pp : Dec (x ≡ ppid) → At x ≢ nothing
            decide-pp (yes p) =
              λ eq' → just≢nothing
                (trans (sym (set-post-same-at
                  {f = set-post f pid (just child)} {pid = ppid}
                  {v = just ppost'} {x = x} p)) eq')
            decide-pp (no ¬pp) = decide-pid (x ≟ₚ pid)
              where
                decide-pid : Dec (x ≡ pid) → At x ≢ nothing
                decide-pid (yes q) =
                  λ eq' → just≢nothing
                    (trans (sym (trans (set-post-other {x = x} ¬pp)
                                       (set-post-same-at {x = x} q))) eq')
                decide-pid (no ¬p) =
                  λ eq' → proj₁ (World.only-used-pids before) mem'
                    (trans (sym (trans (set-post-other {x = x} ¬pp)
                                       (set-post-other {x = x} ¬p))) eq')

    out-part : x ∉ (pid ∷ World.used-post-ids before) → At x ≡ nothing
    out-part ¬mem = decide-pp (x ≟ₚ ppid)
      where
        x∉used = ∉-tail ¬mem
        x≠pid = ∉-head ¬mem
        x≠ppid = ∈-not-eq x∉used ppid-used

        decide-pp : Dec (x ≡ ppid) → At x ≡ nothing
        decide-pp (yes p) = ⊥-elim (x≠ppid p)
        decide-pp (no ¬pp) =
          trans (reply-at-other {x = x} ¬pp x≠pid)
                (proj₂ (World.only-used-pids before) x∉used)

reply-valid-posts :
  (before : World) (pid ppid : PostId) (child ppost' : Post) →
  pid ≢ ppid →
  pid ∉ World.newest-first before →
  {y : PostId} →
  y ∈ (pid ∷ World.newest-first before) →
  ∃[ pst ] reply-at (World.post-at before) pid child ppid ppost' y ≡ just pst
reply-valid-posts before pid ppid child ppost' pid≢ppid not-new {y} mem =
  aux (∈-cons mem)
  where
    f = World.post-at before
    At = reply-at f pid child ppid ppost'

    aux : (y ≡ pid) ⊎ (y ∈ World.newest-first before) →
          ∃[ pst ] At y ≡ just pst
    aux (inj₁ refl) =
      child , reply-at-child {f = f} {pid = pid} {child = child}
                             {ppid = ppid} {parent = ppost'} pid≢ppid
    aux (inj₂ mem') with World.only-valid-posts before mem'
    ... | pst , peq = decide-pp (y ≟ₚ ppid)
      where
        y≠pid = ≢-swap (∈-not-eq not-new mem')

        decide-pp : Dec (y ≡ ppid) → ∃[ pst' ] At y ≡ just pst'
        decide-pp (yes p) =
          ppost' , set-post-same-at {f = set-post f pid (just child)}
                                    {pid = ppid} {v = just ppost'} {x = y} p
        decide-pp (no ¬pp) =
          pst , trans (reply-at-other {x = y} ¬pp y≠pid) peq

reply-replies :
  (before : World) (pid ppid : PostId) (child ppost ppost' : Post) →
  pid ≢ ppid →
  World.post-at before ppid ≡ just ppost →
  World.post-at before pid ≡ nothing →
  Post.parent child ≡ just ppid →
  Post.parent ppost' ≡ Post.parent ppost →
  Post.replies ppost' ≡ pid ∷ Post.replies ppost →
  Post.replies child ≡ [] →
  {c q : PostId} {qpost : Post} →
  c ∈ Post.replies qpost →
  reply-at (World.post-at before) pid child ppid ppost' q ≡ just qpost →
  ∃[ cpost ]
    reply-at (World.post-at before) pid child ppid ppost' c ≡ just cpost
    ∧ Post.parent cpost ≡ just q
    ∧ c ≢ q
reply-replies before pid ppid child ppost ppost' pid≢ppid ppost-eq pid-absent
             child-parent ppost'-parent ppost'-replies child-replies
             {c} {q} {qpost} mem qeq = decide-q (q ≟ₚ pid)
  where
    f = World.post-at before
    At = reply-at f pid child ppid ppost'

    At-from : ∀ {z} {cpost : Post} → f z ≡ just cpost → z ≢ pid → z ≢ ppid →
              At z ≡ just cpost
    At-from {z} ceq ¬p ¬pp =
      trans (trans (set-post-other {x = z} ¬pp) (set-post-other {x = z} ¬p)) ceq

    f-absent : c ≡ pid → f c ≡ nothing
    f-absent refl = pid-absent

    decide-q :
      Dec (q ≡ pid) →
      ∃[ cpost ] At c ≡ just cpost ∧ Post.parent cpost ≡ just q ∧ c ≢ q
    decide-q (yes qp) =
      ⊥-elim (∈-nil (subst (λ r → c ∈ r) child-replies
        (subst (λ r → c ∈ Post.replies r) qpost-eq mem)))
      where
        qpost-eq : qpost ≡ child
        qpost-eq = sym (just-inj
          (trans (sym (reply-at-child {f = f} {pid = pid} {child = child}
                                      {ppid = ppid} {parent = ppost'} pid≢ppid))
                 (subst (λ z → At z ≡ just qpost) qp qeq)))
    decide-q (no ¬qp) = decide-pp (q ≟ₚ ppid)
      where
        decide-pp :
          Dec (q ≡ ppid) →
          ∃[ cpost ] At c ≡ just cpost ∧ Post.parent cpost ≡ just q ∧ c ≢ q
        decide-pp (yes qpp) = decide-c (c ≟ₚ pid)
          where
            qpost-eq : ppost' ≡ qpost
            qpost-eq = just-inj
              (trans (sym (reply-at-parent {f = f} {pid = pid} {child = child}
                                           {ppid = ppid} {parent = ppost'}))
                     (subst (λ z → At z ≡ just qpost) qpp qeq))

            mem' : c ∈ Post.replies ppost'
            mem' = subst (λ r → c ∈ Post.replies r) (sym qpost-eq) mem

            mem'' : c ∈ (pid ∷ Post.replies ppost)
            mem'' = subst (λ r → c ∈ r) ppost'-replies mem'

            decide-c :
              Dec (c ≡ pid) →
              ∃[ cpost ] At c ≡ just cpost ∧ Post.parent cpost ≡ just q ∧ c ≢ q
            decide-c (yes cp) =
              ( child
              , subst (λ z → At z ≡ just child) (sym cp)
                      (reply-at-child {f = f} {pid = pid} {child = child}
                                      {ppid = ppid} {parent = ppost'} pid≢ppid)
              , subst (λ z → Post.parent child ≡ just z) (sym qpp) child-parent
              , (λ z → pid≢ppid (trans (sym cp) (trans z qpp))) )
            decide-c (no ¬cp) = aux (∈-cons mem'')
              where
                aux : (c ≡ pid) ⊎ (c ∈ Post.replies ppost) →
                      ∃[ cpost ] At c ≡ just cpost
                      ∧ Post.parent cpost ≡ just q ∧ c ≢ q
                aux (inj₁ cp) = ⊥-elim (¬cp cp)
                aux (inj₂ mem-pre) with World.only-valid-replies before mem-pre ppost-eq
                ... | cpost , ceq , cpq , cn =
                  cpost
                  , At-from {c} ceq ¬cp cn
                  , subst (λ z → Post.parent cpost ≡ just z) (sym qpp) cpq
                  , (λ z → cn (trans z qpp))
        decide-pp (no ¬qpp) =
          let fq-eq : f q ≡ just qpost
              fq-eq = trans (sym (trans (set-post-other {x = q} ¬qpp)
                                        (set-post-other {x = q} ¬qp))) qeq
              old = World.only-valid-replies before mem fq-eq
          in aux old
          where
            aux : ∃[ cpost ] f c ≡ just cpost
                  ∧ Post.parent cpost ≡ just q ∧ c ≢ q →
                  ∃[ cpost ] At c ≡ just cpost
                  ∧ Post.parent cpost ≡ just q ∧ c ≢ q
            aux (cpost , ceq , cpq , cn) = decide-c (c ≟ₚ pid)
              where
                decide-c :
                  Dec (c ≡ pid) →
                  ∃[ cpost' ] At c ≡ just cpost'
                  ∧ Post.parent cpost' ≡ just q ∧ c ≢ q
                decide-c (yes cp) =
                  ⊥-elim (nothing≢just (trans (sym (f-absent cp)) ceq))
                decide-c (no ¬cp) = decide-pp2 (c ≟ₚ ppid)
                  where
                    decide-pp2 :
                      Dec (c ≡ ppid) →
                      ∃[ cpost' ] At c ≡ just cpost'
                      ∧ Post.parent cpost' ≡ just q ∧ c ≢ q
                    decide-pp2 (yes cpp) =
                      let cpost-eq : cpost ≡ ppost
                          cpost-eq = just-inj
                            (trans (sym (subst (λ z → f z ≡ just cpost) cpp ceq))
                                   ppost-eq)
                          ppq : Post.parent ppost ≡ just q
                          ppq = subst (λ z → Post.parent z ≡ just q) cpost-eq cpq
                      in ppost'
                       , set-post-same-at {f = set-post f pid (just child)}
                                          {pid = ppid} {v = just ppost'}
                                          {x = c} cpp
                       , trans ppost'-parent ppq
                       , cn
                    decide-pp2 (no ¬cpp) =
                      cpost , At-from {c} ceq ¬cp ¬cpp , cpq , cn

reply-uniq-replies :
  (before : World) (pid ppid : PostId) (child ppost ppost' : Post) →
  pid ≢ ppid →
  World.post-at before ppid ≡ just ppost →
  Post.replies child ≡ [] →
  Post.replies ppost' ≡ pid ∷ Post.replies ppost →
  pid ∉ Post.replies ppost →
  {y : PostId} {p : Post} →
  reply-at (World.post-at before) pid child ppid ppost' y ≡ just p →
  uniq (Post.replies p)
reply-uniq-replies before pid ppid child ppost ppost' pid≢ppid pp-eq
                   child-replies ppost'-replies pid∉pre {y} {p} eq =
  decide (y ≟ₚ pid)
  where
    f = World.post-at before
    At = reply-at f pid child ppid ppost'

    uniq-parent : uniq (Post.replies ppost')
    uniq-parent = subst (λ r → uniq r) (sym ppost'-replies)
      (pid∉pre , World.no-duplicate-replies before pp-eq)

    decide : Dec (y ≡ pid) → uniq (Post.replies p)
    decide (yes yp) =
      subst (λ r → uniq (Post.replies r))
            (just-inj (trans (sym (reply-at-child {f = f} {pid = pid}
                                                  {child = child} {ppid = ppid}
                                                  {parent = ppost'} pid≢ppid))
                             (subst (λ z → At z ≡ just p) yp eq)))
            (subst (λ r → uniq r) (sym child-replies) tt)
    decide (no ¬yp) = decide-pp (y ≟ₚ ppid)
      where
        decide-pp : Dec (y ≡ ppid) → uniq (Post.replies p)
        decide-pp (yes ypp) =
          subst (λ r → uniq (Post.replies r))
                (just-inj (trans (sym (reply-at-parent {f = f} {pid = pid}
                                                       {child = child} {ppid = ppid}
                                                       {parent = ppost'}))
                                 (subst (λ z → At z ≡ just p) ypp eq)))
                uniq-parent
        decide-pp (no ¬ypp) =
          World.no-duplicate-replies before
            (trans (sym (reply-at-other {x = y} ¬ypp ¬yp)) eq)

reply-uniq-likes :
  (before : World) (pid ppid : PostId) (child ppost ppost' : Post) →
  pid ≢ ppid →
  World.post-at before ppid ≡ just ppost →
  Post.likes child ≡ [] →
  Post.likes ppost' ≡ Post.likes ppost →
  {y : PostId} {p : Post} →
  reply-at (World.post-at before) pid child ppid ppost' y ≡ just p →
  uniq (Post.likes p)
reply-uniq-likes before pid ppid child ppost ppost' pid≢ppid pp-eq
                 child-likes ppost'-likes {y} {p} eq = decide (y ≟ₚ pid)
  where
    f = World.post-at before
    At = reply-at f pid child ppid ppost'

    uniq-parent : uniq (Post.likes ppost')
    uniq-parent = subst (λ r → uniq r) (sym ppost'-likes)
                        (World.no-duplicate-likes before pp-eq)

    decide : Dec (y ≡ pid) → uniq (Post.likes p)
    decide (yes yp) =
      subst (λ r → uniq (Post.likes r))
            (just-inj (trans (sym (subst (λ z → At z ≡ just child) (sym yp)
                      (reply-at-child {f = f} {pid = pid} {child = child}
                                      {ppid = ppid} {parent = ppost'} pid≢ppid)))
                             eq))
            (subst (λ r → uniq r) (sym child-likes) tt)
    decide (no ¬yp) = decide-pp (y ≟ₚ ppid)
      where
        decide-pp : Dec (y ≡ ppid) → uniq (Post.likes p)
        decide-pp (yes ypp) =
          subst (λ r → uniq (Post.likes r))
                (just-inj (trans (sym (reply-at-parent {f = f} {pid = pid}
                                                       {child = child} {ppid = ppid}
                                                       {parent = ppost'}))
                                 (subst (λ z → At z ≡ just p) ypp eq)))
                uniq-parent
        decide-pp (no ¬ypp) =
          World.no-duplicate-likes before
            (trans (sym (reply-at-other {x = y} ¬ypp ¬yp)) eq)

reply-world :
  (before : World) (pid ppid : PostId) (child ppost ppost' : Post) →
  World.post-at before ppid ≡ just ppost →
  World.post-at before pid ≡ nothing →
  pid ≢ ppid →
  Post.parent child ≡ just ppid →
  Post.parent ppost' ≡ Post.parent ppost →
  Post.replies child ≡ [] →
  Post.likes child ≡ [] →
  Post.replies ppost' ≡ pid ∷ Post.replies ppost →
  Post.likes ppost' ≡ Post.likes ppost →
  World
reply-world before pid ppid child ppost ppost' pp-eq pid-absent pid≢ppid
            child-parent ppost'-parent child-replies child-likes
            ppost'-replies ppost'-likes = record
  { account-at          = World.account-at before
  ; session-at          = World.session-at before
  ; post-at             = reply-at (World.post-at before) pid child ppid ppost'
  ; follows             = World.follows before
  ; newest-first        = pid ∷ World.newest-first before
  ; used-post-ids       = pid ∷ World.used-post-ids before
  ; used-session-ids    = World.used-session-ids before
  ; only-used-pids      = reply-used before pid ppid child ppost' pid≢ppid
                                     (present-used before pp-eq)
  ; only-used-sids      = World.only-used-sids before
  ; only-valid-sessions = World.only-valid-sessions before
  ; only-valid-posts    = reply-valid-posts before pid ppid child ppost' pid≢ppid
                                          (absent∉newest before pid-absent)
  ; only-valid-replies  = reply-replies before pid ppid child ppost ppost' pid≢ppid
                                       pp-eq pid-absent child-parent ppost'-parent
                                       ppost'-replies child-replies
  ; no-duplicate-replies = reply-uniq-replies before pid ppid child ppost ppost'
                                             pid≢ppid pp-eq child-replies
                                             ppost'-replies
                                             (absent∉replies before pid-absent pp-eq)
  ; no-duplicate-likes   = reply-uniq-likes before pid ppid child ppost ppost'
                                           pid≢ppid pp-eq child-likes ppost'-likes
  ; no-duplicate-posts   =
      (absent∉newest before pid-absent , World.no-duplicate-posts before)
  }

--------------------------------------------------------------------------------
-- P6: publish with a parent -- `successful-reply` (Twitter.agda:400-422)
--------------------------------------------------------------------------------

-- A reply to a readable public parent.  `new-reply` (Twitter.agda:213-217) of
-- an `everyone` parent is the author's `new-post`: the account's default
-- visibility.
reply-success-everyone :
  ∀ (before : World) {sid : SessionId} {txt username : String}
    {pid ppid : PostId} {acc : Account}
    {pauthor ptxt : String} {plikes : List String} {preplies : List PostId}
    {pparent : Maybe PostId}
  (vs : ValidSession before sid acc username)
  (can : CanReadPost before sid ppid)
  (pp-eq : World.post-at before ppid ≡
             just (post pauthor ptxt everyone live plikes preplies pparent))
  (pid-absent : World.post-at before pid ≡ nothing)
  (pid≢ppid : pid ≢ ppid) →
  Step before (publish sid txt (just ppid))
       (reply-world before pid ppid
          (new-reply username txt acc ppid
             (post pauthor ptxt everyone live plikes preplies pparent))
          (post pauthor ptxt everyone live plikes preplies pparent)
          (post pauthor ptxt everyone live plikes (pid ∷ preplies) pparent)
          pp-eq pid-absent pid≢ppid refl refl refl refl refl refl)
       (created-post pid)
reply-success-everyone before {sid} {txt} {username} {pid} {ppid} {acc}
  {pauthor} {ptxt} {plikes} {preplies} {pparent}
  vs can pp-eq pid-absent pid≢ppid =
  successful-reply
    {before   = before}
    {after    = reply-world before pid ppid
                  (new-reply username txt acc ppid
                     (post pauthor ptxt everyone live plikes preplies pparent))
                  (post pauthor ptxt everyone live plikes preplies pparent)
                  (post pauthor ptxt everyone live plikes (pid ∷ preplies) pparent)
                  pp-eq pid-absent pid≢ppid refl refl refl refl refl refl}
    {sid      = sid}
    {txt      = txt}
    {username = username}
    {user     = acc}
    {pid      = pid}
    {acc      = acc}
    vs
    (post-is-new pid-absent (reply-at-child pid≢ppid))
    refl
    can
    refl
    refl
    pp-eq
    set-post-same
    pid≢ppid
    (λ {other} {u1} {u2} {s} ¬1 ¬2 →
         sym (reply-at-other (≢-swap ¬2) (≢-swap ¬1)) , refl , refl , refl)

-- A reply to a readable `followers-only` parent.  `new-reply`
-- (Twitter.agda:213-217) overrides the account's default: the reply is
-- `followers-only` even when `acc`'s `default-visibility` is `everyone`.
reply-success-followers-only :
  ∀ (before : World) {sid : SessionId} {txt username : String}
    {pid ppid : PostId} {acc : Account}
    {pauthor ptxt : String} {plikes : List String} {preplies : List PostId}
    {pparent : Maybe PostId}
  (vs : ValidSession before sid acc username)
  (can : CanReadPost before sid ppid)
  (pp-eq : World.post-at before ppid ≡
             just (post pauthor ptxt followers-only live plikes preplies pparent))
  (pid-absent : World.post-at before pid ≡ nothing)
  (pid≢ppid : pid ≢ ppid) →
  Step before (publish sid txt (just ppid))
       (reply-world before pid ppid
          (new-reply username txt acc ppid
             (post pauthor ptxt followers-only live plikes preplies pparent))
          (post pauthor ptxt followers-only live plikes preplies pparent)
          (post pauthor ptxt followers-only live plikes (pid ∷ preplies) pparent)
          pp-eq pid-absent pid≢ppid refl refl refl refl refl refl)
       (created-post pid)
reply-success-followers-only before {sid} {txt} {username} {pid} {ppid} {acc}
  {pauthor} {ptxt} {plikes} {preplies} {pparent}
  vs can pp-eq pid-absent pid≢ppid =
  successful-reply
    {before   = before}
    {after    = reply-world before pid ppid
                  (new-reply username txt acc ppid
                     (post pauthor ptxt followers-only live plikes preplies pparent))
                  (post pauthor ptxt followers-only live plikes preplies pparent)
                  (post pauthor ptxt followers-only live plikes (pid ∷ preplies) pparent)
                  pp-eq pid-absent pid≢ppid refl refl refl refl refl refl}
    {sid      = sid}
    {txt      = txt}
    {username = username}
    {user     = acc}
    {pid      = pid}
    {acc      = acc}
    vs
    (post-is-new pid-absent (reply-at-child pid≢ppid))
    refl
    can
    refl
    refl
    pp-eq
    set-post-same
    pid≢ppid
    (λ {other} {u1} {u2} {s} ¬1 ¬2 →
         sym (reply-at-other (≢-swap ¬2) (≢-swap ¬1)) , refl , refl , refl)

--------------------------------------------------------------------------------
-- P7: failed reply -- `failed-reply` (Twitter.agda:424-430)
--
-- `¬ CanReadPost` mirrors the negative branches of `can-read-post`
-- (Twitter.agda:285-340).
--------------------------------------------------------------------------------

can-read-absent :
  (before : World) (sid : SessionId) (pid : PostId) →
  World.post-at before pid ≡ nothing →
  ¬ CanReadPost before sid pid
can-read-absent before sid pid absent
  (post-is-private {acc = a} {user = u} {post = p'} vs r _ _ _) =
  nothing≢just (trans (sym absent) r)
can-read-absent before sid pid absent
  (post-is-public {acc = a} {user = u} {post = p'} vs r _ _) =
  nothing≢just (trans (sym absent) r)

live≢deleted : live ≢ deleted
live≢deleted = λ ()

everyone≢followers-only : everyone ≢ followers-only
everyone≢followers-only = λ ()

false≢true : false ≢ true
false≢true = λ ()

status≠ : ∀ {z} → Post.status z ≡ live → Post.status z ≡ deleted → ⊥
status≠ {z} alive del = live≢deleted (trans (sym alive) del)

can-read-deleted :
  (before : World) (sid : SessionId) (pid : PostId) {pst : Post} →
  World.post-at before pid ≡ just pst →
  Post.status pst ≡ deleted →
  ¬ CanReadPost before sid pid
can-read-deleted before sid pid {pst} peq del
  (post-is-private {acc = a} {user = u} {post = p'} vs r _ s _) =
  status≠ {z = pst} (subst (λ z → Post.status z ≡ live)
                           (just-inj (trans (sym r) peq)) s) del
can-read-deleted before sid pid {pst} peq del
  (post-is-public {acc = a} {user = u} {post = p'} vs r _ s) =
  status≠ {z = pst} (subst (λ z → Post.status z ≡ live)
                           (just-inj (trans (sym r) peq)) s) del

can-read-private :
  (before : World) (sid : SessionId) (pid : PostId) {pst : Post}
  {acc : Account} {user : String} →
  ValidSession before sid acc user →
  World.post-at before pid ≡ just pst →
  Post.visibility pst ≡ followers-only →
  World.follows before user (Post.author pst) ≡ false →
  ¬ CanReadPost before sid pid
can-read-private before sid pid {pst} {acc} {user} vs peq vis nf
  (post-is-public {post = p'} vs' r v _) =
  everyone≢followers-only (trans (sym (subst (λ z → Post.visibility z ≡ everyone)
                                             (just-inj (trans (sym r) peq)) v)) vis)
can-read-private before sid pid {pst} {acc} {user} vs peq vis nf
  (post-is-private {acc = acc'} {user = u'} {post = p'} vs' r _ _ f) =
  false≢true (trans (sym nf) f-user)
  where
    e : p' ≡ pst
    e = just-inj (trans (sym r) peq)

    u-eq : user ≡ u'
    u-eq = active-inj (trans (sym (ValidSession.session-unchanged vs))
                             (ValidSession.session-unchanged vs'))

    f-user : World.follows before user (Post.author pst) ≡ true
    f-user = subst (λ z → World.follows before user z ≡ true)
                   (cong Post.author e)
                   (subst (λ z → World.follows before z (Post.author p') ≡ true)
                          (sym u-eq) f)

reply-denied-absent :
  ∀ (before : World) {sid : SessionId} {txt : String} {ppid : PostId}
    {acc : Account} {user : String} →
  ValidSession before sid acc user →
  World.post-at before ppid ≡ nothing →
  Step before (publish sid txt (just ppid)) before denied
reply-denied-absent before {sid} {txt} {ppid} vs absent =
  failed-reply {before = before} {sid = sid} {txt = txt} {ppid = ppid}
               vs (can-read-absent before sid ppid absent)

reply-denied-deleted :
  ∀ (before : World) {sid : SessionId} {txt : String} {ppid : PostId}
    {pst : Post} {acc : Account} {user : String} →
  ValidSession before sid acc user →
  World.post-at before ppid ≡ just pst →
  Post.status pst ≡ deleted →
  Step before (publish sid txt (just ppid)) before denied
reply-denied-deleted before {sid} {txt} {ppid} {pst} vs peq del =
  failed-reply {before = before} {sid = sid} {txt = txt} {ppid = ppid}
               vs (can-read-deleted before sid ppid peq del)

reply-denied-private :
  ∀ (before : World) {sid : SessionId} {txt : String} {ppid : PostId}
    {pst : Post} {acc : Account} {user : String} →
  ValidSession before sid acc user →
  World.post-at before ppid ≡ just pst →
  Post.visibility pst ≡ followers-only →
  World.follows before user (Post.author pst) ≡ false →
  Step before (publish sid txt (just ppid)) before denied
reply-denied-private before {sid} {txt} {ppid} {pst} vs peq vis nf =
  failed-reply {before = before} {sid = sid} {txt = txt} {ppid = ppid}
               vs (can-read-private before sid ppid vs peq vis nf)

--------------------------------------------------------------------------------
-- `delete-world`: `pid`'s post becomes `pst'`, a post that keeps every field of
-- `pst` except the ones the caller changes (in practice only `status`).
--
-- Nothing else in the post map moves, so `only-used-pids` only needs to know
-- that `pid` was already used; the other invariants reuse the old ones, with a
-- case split on whether the looked-up pid is the one that changed.
--------------------------------------------------------------------------------

deleted-post : Post → Post
deleted-post (post a t v _ l r pa) = post a t v deleted l r pa

delete-used :
  (before : World) (pid : PostId) (pst' : Post) →
  pid ∈ World.used-post-ids before →
  {x : PostId} →
  (x ∈ World.used-post-ids before →
     set-post (World.post-at before) pid (just pst') x ≢ nothing)
  ∧ (x ∉ World.used-post-ids before →
     set-post (World.post-at before) pid (just pst') x ≡ nothing)
delete-used before pid pst' pid-in {x} = in-part , out-part
  where
    f = World.post-at before

    in-part : x ∈ World.used-post-ids before →
              set-post f pid (just pst') x ≢ nothing
    in-part mem = decide (x ≟ₚ pid)
      where
        decide : Dec (x ≡ pid) → set-post f pid (just pst') x ≢ nothing
        decide (yes p) =
          λ eq → just≢nothing (trans (sym (set-post-same-at {x = x} p)) eq)
        decide (no ¬p) =
          λ eq → proj₁ (World.only-used-pids before) mem
            (trans (sym (set-post-other {x = x} ¬p)) eq)

    out-part : x ∉ World.used-post-ids before →
               set-post f pid (just pst') x ≡ nothing
    out-part ¬mem =
      trans (set-post-other {x = x} (∈-not-eq ¬mem pid-in))
            (proj₂ (World.only-used-pids before) ¬mem)

delete-valid-posts :
  (before : World) (pid : PostId) (pst' : Post) →
  {y : PostId} →
  y ∈ World.newest-first before →
  ∃[ qq ] set-post (World.post-at before) pid (just pst') y ≡ just qq
delete-valid-posts before pid pst' {y} mem
  with World.only-valid-posts before mem
... | qq , peq = decide (y ≟ₚ pid)
  where
    f = World.post-at before

    decide : Dec (y ≡ pid) → ∃[ qq' ] set-post f pid (just pst') y ≡ just qq'
    decide (yes p) = pst' , set-post-same-at {x = y} p
    decide (no ¬p) = qq , trans (set-post-other {x = y} ¬p) peq

delete-replies :
  (before : World) (pid : PostId) (pst pst' : Post) →
  World.post-at before pid ≡ just pst →
  Post.replies pst' ≡ Post.replies pst →
  Post.parent pst' ≡ Post.parent pst →
  {child parent-pid : PostId} {parent-post : Post} →
  child ∈ Post.replies parent-post →
  set-post (World.post-at before) pid (just pst') parent-pid ≡ just parent-post →
  ∃[ cpost ]
    set-post (World.post-at before) pid (just pst') child ≡ just cpost
    ∧ Post.parent cpost ≡ just parent-pid
    ∧ child ≢ parent-pid
delete-replies before pid pst pst' peq replies-eq parent-eq
              {child} {parent-pid} {parent-post} mem peq' =
  decide-parent (parent-pid ≟ₚ pid)
  where
    f = World.post-at before
    At = set-post f pid (just pst')

    decide-parent :
      Dec (parent-pid ≡ pid) →
      ∃[ cpost ] At child ≡ just cpost
      ∧ Post.parent cpost ≡ just parent-pid ∧ child ≢ parent-pid
    decide-parent (yes p) =
      let parent-eq' : pst' ≡ parent-post
          parent-eq' = just-inj
            (trans (sym (set-post-same-at {x = parent-pid} p)) peq')
          mem-pst' : child ∈ Post.replies pst'
          mem-pst' = subst (λ r → child ∈ Post.replies r) (sym parent-eq') mem
          mem-pst : child ∈ Post.replies pst
          mem-pst = subst (λ r → child ∈ r) replies-eq mem-pst'
          old = World.only-valid-replies before mem-pst peq
      in aux old
      where
        aux : ∃[ cpost ] f child ≡ just cpost
              ∧ Post.parent cpost ≡ just pid ∧ child ≢ pid →
              ∃[ cpost ] At child ≡ just cpost
              ∧ Post.parent cpost ≡ just parent-pid ∧ child ≢ parent-pid
        aux (cpost , ceq , cp , cn) = decide-child (child ≟ₚ pid)
          where
            decide-child :
              Dec (child ≡ pid) →
              ∃[ cpost' ] At child ≡ just cpost'
              ∧ Post.parent cpost' ≡ just parent-pid ∧ child ≢ parent-pid
            decide-child (yes q) = ⊥-elim (cn q)
            decide-child (no ¬q) =
              cpost
              , trans (set-post-other {x = child} ¬q) ceq
              , subst (λ z → Post.parent cpost ≡ just z) (sym p) cp
              , (λ z → cn (trans z p))
    decide-parent (no ¬p) =
      let before-eq : f parent-pid ≡ just parent-post
          before-eq = trans (sym (set-post-other {x = parent-pid} ¬p)) peq'
          old = World.only-valid-replies before mem before-eq
      in aux old
      where
        aux : ∃[ cpost ] f child ≡ just cpost
              ∧ Post.parent cpost ≡ just parent-pid ∧ child ≢ parent-pid →
              ∃[ cpost ] At child ≡ just cpost
              ∧ Post.parent cpost ≡ just parent-pid ∧ child ≢ parent-pid
        aux (cpost , ceq , cp , cn) = decide-child (child ≟ₚ pid)
          where
            decide-child :
              Dec (child ≡ pid) →
              ∃[ cpost' ] At child ≡ just cpost'
              ∧ Post.parent cpost' ≡ just parent-pid ∧ child ≢ parent-pid
            decide-child (yes q) =
              let ceq-pid : f pid ≡ just cpost
                  ceq-pid = subst (λ z → f z ≡ just cpost) q ceq
                  pst≡cpost : pst ≡ cpost
                  pst≡cpost = just-inj (trans (sym peq) ceq-pid)
                  pp : Post.parent pst ≡ just parent-pid
                  pp = subst (λ z → Post.parent z ≡ just parent-pid)
                             (sym pst≡cpost) cp
              in pst'
               , set-post-same-at {x = child} q
               , trans parent-eq pp
               , (λ z → ¬p (trans (sym z) q))
            decide-child (no ¬q) =
              cpost , trans (set-post-other {x = child} ¬q) ceq , cp , cn

delete-uniq-replies :
  (before : World) (pid : PostId) (pst pst' : Post) →
  World.post-at before pid ≡ just pst →
  Post.replies pst' ≡ Post.replies pst →
  {y : PostId} {z : Post} →
  set-post (World.post-at before) pid (just pst') y ≡ just z →
  uniq (Post.replies z)
delete-uniq-replies before pid pst pst' peq replies-eq {y} {z} eq =
  decide (y ≟ₚ pid)
  where
    f = World.post-at before

    decide : Dec (y ≡ pid) → uniq (Post.replies z)
    decide (yes p) =
      subst (λ r → uniq (Post.replies r))
            (just-inj (trans (sym (set-post-same-at {x = y} p)) eq))
            (subst (λ r → uniq r) (sym replies-eq)
                   (World.no-duplicate-replies before peq))
    decide (no ¬p) =
      World.no-duplicate-replies before
        (trans (sym (set-post-other {x = y} ¬p)) eq)

delete-uniq-likes :
  (before : World) (pid : PostId) (pst pst' : Post) →
  World.post-at before pid ≡ just pst →
  Post.likes pst' ≡ Post.likes pst →
  {y : PostId} {z : Post} →
  set-post (World.post-at before) pid (just pst') y ≡ just z →
  uniq (Post.likes z)
delete-uniq-likes before pid pst pst' peq likes-eq {y} {z} eq =
  decide (y ≟ₚ pid)
  where
    f = World.post-at before

    decide : Dec (y ≡ pid) → uniq (Post.likes z)
    decide (yes p) =
      subst (λ r → uniq (Post.likes r))
            (just-inj (trans (sym (set-post-same-at {x = y} p)) eq))
            (subst (λ r → uniq r) (sym likes-eq)
                   (World.no-duplicate-likes before peq))
    decide (no ¬p) =
      World.no-duplicate-likes before
        (trans (sym (set-post-other {x = y} ¬p)) eq)

delete-world :
  (before : World) (pid : PostId) (pst pst' : Post) →
  World.post-at before pid ≡ just pst →
  Post.replies pst' ≡ Post.replies pst →
  Post.likes pst' ≡ Post.likes pst →
  Post.parent pst' ≡ Post.parent pst →
  World
delete-world before pid pst pst' peq replies-eq likes-eq parent-eq = record
  { account-at          = World.account-at before
  ; session-at          = World.session-at before
  ; post-at             = set-post (World.post-at before) pid (just pst')
  ; follows             = World.follows before
  ; newest-first        = World.newest-first before
  ; used-post-ids       = World.used-post-ids before
  ; used-session-ids    = World.used-session-ids before
  ; only-used-pids      = delete-used before pid pst' (present-used before peq)
  ; only-used-sids      = World.only-used-sids before
  ; only-valid-sessions = World.only-valid-sessions before
  ; only-valid-posts    = delete-valid-posts before pid pst'
  ; only-valid-replies  = delete-replies before pid pst pst' peq replies-eq
                                       parent-eq
  ; no-duplicate-replies = delete-uniq-replies before pid pst pst' peq replies-eq
  ; no-duplicate-likes   = delete-uniq-likes before pid pst pst' peq likes-eq
  ; no-duplicate-posts   = World.no-duplicate-posts before
  }

--------------------------------------------------------------------------------
-- P8: delete -- `delete-post` (Twitter.agda:432-449) and its failures.
--------------------------------------------------------------------------------

-- A post authored by the session's user becomes `deleted`; every other field of
-- the post and of the world is untouched.  There is no `live` premise, which
-- `delete-idempotent` exercises.
delete-success :
  ∀ (before : World) {sid : SessionId} {pid : PostId}
    {acc : Account} {user : String} {pst : Post}
  (vs : ValidSession before sid acc user)
  (peq : World.post-at before pid ≡ just pst)
  (author-eq : Post.author pst ≡ user) →
  Step before (delete sid pid)
       (delete-world before pid pst (deleted-post pst) peq refl refl refl)
       success
delete-success before {sid} {pid} {acc} {user} {pst} vs peq author-eq =
  delete-post
    {before = before}
    {after  = delete-world before pid pst (deleted-post pst) peq refl refl refl}
    {pid    = pid}
    {sid    = sid}
    {acc    = acc}
    {user   = user}
    {post   = pst}
    {post'  = deleted-post pst}
    vs
    peq
    set-post-same
    author-eq
    refl
    refl
    refl
    refl
    refl
    (λ {other} ¬e → sym (set-post-other (≢-swap ¬e)) , refl , refl , refl)

-- The same rule applied to a post that is already `deleted`: its row stays as
-- it was (the world it produces holds `pst` itself at `pid`), and the answer is
-- still `success`.
delete-idempotent :
  ∀ (before : World) {sid : SessionId} {pid : PostId}
    {acc : Account} {user : String} {pst : Post}
  (vs : ValidSession before sid acc user)
  (peq : World.post-at before pid ≡ just pst)
  (author-eq : Post.author pst ≡ user)
  (already : Post.status pst ≡ deleted) →
  Step before (delete sid pid)
       (delete-world before pid pst pst peq refl refl refl)
       success
delete-idempotent before {sid} {pid} {acc} {user} {pst} vs peq author-eq already =
  delete-post
    {before = before}
    {after  = delete-world before pid pst pst peq refl refl refl}
    {pid    = pid}
    {sid    = sid}
    {acc    = acc}
    {user   = user}
    {post   = pst}
    {post'  = pst}
    vs
    peq
    set-post-same
    author-eq
    refl
    refl
    refl
    refl
    already
    (λ {other} ¬e → sym (set-post-other (≢-swap ¬e)) , refl , refl , refl)

delete-denied-absent :
  ∀ (before : World) {sid : SessionId} {pid : PostId}
    {acc : Account} {user : String} →
  ValidSession before sid acc user →
  World.post-at before pid ≡ nothing →
  Step before (delete sid pid) before denied
delete-denied-absent before vs absent =
  failed-delete-non-existant-post vs absent

delete-denied-not-author :
  ∀ (before : World) {sid : SessionId} {pid : PostId}
    {acc : Account} {user : String} {pst : Post} →
  ValidSession before sid acc user →
  World.post-at before pid ≡ just pst →
  Post.author pst ≢ user →
  Step before (delete sid pid) before denied
delete-denied-not-author before vs peq ne =
  failed-delete-not-author vs peq ne

--------------------------------------------------------------------------------
-- P9: read-post with a session (Twitter.agda:518-548)
--------------------------------------------------------------------------------

-- `read-post-logged-in`, stated for an arbitrary `CanReadPost` witness.
read-logged-in :
  ∀ (before : World) {sid : SessionId} {pid : PostId}
    {pst : Post} {author txt : String} {likes : Nat} {replies : List PostId} →
  CanReadPost before sid pid →
  World.post-at before pid ≡ just pst →
  Post.author pst ≡ author →
  Post.text pst ≡ txt →
  length (Post.likes pst) ≡ likes →
  Post.replies pst ≡ replies →
  Step before (read-post (just sid) pid) before
       (returned-post author txt likes replies)
read-logged-in before {sid} {pid} {pst} can peq =
  read-post-logged-in {post = pst} can peq

-- The `post-is-public` instance of `CanReadPost` (Twitter.agda:171-179).
read-logged-in-public :
  ∀ (before : World) {sid : SessionId} {pid : PostId}
    {acc : Account} {user : String} {pst : Post}
    {author txt : String} {likes : Nat} {replies : List PostId} →
  ValidSession before sid acc user →
  World.post-at before pid ≡ just pst →
  Post.visibility pst ≡ everyone →
  Post.status pst ≡ live →
  Post.author pst ≡ author →
  Post.text pst ≡ txt →
  length (Post.likes pst) ≡ likes →
  Post.replies pst ≡ replies →
  Step before (read-post (just sid) pid) before
       (returned-post author txt likes replies)
read-logged-in-public before {sid} {pid} {pst} vs peq vis st =
  read-logged-in before (post-is-public vs peq vis st) peq

-- The `post-is-private` instance of `CanReadPost` (Twitter.agda:161-170).
read-logged-in-private :
  ∀ (before : World) {sid : SessionId} {pid : PostId}
    {acc : Account} {user : String} {pst : Post}
    {author txt : String} {likes : Nat} {replies : List PostId} →
  ValidSession before sid acc user →
  World.post-at before pid ≡ just pst →
  Post.visibility pst ≡ followers-only →
  Post.status pst ≡ live →
  World.follows before user (Post.author pst) ≡ true →
  Post.author pst ≡ author →
  Post.text pst ≡ txt →
  length (Post.likes pst) ≡ likes →
  Post.replies pst ≡ replies →
  Step before (read-post (just sid) pid) before
       (returned-post author txt likes replies)
read-logged-in-private before {sid} {pid} {pst} vs peq vis st follow-eq =
  read-logged-in before (post-is-private vs peq vis st follow-eq) peq

read-denied-absent :
  ∀ (before : World) {sid : SessionId} {pid : PostId}
    {acc : Account} {user : String} →
  ValidSession before sid acc user →
  World.post-at before pid ≡ nothing →
  Step before (read-post (just sid) pid) before denied
read-denied-absent before vs absent = cant-read-post-public vs absent

read-denied-deleted :
  ∀ (before : World) {sid : SessionId} {pid : PostId}
    {acc : Account} {user : String} {pst : Post} →
  ValidSession before sid acc user →
  World.post-at before pid ≡ just pst →
  Post.status pst ≡ deleted →
  Step before (read-post (just sid) pid) before denied
read-denied-deleted before vs peq del =
  cant-read-post-private-deleted vs peq del

read-denied-private :
  ∀ (before : World) {sid : SessionId} {pid : PostId}
    {acc : Account} {user : String} {pst : Post} →
  ValidSession before sid acc user →
  World.post-at before pid ≡ just pst →
  Post.visibility pst ≡ followers-only →
  World.follows before user (Post.author pst) ≡ false →
  Step before (read-post (just sid) pid) before denied
read-denied-private before {pst = pst} vs peq vis nf =
  cant-read-post-private {author = Post.author pst} vs peq vis refl nf

--------------------------------------------------------------------------------
-- P10: read-post anonymously (Twitter.agda:550-554)
--
-- A readable post is `read-post-anonymously`. An unreadable one is
-- `failed-access` (Twitter.agda:464-468) applied VACUOUSLY:
-- `extract-sid (read-post nothing pid) = nothing` (Twitter.agda:196), and a
-- `nothing` can never be a `just sid`, so the premise of `failed-access`
-- ("every non-`nothing` extracted session is invalid") holds trivially. Hence
-- an anonymous read of an absent, `followers-only` or deleted post is
-- `expired` in EVERY world -- not `denied`. Tested by
-- `anonymous_reads_of_unreadable_posts_expire` in `tests/engine_posts.rs`.
--------------------------------------------------------------------------------

read-anonymous :
  ∀ (before : World) {pid : PostId} {pst : Post} →
  World.post-at before pid ≡ just pst →
  Post.visibility pst ≡ everyone →
  Post.status pst ≡ live →
  Step before (read-post nothing pid) before (return-post pst)
read-anonymous before peq vis st = read-post-anonymously peq vis st

-- The unreadable case: `failed-access` fires vacuously, whatever the world.
read-anonymous-expired :
  ∀ (before : World) (pid : PostId) →
  Step before (read-post nothing pid) before expired
read-anonymous-expired before pid =
  failed-access (λ {sid} eq → ⊥-elim (nothing≢just eq))

--------------------------------------------------------------------------------
-- P11: failed-access for the post commands (Twitter.agda:464-468)
--------------------------------------------------------------------------------

publish-expired :
  ∀ (before : World) {sid : SessionId} {txt : String} {ppid : Maybe PostId} →
  (∀ {user} → World.session-at before sid ≡ active user → ⊥) →
  Step before (publish sid txt ppid) before expired
publish-expired before {sid} {txt} {ppid} ¬act =
  failed-access-inactive before (publish sid txt ppid) sid refl ¬act

delete-expired :
  ∀ (before : World) {sid : SessionId} {pid : PostId} →
  (∀ {user} → World.session-at before sid ≡ active user → ⊥) →
  Step before (delete sid pid) before expired
delete-expired before {sid} {pid} ¬act =
  failed-access-inactive before (delete sid pid) sid refl ¬act

read-expired :
  ∀ (before : World) {sid : SessionId} {pid : PostId} →
  (∀ {user} → World.session-at before sid ≡ active user → ⊥) →
  Step before (read-post (just sid) pid) before expired
read-expired before {sid} {pid} ¬act =
  failed-access-inactive before (read-post (just sid) pid) sid refl ¬act
