open import Agda.Builtin.Maybe
open import Data.Empty                            using (⊥; ⊥-elim)
open import Data.List                             using (List; []; _∷_)
open import Data.Product                          using (_,_; proj₁; proj₂; ∃-syntax)
open import Data.String                           using (String; _≟_)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
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
