open import Agda.Builtin.Bool                     using (Bool; true; false)
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat                      using (Nat)
open import Data.Empty                            using (⊥; ⊥-elim)
open import Data.List                             using (List; []; _∷_; length;
                                                         take; filter; filterᵇ)
open import Data.Product                          using (_,_; proj₁; proj₂; ∃-syntax)
open import Data.String                           using (String; _≟_)
open import Function                              using (_∘_)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Data.Unit                             using (⊤; tt)
open import Relation.Binary.Definitions           using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym;
                                                         subst; trans)
open import Relation.Nullary.Decidable.Core        using (Dec; yes; no; does)
open import Relation.Unary                        using (Pred; Decidable)
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
-- P15: time-passes (Twitter.agda:124) and the `session-timeout` Step (691-702)
--
-- `time-passes` has no session argument: instead of expiring one request it
-- applies `logout`-like revocation to EVERY session at once.  Its Step says
-- every session that was `active` is `revoked` afterwards and that nothing
-- else -- no account, no post, no follow, no timeline -- moves.  The engine
-- performs it as one `UPDATE sessions SET status = 'revoked' WHERE status =
-- 'active'`, so the after-world is `before` with `session-at` mapped through
-- `timed-out`, and every other component copied.
--
-- `timed-out-world` therefore only has to re-discharge the two invariants
-- that speak about the session table: `only-used-sids` (Twitter.agda:82-86)
-- holds because `timed-out` maps `unused` to `unused`, and
-- `only-valid-sessions` (Twitter.agda:87-91) holds vacuously because
-- `timed-out` never produces `active`.  `only-used-pids`, `only-valid-posts`,
-- `only-valid-replies` and the three `no-duplicate-*` invariants are copied
-- from `before`.
--------------------------------------------------------------------------------

-- The whole effect of `time-passes` on a single session: an `active` session
-- times out, a session that is already `unused` or `revoked` is left alone.
timed-out : SessionStatus → SessionStatus
timed-out unused     = unused
timed-out (active _) = revoked
timed-out revoked    = revoked

-- The "in" half of `only-used-sids` after the timeout: a used session is
-- still not `unused`, because `timed-out` maps `unused` to `unused` only.
timed-out-never-unused :
  ∀ (st : SessionStatus) → st ≢ unused → timed-out st ≢ unused
timed-out-never-unused unused     ¬unused = ⊥-elim (¬unused refl)
timed-out-never-unused (active _) _       = revoked≢unused
timed-out-never-unused revoked    _       = revoked≢unused

-- `only-valid-sessions` is vacuous afterwards: `timed-out` never answers
-- `active`, so the invariant has no witness to discharge.
timed-out-never-active :
  ∀ (st : SessionStatus) {u : String} → timed-out st ≢ active u
timed-out-never-active unused     = unused≢active
timed-out-never-active (active _) = revoked≢active
timed-out-never-active revoked    = revoked≢active

timed-out-used :
  (before : World) {s : SessionId} →
  (s ∈ World.used-session-ids before →
     timed-out (World.session-at before s) ≢ unused)
  ∧ (s ∉ World.used-session-ids before →
     timed-out (World.session-at before s) ≡ unused)
timed-out-used before {s} = in-part , out-part
  where
    sess = World.session-at before

    in-part : s ∈ World.used-session-ids before → timed-out (sess s) ≢ unused
    in-part mem =
      timed-out-never-unused (sess s) (proj₁ (World.only-used-sids before) mem)

    out-part : s ∉ World.used-session-ids before → timed-out (sess s) ≡ unused
    out-part ¬mem = cong timed-out (proj₂ (World.only-used-sids before) ¬mem)

timed-out-valid :
  (before : World) {s : SessionId} {u : String} →
  timed-out (World.session-at before s) ≡ active u →
  ∃[ a ] World.account-at before u ≡ just a
timed-out-valid before {s} {u} eq =
  ⊥-elim (timed-out-never-active (World.session-at before s) eq)

timed-out-world : (before : World) → World
timed-out-world before = record
  { account-at          = World.account-at before
  ; session-at          = λ sid → timed-out (World.session-at before sid)
  ; post-at             = World.post-at before
  ; follows             = World.follows before
  ; newest-first        = World.newest-first before
  ; used-post-ids       = World.used-post-ids before
  ; used-session-ids    = World.used-session-ids before
  ; only-used-pids      = World.only-used-pids before
  ; only-used-sids      = timed-out-used before
  ; only-valid-sessions = timed-out-valid before
  ; only-valid-posts    = World.only-valid-posts before
  ; only-valid-replies  = World.only-valid-replies before
  ; no-duplicate-replies = World.no-duplicate-replies before
  ; no-duplicate-likes   = World.no-duplicate-likes before
  ; no-duplicate-posts   = World.no-duplicate-posts before
  }

-- `session-timeout`: on an arbitrary world, every active session becomes
-- revoked -- `cong timed-out` at each such session, since `timed-out (active
-- user)` is `revoked` by definition -- and every other component is copied,
-- which is why the "everything else unchanged" premise is `refl`.
time-passes-success :
  ∀ (before : World) →
  Step before time-passes (timed-out-world before) success
time-passes-success before = session-timeout
  {before = before}
  {after  = timed-out-world before}
  (λ {sid} {user} eq → cong timed-out eq)
  (λ {sid} _ _ _ _ → refl)

-- A second `time-passes` answers `success` again and changes nothing: the
-- world after one timeout is already a fixed point of `timed-out`, and no
-- session is `active` any more, so the first premise of `session-timeout` is
-- vacuous (`timed-out-never-active`).
time-passes-idempotent :
  ∀ (before : World) →
  Step (timed-out-world before) time-passes (timed-out-world before) success
time-passes-idempotent before = session-timeout
  {before = timed-out-world before}
  {after  = timed-out-world before}
  (λ {sid} {user} eq →
       ⊥-elim (timed-out-never-active (World.session-at before sid) eq))
  (λ {sid} _ _ _ _ → refl)

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

--------------------------------------------------------------------------------
-- P12: follow / unfollow (Twitter.agda:655-675)
--
-- `follow-user` and `unfollow-user` change the follow table and nothing else.
-- No `World` invariant (Twitter.agda:64-116) mentions `follows`, so every
-- obligation of `follows-world` / `unfollows-world` is copied from `before`.
-- Neither rule looks the followee up: following an account that does not exist
-- is `success` (there is no failure rule), so `followee` is an arbitrary
-- `String`.
--------------------------------------------------------------------------------

follows-world : (before : World) (follower followee : String) → World
follows-world before follower followee = record
  { account-at          = World.account-at before
  ; session-at          = World.session-at before
  ; post-at             = World.post-at before
  ; follows             = add-follower (World.follows before) follower followee
  ; newest-first        = World.newest-first before
  ; used-post-ids       = World.used-post-ids before
  ; used-session-ids    = World.used-session-ids before
  ; only-used-pids      = World.only-used-pids before
  ; only-used-sids      = World.only-used-sids before
  ; only-valid-sessions = World.only-valid-sessions before
  ; only-valid-posts    = World.only-valid-posts before
  ; only-valid-replies  = World.only-valid-replies before
  ; no-duplicate-replies = World.no-duplicate-replies before
  ; no-duplicate-likes   = World.no-duplicate-likes before
  ; no-duplicate-posts   = World.no-duplicate-posts before
  }

-- `follow-user` (Twitter.agda:655-664): the session must be valid, the
-- follower is its user, and the only change is `add-follower`.
follow-success :
  ∀ (before : World) {sid : SessionId} {acc : Account}
    {follower followee : String} →
  ValidSession before sid acc follower →
  Step before (follow sid followee)
       (follows-world before follower followee) success
follow-success before {sid} {acc} {follower} {followee} vs =
  follow-user
    {before   = before}
    {after    = follows-world before follower followee}
    {sid      = sid}
    {acc      = acc}
    {follower = follower}
    {followee = followee}
    vs
    refl
    refl
    refl
    refl
    refl

unfollows-world : (before : World) (follower followee : String) → World
unfollows-world before follower followee = record
  { account-at          = World.account-at before
  ; session-at          = World.session-at before
  ; post-at             = World.post-at before
  ; follows             = remove-follower (World.follows before) follower followee
  ; newest-first        = World.newest-first before
  ; used-post-ids       = World.used-post-ids before
  ; used-session-ids    = World.used-session-ids before
  ; only-used-pids      = World.only-used-pids before
  ; only-used-sids      = World.only-used-sids before
  ; only-valid-sessions = World.only-valid-sessions before
  ; only-valid-posts    = World.only-valid-posts before
  ; only-valid-replies  = World.only-valid-replies before
  ; no-duplicate-replies = World.no-duplicate-replies before
  ; no-duplicate-likes   = World.no-duplicate-likes before
  ; no-duplicate-posts   = World.no-duplicate-posts before
  }

-- `unfollow-user` (Twitter.agda:666-675).  There is no precondition that the
-- pair was followed, which is why a repeated `unfollow` is still `success`.
unfollow-success :
  ∀ (before : World) {sid : SessionId} {acc : Account}
    {follower followee : String} →
  ValidSession before sid acc follower →
  Step before (unfollow sid followee)
       (unfollows-world before follower followee) success
unfollow-success before {sid} {acc} {follower} {followee} vs =
  unfollow-user
    {before   = before}
    {after    = unfollows-world before follower followee}
    {sid      = sid}
    {acc      = acc}
    {follower = follower}
    {followee = followee}
    vs
    refl
    refl
    refl
    refl
    refl

--------------------------------------------------------------------------------
-- P13: like / unlike (Twitter.agda:574-653)
--
-- `like-post` requires that `user` be a member of the AFTER like list and that
-- the membership of every OTHER user be unchanged (Twitter.agda:601-604);
-- `unlike-post` requires the mirror image, with `user` absent from the AFTER
-- list (Twitter.agda:621-647).  `like-add` / `like-remove` are exactly those
-- two list operations, and the bundle below shows that each satisfies its
-- half -- and that both keep the list duplicate-free, which is what
-- `no-duplicate-likes` (Twitter.agda:110-113) needs.
--------------------------------------------------------------------------------

-- `user` is consed only when absent, so a repeated like changes nothing.
--
-- The `Dec` of the head element is passed to a separate `like-add-cons`, so
-- that the case tree of the step splits on a *variable*, not on the value of
-- `_≟_` (whose reduction on two variables is stuck).  Each lemma below then
-- matches on that variable, which is why the two branches are trivially
-- available.
mutual
  like-add : List String → String → List String
  like-add []       user = user ∷ []
  like-add (x ∷ xs) user = like-add-cons x xs user (x ≟ user)

  like-add-cons : (x : String) (xs : List String) (user : String)
                  → Dec (x ≡ user) → List String
  like-add-cons x xs user (yes _) = x ∷ xs
  like-add-cons x xs user (no  _) = x ∷ like-add xs user

-- Every occurrence of `user` is deleted, so a repeated unlike changes nothing.
mutual
  like-remove : List String → String → List String
  like-remove []       user = []
  like-remove (x ∷ xs) user = like-remove-cons x xs user (x ≟ user)

  like-remove-cons : (x : String) (xs : List String) (user : String)
                     → Dec (x ≡ user) → List String
  like-remove-cons x xs user (yes _) = like-remove xs user
  like-remove-cons x xs user (no  _) = x ∷ like-remove xs user

infix 3 _⇔_
_⇔_ : Set → Set → Set
_⇔_ a b = (a → b) ∧ (b → a)

-- Absence from a cons, from absence of the head and of the tail.
∉-cons : {x y : String} {xs : List String} → x ≢ y → x ∉ xs → x ∉ (y ∷ xs)
∉-cons {x} {y} {xs} ne ¬xs m = aux (∈-cons m)
  where
    aux : (x ≡ y) ⊎ (x ∈ xs) → ⊥
    aux (inj₁ e) = ne e
    aux (inj₂ q) = ¬xs q

like-add-member : (likes : List String) (user : String) → user ∈ like-add likes user
like-add-member []       user = here
like-add-member (x ∷ xs) user = aux (x ≟ user)
  where
    aux : (d : Dec (x ≡ user)) → user ∈ like-add-cons x xs user d
    aux (yes p) = subst (λ z → z ∈ x ∷ xs) p here
    aux (no  _) = there (like-add-member xs user)

-- Every OTHER user keeps its membership status: the per-user premise of
-- `like-post` (Twitter.agda:601-604), in both directions.
like-add-iff :
  (likes : List String) (user u : String) → user ≢ u →
  (u ∈ likes) ⇔ (u ∈ like-add likes user)
like-add-iff [] user u ne = (λ ()) , (λ m → ⊥-elim (aux (∈-cons m)))
  where
    aux : (u ≡ user) ⊎ (u ∈ []) → ⊥
    aux (inj₁ e) = ne (sym e)
    aux (inj₂ ())
like-add-iff (x ∷ xs) user u ne = aux (x ≟ user)
  where
    ih = like-add-iff xs user u ne

    aux : (d : Dec (x ≡ user)) →
          (u ∈ x ∷ xs) ⇔ (u ∈ like-add-cons x xs user d)
    aux (yes _) = (λ m → m) , (λ m → m)
    aux (no ¬q) = fwd , bwd
      where
        fwd : u ∈ (x ∷ xs) → u ∈ (x ∷ like-add xs user)
        fwd m = step (∈-cons m)
          where
            step : (u ≡ x) ⊎ (u ∈ xs) → u ∈ (x ∷ like-add xs user)
            step (inj₁ e) =
              subst (λ z → z ∈ (x ∷ like-add xs user)) (sym e) here
            step (inj₂ q) = there (proj₁ ih q)

        bwd : u ∈ (x ∷ like-add xs user) → u ∈ (x ∷ xs)
        bwd m = step (∈-cons m)
          where
            step : (u ≡ x) ⊎ (u ∈ like-add xs user) → u ∈ (x ∷ xs)
            step (inj₁ e) = subst (λ z → z ∈ (x ∷ xs)) (sym e) here
            step (inj₂ q) = there (proj₂ ih q)

like-add-others :
  (likes : List String) (user u : String) → user ≢ u →
  (u ∈ likes → u ∈ like-add likes user)
  ∧ (u ∉ likes → u ∉ like-add likes user)
like-add-others likes user u ne =
    proj₁ (like-add-iff likes user u ne)
  , (λ ¬mem mem → ¬mem (proj₂ (like-add-iff likes user u ne) mem))

uniq-like-add :
  (likes : List String) (user : String) → uniq likes → uniq (like-add likes user)
uniq-like-add []       user uq = (λ ()) , tt
uniq-like-add (x ∷ xs) user uq = aux (x ≟ user)
  where
    aux : (d : Dec (x ≡ user)) → uniq (like-add-cons x xs user d)
    aux (yes _) = uq
    aux (no ¬q) =
      ( (λ m → proj₁ uq (proj₂ (like-add-iff xs user x (≢-swap ¬q)) m))
      , uniq-like-add xs user (proj₂ uq) )

like-remove-absent :
  (likes : List String) (user : String) → user ∉ like-remove likes user
like-remove-absent []       user = λ ()
like-remove-absent (x ∷ xs) user = aux (x ≟ user)
  where
    aux : (d : Dec (x ≡ user)) → user ∉ like-remove-cons x xs user d
    aux (yes _) = like-remove-absent xs user
    aux (no ¬q) = ∉-cons (≢-swap ¬q) (like-remove-absent xs user)

-- Every OTHER user keeps its membership status.  Stated in the orientation of
-- `unlike-post` (Twitter.agda:628-631), whose `post` is the AFTER post.
like-remove-iff :
  (likes : List String) (user u : String) → user ≢ u →
  (u ∈ likes) ⇔ (u ∈ like-remove likes user)
like-remove-iff [] user u ne = (λ ()) , (λ ())
like-remove-iff (x ∷ xs) user u ne = aux (x ≟ user)
  where
    ih = like-remove-iff xs user u ne

    aux : (d : Dec (x ≡ user)) →
          (u ∈ x ∷ xs) ⇔ (u ∈ like-remove-cons x xs user d)
    aux (yes q) = fwd , bwd
      where
        fwd : u ∈ (x ∷ xs) → u ∈ like-remove xs user
        fwd m = step (∈-cons m)
          where
            step : (u ≡ x) ⊎ (u ∈ xs) → u ∈ like-remove xs user
            step (inj₁ e) = ⊥-elim (ne (sym (trans e q)))
            step (inj₂ r) = proj₁ ih r

        bwd : u ∈ like-remove xs user → u ∈ (x ∷ xs)
        bwd r = there (proj₂ ih r)
    aux (no ¬q) = fwd , bwd
      where
        fwd : u ∈ (x ∷ xs) → u ∈ (x ∷ like-remove xs user)
        fwd m = step (∈-cons m)
          where
            step : (u ≡ x) ⊎ (u ∈ xs) → u ∈ (x ∷ like-remove xs user)
            step (inj₁ e) =
              subst (λ z → z ∈ (x ∷ like-remove xs user)) (sym e) here
            step (inj₂ r) = there (proj₁ ih r)

        bwd : u ∈ (x ∷ like-remove xs user) → u ∈ (x ∷ xs)
        bwd m = step (∈-cons m)
          where
            step : (u ≡ x) ⊎ (u ∈ like-remove xs user) → u ∈ (x ∷ xs)
            step (inj₁ e) = subst (λ z → z ∈ (x ∷ xs)) (sym e) here
            step (inj₂ r) = there (proj₂ ih r)

like-remove-others :
  (likes : List String) (user u : String) → user ≢ u →
  (u ∈ like-remove likes user → u ∈ likes)
  ∧ (u ∉ like-remove likes user → u ∉ likes)
like-remove-others likes user u ne =
    proj₂ (like-remove-iff likes user u ne)
  , (λ ¬mem mem → ¬mem (proj₁ (like-remove-iff likes user u ne) mem))

uniq-like-remove :
  (likes : List String) (user : String) → uniq likes → uniq (like-remove likes user)
uniq-like-remove []       user uq = tt
uniq-like-remove (x ∷ xs) user uq = aux (x ≟ user)
  where
    aux : (d : Dec (x ≡ user)) → uniq (like-remove-cons x xs user d)
    aux (yes _) = uniq-like-remove xs user (proj₂ uq)
    aux (no ¬q) =
      ( (λ m → proj₁ uq (proj₂ (like-remove-iff xs user x (≢-swap ¬q)) m))
      , uniq-like-remove xs user (proj₂ uq) )

--------------------------------------------------------------------------------
-- The post transition: `pid`'s post keeps every field but its like list.
--------------------------------------------------------------------------------

with-likes : Post → List String → Post
with-likes (post a t v s _ r p) ls = post a t v s ls r p

liked-post : (pst : Post) (user : String) → Post
liked-post pst user = with-likes pst (like-add (Post.likes pst) user)

unliked-post : (pst : Post) (user : String) → Post
unliked-post pst user = with-likes pst (like-remove (Post.likes pst) user)

with-likes-replies :
  (pst : Post) (ls : List String) → Post.replies (with-likes pst ls) ≡ Post.replies pst
with-likes-replies (post _ _ _ _ _ _ _) _ = refl

with-likes-parent :
  (pst : Post) (ls : List String) → Post.parent (with-likes pst ls) ≡ Post.parent pst
with-likes-parent (post _ _ _ _ _ _ _) _ = refl

-- `no-duplicate-likes` (Twitter.agda:110-113) after a like.
like-uniq-likes :
  (before : World) (pid : PostId) (pst pst' : Post) (user : String) →
  World.post-at before pid ≡ just pst →
  Post.likes pst' ≡ like-add (Post.likes pst) user →
  {y : PostId} {z : Post} →
  set-post (World.post-at before) pid (just pst') y ≡ just z →
  uniq (Post.likes z)
like-uniq-likes before pid pst pst' user peq likes-eq {y} {z} eq =
  decide (y ≟ₚ pid)
  where
    decide : Dec (y ≡ pid) → uniq (Post.likes z)
    decide (yes p) =
      subst (λ r → uniq (Post.likes r))
            (just-inj (trans (sym (set-post-same-at {x = y} p)) eq))
            (subst (λ r → uniq r) (sym likes-eq)
                   (uniq-like-add (Post.likes pst) user
                                  (World.no-duplicate-likes before peq)))
    decide (no ¬p) =
      World.no-duplicate-likes before
        (trans (sym (set-post-other {x = y} ¬p)) eq)

-- ... and after an unlike.
unlike-uniq-likes :
  (before : World) (pid : PostId) (pst pst' : Post) (user : String) →
  World.post-at before pid ≡ just pst →
  Post.likes pst' ≡ like-remove (Post.likes pst) user →
  {y : PostId} {z : Post} →
  set-post (World.post-at before) pid (just pst') y ≡ just z →
  uniq (Post.likes z)
unlike-uniq-likes before pid pst pst' user peq likes-eq {y} {z} eq =
  decide (y ≟ₚ pid)
  where
    decide : Dec (y ≡ pid) → uniq (Post.likes z)
    decide (yes p) =
      subst (λ r → uniq (Post.likes r))
            (just-inj (trans (sym (set-post-same-at {x = y} p)) eq))
            (subst (λ r → uniq r) (sym likes-eq)
                   (uniq-like-remove (Post.likes pst) user
                                     (World.no-duplicate-likes before peq)))
    decide (no ¬p) =
      World.no-duplicate-likes before
        (trans (sym (set-post-other {x = y} ¬p)) eq)

liked-world :
  (before : World) (pid : PostId) (user : String) (pst : Post) →
  World.post-at before pid ≡ just pst → World
liked-world before pid user pst peq = record
  { account-at          = World.account-at before
  ; session-at          = World.session-at before
  ; post-at             = set-post (World.post-at before) pid
                            (just (liked-post pst user))
  ; follows             = World.follows before
  ; newest-first        = World.newest-first before
  ; used-post-ids       = World.used-post-ids before
  ; used-session-ids    = World.used-session-ids before
  ; only-used-pids      = delete-used before pid (liked-post pst user)
                            (present-used before peq)
  ; only-used-sids      = World.only-used-sids before
  ; only-valid-sessions = World.only-valid-sessions before
  ; only-valid-posts    = delete-valid-posts before pid (liked-post pst user)
  ; only-valid-replies  = delete-replies before pid pst (liked-post pst user) peq
                            (with-likes-replies pst (like-add (Post.likes pst) user))
                            (with-likes-parent pst (like-add (Post.likes pst) user))
  ; no-duplicate-replies = delete-uniq-replies before pid pst (liked-post pst user) peq
                            (with-likes-replies pst (like-add (Post.likes pst) user))
  ; no-duplicate-likes   = like-uniq-likes before pid pst (liked-post pst user) user
                            peq refl
  ; no-duplicate-posts   = World.no-duplicate-posts before
  }

unliked-world :
  (before : World) (pid : PostId) (user : String) (pst : Post) →
  World.post-at before pid ≡ just pst → World
unliked-world before pid user pst peq = record
  { account-at          = World.account-at before
  ; session-at          = World.session-at before
  ; post-at             = set-post (World.post-at before) pid
                            (just (unliked-post pst user))
  ; follows             = World.follows before
  ; newest-first        = World.newest-first before
  ; used-post-ids       = World.used-post-ids before
  ; used-session-ids    = World.used-session-ids before
  ; only-used-pids      = delete-used before pid (unliked-post pst user)
                            (present-used before peq)
  ; only-used-sids      = World.only-used-sids before
  ; only-valid-sessions = World.only-valid-sessions before
  ; only-valid-posts    = delete-valid-posts before pid (unliked-post pst user)
  ; only-valid-replies  = delete-replies before pid pst (unliked-post pst user) peq
                            (with-likes-replies pst (like-remove (Post.likes pst) user))
                            (with-likes-parent pst (like-remove (Post.likes pst) user))
  ; no-duplicate-replies = delete-uniq-replies before pid pst (unliked-post pst user) peq
                            (with-likes-replies pst (like-remove (Post.likes pst) user))
  ; no-duplicate-likes   = unlike-uniq-likes before pid pst (unliked-post pst user) user
                            peq refl
  ; no-duplicate-posts   = World.no-duplicate-posts before
  }

-- `like-post` (Twitter.agda:587-613), with every premise discharged: the user
-- is a member of the after list, every other user keeps its membership status,
-- the rest of the post is unchanged, and no other row of the world moves.
like-success :
  ∀ (before : World) {sid : SessionId} {pid : PostId}
    {acc : Account} {user : String} {pst : Post}
  (vs : ValidSession before sid acc user)
  (can : CanReadPost before sid pid)
  (peq : World.post-at before pid ≡ just pst) →
  Step before (like sid pid) (liked-world before pid user pst peq) success
like-success before {sid} {pid} {acc} {user} {pst} vs can peq =
  like-post
    {before = before}
    {after  = liked-world before pid user pst peq}
    {sid    = sid}
    {pid    = pid}
    {acc    = acc}
    {user   = user}
    {post   = pst}
    {post'  = liked-post pst user}
    vs
    can
    peq
    set-post-same
    (like-add-member (Post.likes pst) user)
    refl
    refl
    refl
    refl
    refl
    refl
    (λ {u'} ne → like-add-others (Post.likes pst) user u' ne)
    (λ {other} ¬e →
         refl , refl , sym (set-post-other (≢-swap ¬e)) , refl , refl)

-- `unlike-post` (Twitter.agda:621-647).  Its `post` is the AFTER post and its
-- `post'` the BEFORE one, so `user ∉ Post.likes post` is discharged by
-- `like-remove-absent`.
unlike-success :
  ∀ (before : World) {sid : SessionId} {pid : PostId}
    {acc : Account} {user : String} {pst : Post}
  (vs : ValidSession before sid acc user)
  (can : CanReadPost before sid pid)
  (peq : World.post-at before pid ≡ just pst) →
  Step before (unlike sid pid) (unliked-world before pid user pst peq) success
unlike-success before {sid} {pid} {acc} {user} {pst} vs can peq =
  unlike-post
    {before = before}
    {after  = unliked-world before pid user pst peq}
    {sid    = sid}
    {pid    = pid}
    {acc    = acc}
    {user   = user}
    {post   = unliked-post pst user}
    {post'  = pst}
    vs
    can
    peq
    set-post-same
    (like-remove-absent (Post.likes pst) user)
    refl
    refl
    refl
    refl
    refl
    refl
    (λ {u'} ne → like-remove-others (Post.likes pst) user u' ne)
    (λ {other} ¬e →
         sym (set-post-other (≢-swap ¬e)) , refl , refl , refl , refl)

-- `failed-like-post` / `failed-unlike-post` (Twitter.agda:615-619, 649-653):
-- an unreadable post is `denied` and the world is untouched.  `can-read-absent`,
-- `can-read-deleted` and `can-read-private` above all supply the
-- `¬ CanReadPost` these need.
like-denied :
  ∀ (before : World) {sid : SessionId} {pid : PostId}
    {acc : Account} {user : String} →
  ValidSession before sid acc user →
  ¬ CanReadPost before sid pid →
  Step before (like sid pid) before denied
like-denied before vs ¬can = failed-like-post vs ¬can

unlike-denied :
  ∀ (before : World) {sid : SessionId} {pid : PostId}
    {acc : Account} {user : String} →
  ValidSession before sid acc user →
  ¬ CanReadPost before sid pid →
  Step before (unlike sid pid) before denied
unlike-denied before vs ¬can = failed-unlike-post vs ¬can

--------------------------------------------------------------------------------
-- P14: failed-access for the social commands (Twitter.agda:464-468)
--
-- Each of the four commands extracts its session (Twitter.agda:203-207), so a
-- session that is not `active` expires the request and changes nothing.
--------------------------------------------------------------------------------

follow-expired :
  ∀ (before : World) {sid : SessionId} {followee : String} →
  (∀ {user} → World.session-at before sid ≡ active user → ⊥) →
  Step before (follow sid followee) before expired
follow-expired before {sid} {followee} ¬act =
  failed-access-inactive before (follow sid followee) sid refl ¬act

unfollow-expired :
  ∀ (before : World) {sid : SessionId} {followee : String} →
  (∀ {user} → World.session-at before sid ≡ active user → ⊥) →
  Step before (unfollow sid followee) before expired
unfollow-expired before {sid} {followee} ¬act =
  failed-access-inactive before (unfollow sid followee) sid refl ¬act

like-expired :
  ∀ (before : World) {sid : SessionId} {pid : PostId} →
  (∀ {user} → World.session-at before sid ≡ active user → ⊥) →
  Step before (like sid pid) before expired
like-expired before {sid} {pid} ¬act =
  failed-access-inactive before (like sid pid) sid refl ¬act

unlike-expired :
  ∀ (before : World) {sid : SessionId} {pid : PostId} →
  (∀ {user} → World.session-at before sid ≡ active user → ⊥) →
  Step before (unlike sid pid) before expired
unlike-expired before {sid} {pid} ¬act =
  failed-access-inactive before (unlike sid pid) sid refl ¬act
-- ---------------------------------------------------------------------------
-- P15: timelines (Twitter.agda:557-585)
--
-- The three timeline rules read
--   `take n ∘ filterᵇ (follows-post-author before user) ∘ filter
--    (can-read-post before sid) ∘ newest-first`  (personal),
--   `take n ∘ filter (can-read-post before sid) ∘ newest-first` (private
--    global), and `take n ∘ filter (is-post-public before) ∘ newest-first`
--    (public global).
-- The engine instead evaluates the simple test its SQL two-column filters
-- express: `*-allowed`, a `Bool` over the looked-up post row and the follow
-- table.  `filter-dec-eq`, `filterᵇ-cong` and `filterᵇ-and` turn the spec's
-- filters into `filterᵇ` of a `Bool` predicate, and `personal-pointwise`,
-- `global-pointwise` and `public-pointwise` show that predicate agrees with
-- `personal-allowed` / `global-allowed` / `public-allowed` -- the exact list
-- the Rust tests compute.  `personal-timeline`, `private-global-timeline`
-- and `public-global-timeline` are then the spec's three rules rewritten by
-- `personal-char` / `global-char` / `public-char`, and
-- `personal-timeline-expired` / `private-global-timeline-expired` are
-- `failed-access` for an inactive session.  `read-global-timeline nothing`
-- is tokenless (`extract-sid` is `nothing`), so it never expires.
-- ---------------------------------------------------------------------------

vis-b : Visibility → Bool
vis-b everyone       = true
vis-b followers-only = false

status-b : PostStatus → Bool
status-b live    = true
status-b deleted = false

and-b : Bool → Bool → Bool
and-b true  b = b
and-b false _ = false

or-b : Bool → Bool → Bool
or-b true  _ = true
or-b false b = b

and-b-false-right : (b : Bool) → and-b b false ≡ false
and-b-false-right true  = refl
and-b-false-right false = refl

or-b-true-right : (b : Bool) → or-b b true ≡ true
or-b-true-right true  = refl
or-b-true-right false = refl

and-b-true-left : (b c : Bool) → and-b b c ≡ true → b ≡ true
and-b-true-left true  c h = refl
and-b-true-left false c ()

and-b-true-right : (b c : Bool) → and-b b c ≡ true → c ≡ true
and-b-true-right true  c h = h
and-b-true-right false c ()

or-b-true-left :
  (b c : Bool) → or-b b c ≡ true → (b ≡ true) ⊎ ((b ≡ false) × (c ≡ true))
or-b-true-left true  c h = inj₁ refl
or-b-true-left false c h = inj₂ (refl , h)

bool-false : (b : Bool) → (b ≡ true → ⊥) → b ≡ false
bool-false true  ¬t = ⊥-elim (¬t refl)
bool-false false ¬t = refl

status-b-live : (s : PostStatus) → status-b s ≡ true → s ≡ live
status-b-live live    h = refl
status-b-live deleted ()

vis-b-everyone : (v : Visibility) → vis-b v ≡ true → v ≡ everyone
vis-b-everyone everyone       h = refl
vis-b-everyone followers-only ()

vis-b-followers : (v : Visibility) → vis-b v ≡ false → v ≡ followers-only
vis-b-followers everyone       h = ⊥-elim (false≢true (sym h))
vis-b-followers followers-only h = refl

-- The simple characterizations the engine's SQL computes.
personal-ok : World → String → Maybe Post → Bool
personal-ok w user nothing                            = false
personal-ok w user (just (post a txt v s lk rp par)) = and-b (status-b s) (World.follows w user a)

global-ok : World → String → Maybe Post → Bool
global-ok w user nothing                            = false
global-ok w user (just (post a txt v s lk rp par)) =
  and-b (status-b s) (or-b (vis-b v) (World.follows w user a))

public-ok : Maybe Post → Bool
public-ok nothing                            = false
public-ok (just (post a txt v s lk rp par)) = and-b (status-b s) (vis-b v)

personal-allowed : World → String → PostId → Bool
personal-allowed w user pid = personal-ok w user (World.post-at w pid)

global-allowed : World → String → PostId → Bool
global-allowed w user pid = global-ok w user (World.post-at w pid)

public-allowed : World → PostId → Bool
public-allowed w pid = public-ok (World.post-at w pid)

-- `follows-post-author` (Twitter.agda:366-369) as a function of the post row.
follows-maybe : World → String → Maybe Post → Bool
follows-maybe w user nothing                            = false
follows-maybe w user (just (post a txt v s lk rp par)) = World.follows w user a

follows-maybe-just : (w : World) (user : String) (p : Post) →
  follows-maybe w user (just p) ≡ World.follows w user (Post.author p)
follows-maybe-just w user (post a txt v s lk rp par) = refl

follows-post-author-eq : (w : World) (user : String) (pid : PostId) →
  follows-post-author w user pid ≡ follows-maybe w user (World.post-at w pid)
follows-post-author-eq w user pid with World.post-at w pid
... | nothing = refl
... | just p  = refl

follows-post-author-just :
  (w : World) (user : String) (pid : PostId) (p : Post) →
  World.post-at w pid ≡ just p →
  follows-post-author w user pid ≡ World.follows w user (Post.author p)
follows-post-author-just w user pid p eq =
  trans (follows-post-author-eq w user pid)
        (trans (cong (follows-maybe w user) eq) (follows-maybe-just w user p))

-- filter over a Decidable predicate = filterᵇ over its decision.
filter-dec-eq : ∀ {a p} {A : Set a} {P : A → Set p} (P? : Decidable P) (xs : List A) →
  filter P? xs ≡ filterᵇ (λ x → does (P? x)) xs
filter-dec-eq P? [] = refl
filter-dec-eq P? (x ∷ xs) with does (P? x)
... | true  = cong (x ∷_) (filter-dec-eq P? xs)
... | false = filter-dec-eq P? xs

filterᵇ-true : ∀ {a} {A : Set a} (p : A → Bool) (x : A) (xs : List A) →
  p x ≡ true → filterᵇ p (x ∷ xs) ≡ x ∷ filterᵇ p xs
filterᵇ-true p x xs eq with p x
... | true  = refl
... | false = ⊥-elim (false≢true eq)

filterᵇ-false : ∀ {a} {A : Set a} (p : A → Bool) (x : A) (xs : List A) →
  p x ≡ false → filterᵇ p (x ∷ xs) ≡ filterᵇ p xs
filterᵇ-false p x xs eq with p x
... | true  = ⊥-elim (false≢true (sym eq))
... | false = refl

filterᵇ-cong : ∀ {a} {A : Set a} (p q : A → Bool) (xs : List A) →
  (∀ x → p x ≡ q x) → filterᵇ p xs ≡ filterᵇ q xs
filterᵇ-cong p q [] eq = refl
filterᵇ-cong p q (x ∷ xs) eq with p x in ep
... | true  = trans (cong (x ∷_) (filterᵇ-cong p q xs eq))
                    (sym (filterᵇ-true q x xs (trans (sym (eq x)) ep)))
... | false = trans (filterᵇ-cong p q xs eq)
                    (sym (filterᵇ-false q x xs (trans (sym (eq x)) ep)))

and-f : ∀ {a} {A : Set a} (p q : A → Bool) → A → Bool
and-f p q z = and-b (p z) (q z)

filterᵇ-and-cons :
  ∀ {a} {A : Set a} (p q : A → Bool) (x : A) (xs : List A) (b c : Bool) →
  q x ≡ b → p x ≡ c →
  filterᵇ p (filterᵇ q xs) ≡ filterᵇ (and-f p q) xs →
  filterᵇ p (filterᵇ q (x ∷ xs)) ≡ filterᵇ (and-f p q) (x ∷ xs)
filterᵇ-and-cons p q x xs false c eqq eqp ih =
  trans (cong (filterᵇ p) (filterᵇ-false q x xs eqq))
        (trans ih
               (sym (filterᵇ-false (and-f p q) x xs
                          (trans (cong (λ z → and-b (p x) z) eqq)
                                 (and-b-false-right (p x))))))
filterᵇ-and-cons p q x xs true c eqq eqp ih with c
... | true =
  trans (cong (filterᵇ p) (filterᵇ-true q x xs eqq))
        (trans (filterᵇ-true p x (filterᵇ q xs) eqp)
               (trans (cong (x ∷_) ih)
                      (sym (filterᵇ-true (and-f p q) x xs
                             (trans (cong (λ z → and-b z (q x)) eqp)
                                    (cong (and-b true) eqq))))))
... | false =
  trans (cong (filterᵇ p) (filterᵇ-true q x xs eqq))
        (trans (filterᵇ-false p x (filterᵇ q xs) eqp)
               (trans ih
                      (sym (filterᵇ-false (and-f p q) x xs
                             (cong (λ z → and-b z (q x)) eqp)))))

filterᵇ-and : ∀ {a} {A : Set a} (p q : A → Bool) (xs : List A) →
  filterᵇ p (filterᵇ q xs) ≡ filterᵇ (and-f p q) xs
filterᵇ-and p q [] = refl
filterᵇ-and p q (x ∷ xs) =
  filterᵇ-and-cons p q x xs (q x) (p x) refl refl (filterᵇ-and p q xs)

does-eq : ∀ {a} {A : Set a} (P? : Dec A) (p : Bool) →
  (A → p ≡ true) → (¬ A → p ≡ false) → does P? ≡ p
does-eq (yes a) p A→true ¬A→false = sym (A→true a)
does-eq (no ¬a) p A→true ¬A→false = sym (¬A→false ¬a)

-- `CanReadPost` implies the simple (private-global) characterization.
can-read-true :
  (w : World) (sid : SessionId) (pid : PostId) {acc : Account} {user : String} →
  ValidSession w sid acc user →
  CanReadPost w sid pid →
  global-ok w user (World.post-at w pid) ≡ true
can-read-true w sid pid {acc} {user} vs
  (post-is-public {post = post a txt v s lk rp par} vs' peq refl refl)
  rewrite peq = refl
can-read-true w sid pid {acc} {user} vs
  (post-is-private {acc = acc'} {user = user'} {post = post a txt v s lk rp par}
                   vs' peq refl refl f) =
  subst (λ m → global-ok w user m ≡ true) (sym peq)
        (subst (λ b → and-b true (or-b false b) ≡ true) (sym follows-eq) refl)
  where
    u-eq : user ≡ user'
    u-eq = active-inj (trans (sym (ValidSession.session-unchanged vs))
                             (ValidSession.session-unchanged vs'))

    follows-eq : World.follows w user a ≡ true
    follows-eq = trans (cong (λ z → World.follows w z a) u-eq) f

-- ... and conversely.
can-read-global-m :
  (w : World) (sid : SessionId) (pid : PostId) {acc : Account} {user : String} →
  ValidSession w sid acc user → (m : Maybe Post) →
  World.post-at w pid ≡ m →
  global-ok w user m ≡ true →
  CanReadPost w sid pid
can-read-global-m w sid pid {acc} {user} vs nothing eq h =
  ⊥-elim (false≢true h)
can-read-global-m w sid pid {acc} {user} vs (just (post a txt v s lk rp par)) eq h =
  go (or-b-true-left (vis-b v) (World.follows w user a) rest)
  where
    st-true : status-b s ≡ true
    st-true = and-b-true-left (status-b s) (or-b (vis-b v) (World.follows w user a)) h

    s-live : s ≡ live
    s-live = status-b-live s st-true

    rest : or-b (vis-b v) (World.follows w user a) ≡ true
    rest = and-b-true-right (status-b s) (or-b (vis-b v) (World.follows w user a)) h

    go : (vis-b v ≡ true) ⊎ ((vis-b v ≡ false) × (World.follows w user a ≡ true))
       → CanReadPost w sid pid
    go (inj₁ ev)          = post-is-public vs eq (vis-b-everyone v ev) s-live
    go (inj₂ (nv , fv))   = post-is-private vs eq (vis-b-followers v nv) s-live fv

can-read-global :
  (w : World) (sid : SessionId) (pid : PostId) {acc : Account} {user : String} →
  ValidSession w sid acc user →
  global-ok w user (World.post-at w pid) ≡ true →
  CanReadPost w sid pid
can-read-global w sid pid vs =
  can-read-global-m w sid pid vs (World.post-at w pid) refl

can-read-false :
  (w : World) (sid : SessionId) (pid : PostId) {acc : Account} {user : String} →
  ValidSession w sid acc user →
  ¬ CanReadPost w sid pid →
  global-ok w user (World.post-at w pid) ≡ false
can-read-false w sid pid {acc} {user} vs ¬can =
  bool-false (global-ok w user (World.post-at w pid))
             (λ h → ¬can (can-read-global w sid pid vs h))

global-pointwise :
  (w : World) (sid : SessionId) (pid : PostId) {acc : Account} {user : String} →
  ValidSession w sid acc user →
  does (can-read-post w sid pid) ≡ global-allowed w user pid
global-pointwise w sid pid {acc} {user} vs =
  does-eq (can-read-post w sid pid) (global-ok w user (World.post-at w pid))
          (can-read-true w sid pid vs) (can-read-false w sid pid vs)

personal-bool : (f st tv c : Bool) →
  c ≡ and-b st (or-b tv f) → and-b f c ≡ and-b st f
personal-bool f st tv c h with f
... | false = sym (and-b-false-right st)
... | true  = trans h (cong (and-b st) (or-b-true-right tv))

personal-pointwise-just :
  (w : World) (sid : SessionId) (pid : PostId) {acc : Account} {user : String} →
  ValidSession w sid acc user → (p : Post) →
  World.post-at w pid ≡ just p →
  and-b (World.follows w user (Post.author p)) (does (can-read-post w sid pid))
  ≡ and-b (status-b (Post.status p)) (World.follows w user (Post.author p))
personal-pointwise-just w sid pid {acc} {user} vs
  (post a txt v s lk rp par) eq =
  personal-bool (World.follows w user a) (status-b s) (vis-b v)
                (does (can-read-post w sid pid))
                (trans (global-pointwise w sid pid vs)
                       (cong (global-ok w user) eq))

personal-step-m :
  (w : World) (sid : SessionId) (pid : PostId) {acc : Account} {user : String} →
  ValidSession w sid acc user → (m : Maybe Post) →
  World.post-at w pid ≡ m →
  and-b (follows-maybe w user m) (does (can-read-post w sid pid))
  ≡ personal-ok w user m
personal-step-m w sid pid {acc} {user} vs nothing eq = refl
personal-step-m w sid pid {acc} {user} vs (just (post a txt v s lk rp par)) eq =
  personal-pointwise-just w sid pid vs (post a txt v s lk rp par) eq

personal-step :
  (w : World) (sid : SessionId) (pid : PostId) {acc : Account} {user : String} →
  ValidSession w sid acc user →
  and-b (follows-maybe w user (World.post-at w pid)) (does (can-read-post w sid pid))
  ≡ personal-ok w user (World.post-at w pid)
personal-step w sid pid vs = personal-step-m w sid pid vs (World.post-at w pid) refl

personal-pointwise :
  (w : World) (sid : SessionId) (pid : PostId) {acc : Account} {user : String} →
  ValidSession w sid acc user →
  and-b (follows-post-author w user pid) (does (can-read-post w sid pid))
  ≡ personal-allowed w user pid
personal-pointwise w sid pid {acc} {user} vs =
  trans (cong (λ z → and-b z (does (can-read-post w sid pid)))
              (follows-post-author-eq w user pid))
        (personal-step w sid pid vs)

-- `is-post-public` (Twitter.agda:342-357) is the `public-ok` characterization.
public-true :
  (w : World) (pid : PostId) →
  (∃[ p ] (World.post-at w pid ≡ just p)
         × (Post.visibility p ≡ everyone) × (Post.status p ≡ live)) →
  public-ok (World.post-at w pid) ≡ true
public-true w pid (post a txt v s lk rp par , peq , vis , stp)
  rewrite peq | vis | stp = refl

public-can-read-m :
  (w : World) (pid : PostId) (m : Maybe Post) →
  World.post-at w pid ≡ m →
  public-ok m ≡ true →
  ∃[ p ] (World.post-at w pid ≡ just p)
        × (Post.visibility p ≡ everyone) × (Post.status p ≡ live)
public-can-read-m w pid nothing eq h = ⊥-elim (false≢true h)
public-can-read-m w pid (just (post a txt v s lk rp par)) eq h =
  ( post a txt v s lk rp par
  , eq
  , vis-b-everyone v (and-b-true-right (status-b s) (vis-b v) h)
  , status-b-live s (and-b-true-left (status-b s) (vis-b v) h) )

public-can-read :
  (w : World) (pid : PostId) →
  public-ok (World.post-at w pid) ≡ true →
  ∃[ p ] (World.post-at w pid ≡ just p)
        × (Post.visibility p ≡ everyone) × (Post.status p ≡ live)
public-can-read w pid = public-can-read-m w pid (World.post-at w pid) refl

public-pointwise :
  (w : World) (pid : PostId) →
  does (is-post-public w pid) ≡ public-allowed w pid
public-pointwise w pid =
  does-eq (is-post-public w pid) (public-ok (World.post-at w pid))
          (public-true w pid)
          (λ ¬a → bool-false (public-ok (World.post-at w pid))
                             (λ h → ¬a (public-can-read w pid h)))

-- The three characterizations: the spec's filter expression equals the simple one.
personal-char :
  ∀ {w sid acc user} → ValidSession w sid acc user →
  filterᵇ (follows-post-author w user)
          (filter (can-read-post w sid) (World.newest-first w))
  ≡ filterᵇ (personal-allowed w user) (World.newest-first w)
personal-char {w} {sid} {acc} {user} vs =
  trans (cong (filterᵇ (follows-post-author w user))
              (filter-dec-eq (can-read-post w sid) (World.newest-first w)))
        (trans (filterᵇ-and (follows-post-author w user)
                            (λ pid → does (can-read-post w sid pid))
                            (World.newest-first w))
               (filterᵇ-cong (λ pid → and-b (follows-post-author w user pid)
                                          (does (can-read-post w sid pid)))
                             (personal-allowed w user)
                             (World.newest-first w)
                             (λ pid → personal-pointwise w sid pid vs)))

global-char :
  ∀ {w sid acc user} → ValidSession w sid acc user →
  filter (can-read-post w sid) (World.newest-first w)
  ≡ filterᵇ (global-allowed w user) (World.newest-first w)
global-char {w} {sid} {acc} {user} vs =
  trans (filter-dec-eq (can-read-post w sid) (World.newest-first w))
        (filterᵇ-cong (λ pid → does (can-read-post w sid pid))
                      (global-allowed w user)
                      (World.newest-first w)
                      (λ pid → global-pointwise w sid pid vs))

public-char :
  (w : World) →
  filter (is-post-public w) (World.newest-first w)
  ≡ filterᵇ (public-allowed w) (World.newest-first w)
public-char w =
  trans (filter-dec-eq (is-post-public w) (World.newest-first w))
        (filterᵇ-cong (λ pid → does (is-post-public w pid))
                      (public-allowed w)
                      (World.newest-first w)
                      (public-pointwise w))

-- P15: the timelines (Twitter.agda:557-585).
personal-timeline :
  ∀ {before n sid acc user} → ValidSession before sid acc user →
  Step before (read-personal-timeline sid n) before
    (returned-timeline
       (take n (filterᵇ (personal-allowed before user) (World.newest-first before))))
personal-timeline {before} {n} {sid} {acc} {user} vs =
  subst (λ xs → Step before (read-personal-timeline sid n) before
                  (returned-timeline (take n xs)))
        (personal-char vs)
        (get-personal-timeline {n = n} vs)

private-global-timeline :
  ∀ {before n sid acc user} → ValidSession before sid acc user →
  Step before (read-global-timeline (just sid) n) before
    (returned-timeline
       (take n (filterᵇ (global-allowed before user) (World.newest-first before))))
private-global-timeline {before} {n} {sid} {acc} {user} vs =
  subst (λ xs → Step before (read-global-timeline (just sid) n) before
                  (returned-timeline (take n xs)))
        (global-char vs)
        (get-private-global-timeline {n = n} vs)

public-global-timeline :
  ∀ {before n} →
  Step before (read-global-timeline nothing n) before
    (returned-timeline
       (take n (filterᵇ (public-allowed before) (World.newest-first before))))
public-global-timeline {before} {n} =
  subst (λ xs → Step before (read-global-timeline nothing n) before
                  (returned-timeline (take n xs)))
        (public-char before)
        (get-public-global-timeline {n = n})

-- An inactive session expires both session-carrying timelines.
personal-timeline-expired :
  ∀ (before : World) {sid : SessionId} {n : Nat} →
  (∀ {user} → World.session-at before sid ≡ active user → ⊥) →
  Step before (read-personal-timeline sid n) before expired
personal-timeline-expired before {sid} {n} ¬act =
  failed-access-inactive before (read-personal-timeline sid n) sid refl ¬act

private-global-timeline-expired :
  ∀ (before : World) {sid : SessionId} {n : Nat} →
  (∀ {user} → World.session-at before sid ≡ active user → ⊥) →
  Step before (read-global-timeline (just sid) n) before expired
private-global-timeline-expired before {sid} {n} ¬act =
  failed-access-inactive before (read-global-timeline (just sid) n) sid refl ¬act
