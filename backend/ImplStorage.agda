-- Storage encodings for db.rs (task T3): the integer pins for visibility,
-- post status and session rows, mirroring enc_vis/dec_vis, enc_status/dec_status
-- and enc_sess_row/dec_sess_row. Self-contained: no spec imports.

module ImplStorage where

open import Data.Nat                        using (ℕ; zero; suc)
open import Data.Nat.Properties             using () renaming (_≟_ to _≟ℕ_)
open import Data.String                     using (String)
open import Data.Maybe                      using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no)

-- Visibility: Everyone = 0, FollowersOnly = 1; unknown codes decode to Everyone.

data Vis : Set where
  everyone       : Vis
  followers-only : Vis

vis-to-nat : Vis → ℕ
vis-to-nat everyone = zero
vis-to-nat followers-only = suc zero

vis-of : ℕ → Vis
vis-of n with (_≟ℕ_ n (suc zero))
vis-of n | yes _ = followers-only
vis-of n | no _ = everyone

-- Post status: live (Other) = 0, Deleted = 1; unknown codes decode to live.

data St : Set where
  live    : St
  deleted : St

st-to-nat : St → ℕ
st-to-nat live = zero
st-to-nat deleted = suc zero

st-of : ℕ → St
st-of n with (_≟ℕ_ n (suc zero))
st-of n | yes _ = deleted
st-of n | no _ = live

-- Session rows: (1, just u) → active u; (2, nothing) → revoked;
-- anything else is malformed and decodes to revoked (cf. dec_sess_row fallbacks).

data Sess : Set where
  active  : String → Sess
  revoked : Sess

dec-sess : ℕ → Maybe String → Sess
dec-sess zero (just u) = revoked
dec-sess zero nothing = revoked
dec-sess (suc zero) (just u) = active u
dec-sess (suc zero) nothing = revoked
dec-sess (suc (suc n)) u = revoked

-- The encoding pins that db.rs implements.

th-vis-everyone : vis-of (vis-to-nat everyone) ≡ everyone
th-vis-everyone = refl

th-vis-fo : vis-of (vis-to-nat followers-only) ≡ followers-only
th-vis-fo = refl

th-status-live : st-of (st-to-nat live) ≡ live
th-status-live = refl

th-status-deleted : st-of (st-to-nat deleted) ≡ deleted
th-status-deleted = refl

th-sess-active : dec-sess (suc zero) (just "alice") ≡ active "alice"
th-sess-active = refl

th-sess-revoked : dec-sess (suc (suc zero)) nothing ≡ revoked
th-sess-revoked = refl
