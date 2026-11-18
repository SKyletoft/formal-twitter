-- Tick-schedule pins for backend/src/main.rs:next_tick (task RV2a).
-- Rust: pub fn next_tick(t: u64) -> u64 { (t + 1) % 4 } (main.rs:170-172), the
-- rotation behind DB3c's one-section-per-request reload and behind the orphan
-- test test_tick_rotation_cycle (main.rs:383).  u64 only wraps above 2^64 and the
-- tick is always produced by next_tick itself, so the schedule is modelled on Nat
-- with Data.Nat.DivMod's _%_ (same modulo as the Rust % on a non-negative operand).
--
-- th-next-tick-0..7 pin next-tick on 0..7, which is exactly the Rust test's third
-- loop: `for i in 0..8 { assert(next_tick i == (i + 1) % 4) }`.  th-cycle-0..3 pin
-- next-tick^4 = id on every residue, i.e. the test's second loop.  th-tick-hits
-- pins the eight landings of the test's first loop (step from tick 0, count the
-- section landed on) to [1,2,3,0,1,2,3,0].  That list is [1,2,3,0] twice, so each
-- of the four cache sections is hit exactly twice over eight requests: the hits
-- array is [2,2,2,2], and no section is re-queried more often than once per four
-- requests (never all at once).  Everything below is concrete, so every theorem is
-- refl; no postulates.

module ImplTick where

open import Data.Nat                              using (ℕ; zero; suc)
open import Data.Nat.DivMod                       using (_%_)
open import Data.List                             using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- main.rs:170-172 next_tick: (t + 1) % 4.

next-tick : ℕ → ℕ
next-tick t = suc t % 4

-- ---- the eight shift pins: next-tick i ≡ (i + 1) % 4 for i in 0..7 ----
-- (so the wrap lands at i = 3 and i = 7, exactly as the Rust % does.)
-- main.rs:399-401 asserts exactly this for i in 0..8.

th-next-tick-0 : next-tick 0 ≡ 1
th-next-tick-0 = refl

th-next-tick-1 : next-tick 1 ≡ 2
th-next-tick-1 = refl

th-next-tick-2 : next-tick 2 ≡ 3
th-next-tick-2 = refl

th-next-tick-3 : next-tick 3 ≡ 0
th-next-tick-3 = refl

th-next-tick-4 : next-tick 4 ≡ 1
th-next-tick-4 = refl

th-next-tick-5 : next-tick 5 ≡ 2
th-next-tick-5 = refl

th-next-tick-6 : next-tick 6 ≡ 3
th-next-tick-6 = refl

th-next-tick-7 : next-tick 7 ≡ 0
th-next-tick-7 = refl

-- ---- main.rs:394-397: next_tick^4 == id for start in 0..4 ----

th-cycle-0 : next-tick (next-tick (next-tick (next-tick 0))) ≡ 0
th-cycle-0 = refl

th-cycle-1 : next-tick (next-tick (next-tick (next-tick 1))) ≡ 1
th-cycle-1 = refl

th-cycle-2 : next-tick (next-tick (next-tick (next-tick 2))) ≡ 2
th-cycle-2 = refl

th-cycle-3 : next-tick (next-tick (next-tick (next-tick 3))) ≡ 3
th-cycle-3 = refl

-- ---- main.rs:384-392: the hits loop stepping eight times from tick 0 ----
-- Stepping from 0 the intermediate ticks are 0,1,2,3,4,5,6,7, so the sections
-- landed on are next-tick applied to upto 8 = [0,1,2,3,4,5,6,7].

upto : (n : ℕ) → List ℕ
upto zero      = []
upto (suc n)   = zero ∷ map suc (upto n)

th-tick-hits : map next-tick (upto 8) ≡ 1 ∷ 2 ∷ 3 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 0 ∷ []
th-tick-hits = refl

-- [1,2,3,0] appears twice in the pinned landing sequence, and its first block has
-- pairwise-distinct entries, so over eight requests every residue 0,1,2,3 is landed
-- on exactly twice: hits == [2,2,2,2], one reload of each section every four requests.
