/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.Exist
import Nc.Uni.LenU
import Nc.Uni.TopU
import Nc.Tape.ProgRun

/-!
# The universal automaton: bounds for the time
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset NS1

section General

variable {A : Type} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K] {P : Mach A M K}

theorem tU_mono {b T T' L L' : ℕ} (hT : T ≤ T') (hL : L ≤ L') : tU b T L ≤ tU b T' L' := by
  unfold tU
  gcongr

end General

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- The number of steps. -/
def stepsU (supp : Finset (List Bool)) (τ s : ℕ) : ℕ := 3 * s + (40 + 2 * Lm supp) * τ + 10

theorem tU_le (b T L : ℕ) : tU b T L ≤ (50 + b) * ((T + 1) * (L + 1) ^ 2) := by
  obtain ⟨t, rfl⟩ : ∃ t, T = t := ⟨T, rfl⟩
  have h3 : L + 2 ≤ 2 * (L + 1) := by omega
  have h4 : L + 3 ≤ 3 * (L + 1) := by omega
  have h5 : 2 * T + 1 ≤ 2 * (T + 1) := by omega
  have hl : 1 ≤ L + 1 := by omega
  have ht : 1 ≤ T + 1 := by omega
  unfold tU
  -- With `t = T + 1` and `l = L + 1`: bounding `T ≤ t`, `L + 2 ≤ 2 l` (`h3`), `L + 3 ≤ 3 l` (`h4`),
  -- `L + 4 ≤ 4 l` and `2 T + 1 ≤ 2 t` (`h5`) term by term gives at most
  -- `24 t l² + 23 t l + t + 2 l + b l`; since `1 ≤ l` (`hl`) and `1 ≤ t` (`ht`), each of
  -- `t l`, `t`, `l` is at most `t l²`, and the coefficients sum to `24 + 23 + 1 + 2 + b = 50 + b`.
  grind

theorem size_le_lg (n : ℕ) : Nat.size n ≤ lg n := by
  rw [Nat.size_le, lg]
  exact Nat.lt_pow_succ_log_self (by norm_num) n

theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

end Nc.Uni
