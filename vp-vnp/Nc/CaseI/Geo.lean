/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Geometry for the lower bound of the complete network

The distance from half a unit vector, sums over a set and its complement, and the sign of a node for a set A ⊂ [k].
-/

namespace Nc.CaseI

open Finset

variable {k : ℕ}

/-- The distance from half a unit vector. -/
theorem dist_half_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {u : V}
    (hu : ‖u‖ = 1) (x : V) : dist ((1 / 2 : ℝ) • u) x ≤ 1 / 2 - inner ℝ u x + ‖x‖ ^ 2 := by
  rw [dist_eq_norm]
  have h1 : ‖(1 / 2 : ℝ) • u - x‖ ^ 2 = 1 / 4 - inner ℝ u x + ‖x‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, hu, real_inner_smul_left, show ‖(1 / 2 : ℝ)‖ = 1 / 2 by norm_num]
    ring
  nlinarith [sq_nonneg (‖(1 / 2 : ℝ) • u - x‖ - 1 / 2)]

theorem sum_ite_card (A : Finset (Fin k)) (y z : ℝ) :
    ∑ a : Fin k, (if a ∈ A then y else z) = A.card * y + ((k : ℝ) - A.card) * z := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.filter_mem_eq_inter, Finset.univ_inter]
  congr 2
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin k))) (fun a => a ∈ A)
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at h
  have : ((univ.filter fun a => a ∉ A).card : ℝ) = k - A.card := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact_mod_cast h
  exact this

/-- The sign of a node. -/
noncomputable def sideSign (A : Finset (Fin k)) (a : Fin k) : ℝ := if a ∈ A then 1 else -1

end Nc.CaseI
