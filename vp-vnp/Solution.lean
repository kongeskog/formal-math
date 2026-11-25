/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Statement
import Paper.Approximate

/-!
# Proofs of the statements, all from Theorem thm:approx (`Paper.thm_approx`)

The exact statements follow because a circuit that computes a polynomial approximates it with no error
(`Nc.Computes.approximates`).
-/

namespace Solution

open Statement

universe u

/-- The main theorem for approximate circuits (Theorem thm:approx); a `p` that is neither zero nor prime
is the characteristic of no field. -/
theorem mainTheoremApprox : MainTheoremApprox.{u} := by
  obtain ⟨c, hc, h⟩ := Paper.thm_approx.{u}.1
  refine ⟨c, hc, fun p => ?_⟩
  by_cases hp : p = 0 ∨ p.Prime
  · exact h p hp
  · exact ⟨0, fun F _ _ => absurd (CharP.char_is_prime_or_zero F p).symm hp⟩

/-- Over every field VNP is not contained in the closure of VP (Theorem thm:approx). -/
theorem separationClosure : SeparationClosure.{u} := fun F _ h =>
  Paper.thm_approx.{u}.2 F fun _ hg => h hg

/-- The main theorem (Theorem thm:allfields), from `mainTheoremApprox`: exact circuits approximate. -/
theorem mainTheorem : MainTheorem.{u} := by
  obtain ⟨c, hc, h⟩ := mainTheoremApprox.{u}
  refine ⟨c, hc, fun p => ?_⟩
  obtain ⟨m₀, hm⟩ := h p
  exact ⟨m₀, fun F _ _ m hm' s => ⟨fun hs => (hm F m hm' s).1 (Nc.Computes.approximates hs),
    fun h2 hs => (hm F m hm' s).2 h2 (Nc.Computes.approximates hs)⟩⟩

/-- VP is a proper subset of VNP over every field (Corollary cor:allclasses), from `separationClosure`:
VP is contained in its closure, so VNP ⊆ VP would give VNP ⊆ closure of VP. -/
theorem separation : Separation.{u} := fun F _ =>
  ⟨Paper.vp_subset_vnp F, fun h => separationClosure F fun _ hf =>
    let ⟨a, ha⟩ := h hf
    ⟨a, fun n => ⟨(ha n).1, (ha n).2.1, Nc.Computes.approximates (ha n).2.2⟩⟩⟩

/-- The special case in the main text of the paper: the real numbers and the permanent (Theorem thm:main),
from `mainTheorem` at p = 0. -/
theorem permanent_over_real : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ,
    Computes (perm ℝ m) s → Beyond c m s := by
  obtain ⟨c, hc, h⟩ := mainTheorem.{0}
  obtain ⟨m₀, hm⟩ := h 0
  exact ⟨c, hc, m₀, fun m hm' s hs => (hm ℝ m hm' s).2 (by norm_num) hs⟩

end Solution
