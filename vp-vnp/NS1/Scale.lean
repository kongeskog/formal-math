/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Postpone

/-!
# One round: guess exponents, postpone, cut, accelerate
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- The cut at the scale `v ^ H`, for times up to `v ^ (H * α)`. -/
def CutAt (θ : List Bool → A) (H v α : ℕ) : Prop :=
  ∀ τ s, v ^ H ≤ τ → τ ≤ v ^ (H * α) → s * v ^ 48 ≤ τ → ∃ G, CutProg θ H v τ s G

theorem CutHyp.at {H C₀ v₀ v α : ℕ} (h : CutHyp θ H C₀ v₀) (hv : v₀ ≤ v) (hl : lg v ^ (C₀ * α) ≤ v) : CutAt θ H v α :=
  fun τ s => h v hv α τ s hl

theorem Plain.of_le {T T' : ℕ} {z : Tree} (h : Plain θ T z) (hT : T ≤ T') : Plain θ T' z :=
  ⟨h.1, fun r hr => ⟨(h.2 r hr).1, (h.2 r hr).2.trans hT⟩⟩

/-- A constant: it bounds the sizes of the fixed programs. -/
def cst : ℕ := WF.code.size + UF.code.size + 2000

theorem cst_def : cst = WF.code.size + UF.code.size + 2000 := rfl

theorem size_LP (D : Tree) : (LP D).code.size ≤ D.size + 300 := by
  simp only [LP, Fm.code, Tree.size, size_num]
  omega

theorem pow_le_pow {u a b : ℕ} (hu : 1 ≤ u) (h : a ≤ b) : u ^ a ≤ u ^ b := Nat.pow_le_pow_right hu h

/-! Arithmetic of the step from one scale to the next (`Paper/ApproxRound`). -/

theorem pow_big {u : ℕ} (hu : 2000 ≤ u) (a : ℕ) : 2000 * u ^ a ≤ u ^ (a + 1) := by
  rw [pow_succ']
  exact Nat.mul_le_mul_right _ hu

theorem mul_sub_scale (α h c : ℕ) : α * (16 * h - c) = 16 * (h * α) - c * α := by
  rw [Nat.mul_sub]
  congr 1 <;> ring

/-- A trie of powers with `B + 1 ≤ X` has few nodes compared to `u`. -/
theorem nds_expand_le {R' : Type} [CommRing R'] {K : KT R'} {u m B X c : ℕ} (hK : K.nds ≤ u ^ m)
    (hB : B + 1 ≤ X) (hXu : 1000 * X ^ 3 ≤ u) (hc : c * X ^ 2 ≤ 1000 * X ^ 3) :
    (K.expand B).nds * (c * X) ≤ 2 * u ^ (m + 1) :=
  calc (K.expand B).nds * (c * X) ≤ K.nds * (2 * X) * (c * X) :=
        Nat.mul_le_mul_right _ ((KT.nds_expand B K).trans (Nat.mul_le_mul_left _ (by omega)))
    _ = K.nds * (2 * (c * X ^ 2)) := by ring
    _ ≤ u ^ m * (2 * u) := Nat.mul_le_mul hK (by omega)
    _ = 2 * u ^ (m + 1) := by rw [pow_succ]; ring

/-- The programs of the rounds stay below `u ^ (4 * h * α)`. -/
theorem size_rounds {h α u n : ℕ} (hh : 17 ≤ h) (hα : 5 ≤ α) (hu : 2000 ≤ u) (hn : n ≤ u) :
    u + n * (u ^ (h * α + 2) + u ^ (16 * h + 1)) ≤ u ^ (4 * h * α) := by
  have hh1 : 5 * h ≤ h * α := by rw [Nat.mul_comm h α]; exact Nat.mul_le_mul_right _ hα
  have e4 : 4 * h * α = 4 * (h * α) := by ring
  obtain ⟨a, ha⟩ : ∃ a, 4 * h * α = a + 1 := ⟨4 * h * α - 1, by omega⟩
  have t1 : n * (u ^ (h * α + 2) + u ^ (16 * h + 1)) ≤ u * (u ^ (h * α + 2) + u ^ (16 * h + 1)) :=
    Nat.mul_le_mul_right _ hn
  have t2 : u * (u ^ (h * α + 2) + u ^ (16 * h + 1)) = u ^ (h * α + 3) + u ^ (16 * h + 2) := by
    rw [mul_add, ← pow_succ', ← pow_succ']
  have t3 : u ^ (h * α + 3) ≤ u ^ a := pow_le_pow (by omega) (by omega)
  have t4 : u ^ (16 * h + 2) ≤ u ^ a := pow_le_pow (by omega) (by omega)
  have t5 : u ^ 1 ≤ u ^ a := pow_le_pow (by omega) (by omega)
  have t6 := pow_big hu a
  rw [pow_one] at t5
  rw [ha]
  omega

end NS1
