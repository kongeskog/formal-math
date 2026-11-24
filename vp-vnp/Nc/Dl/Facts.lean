/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.G.Exact
import Nc.Cut.Facts

/-!
# Bounds that follow from one contributing choice

The numbers of units that a party holds at the beginning, and the outcomes of the moves.
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open Finset Nc.Cut Nc.G

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K U0 E U1 : ℕ} {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {ub : ℕ} {c : ℕ}
  {cb : Option Γ → Fin c → Bool}

/-- A party reads at most `T` letters in all. -/
theorem partyW_read_le {q : Fin (K + 1) → Q} {x : Fin K → List Γ} {R C : Option S → Fin (K + K) → List Γ}
    {p : Fin (K + K)} (h : partyW mu T q x p R C ≠ 0) : ∑ s, (cat (C s)).length ≤ T := by
  classical
  induction p using Fin.addCases with
  | left κ =>
    rw [partyW_block] at h
    split_ifs at h with hc
    swap
    · exact absurd rfl h
    refine le_trans ?_ (blockW_sum_le h)
    let f : Option S → Ch S Unit := fun s => s.elim (.inp ()) fun s => .tp s true
    have hf : ∑ s, (cat (C s)).length = ∑ s, (vec R C (f s)).length := by
      refine Finset.sum_congr rfl fun s _ => ?_
      cases s <;> simp [f, vec]
    have inj : Function.Injective f := by
      intro s s' e
      cases s <;> cases s' <;> simp [f] at e ⊢
      exact e
    rw [hf, ← Finset.sum_image (f := fun z : Ch S Unit => (vec R C z).length) (s := univ) (g := f)
      fun s _ s' _ e => inj e]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  | right κ =>
    rw [partyW_input] at h
    split_ifs at h with hc
    swap
    · exact absurd rfl h
    refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [cat_nil_of (hc.2.1 s), List.length_nil]

/-- The number of units that a party holds at the beginning. -/
theorem init_count {N : Type} [Fintype N] [DecidableEq N] {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
    (hx : ∀ κ, (x κ).length ≤ T) {ρ : Option S → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → ℕ} {p : Fin (K + K)}
    {y : G.Uid (K + K) U0 N U1 → UW ub} {R C : Option S → Fin (K + K) → List Γ} (h : G.InitOk ub cb ρ n p y R C)
    (hW : partyW mu T q x p R C ≠ 0) :
    ∑ b, (n p b + n b p) ≤ 2 * ((T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K)) := by
  have h1 : ∑ b, n p b ≤ (T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K) := by
    rw [Finset.sum_congr rfl fun b _ => ((h.2.1 b).1).symm]
    exact sum_ucount_le (partyW_sum_le hx hW)
  have h2 : ∑ b, n b p ≤ (T + (K + K) * (Fintype.card S + 1)) * c / ub + (K + K) := by
    rw [Finset.sum_congr rfl fun b _ => ((h.2.2 b).1).symm]
    exact sum_ucount_le (partyW_read_le hW)
  rw [Finset.sum_add_distrib]
  omega

end Nc.Dl
