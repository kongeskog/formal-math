/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.PutDef
import Nc.Cut.Units
import Nc.Plus.UnitBits

/-!
# Comparing the units of a string with the contents of a store
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

/-- The contents at the keys are the values of `u`. -/
def Fits (keys : List (List Bool)) (u : ℕ → List Bool) (t : Tree) : Prop :=
  ∀ i (h : i < keys.length), tget keys[i] t = ofBits (u i)

theorem fits_cons (k : List Bool) (ks : List (List Bool)) (u : ℕ → List Bool) (t : Tree) :
    Fits (k :: ks) u t ↔ tget k t = ofBits (u 0) ∧ Fits ks (fun i => u (i + 1)) t := by
  constructor
  · exact fun h => ⟨h 0 (by simp), fun i hi => h (i + 1) (by simpa using hi)⟩
  · rintro ⟨h0, h1⟩ i hi
    cases i with
    | zero => exact h0
    | succ i => exact h1 i (by simpa using hi)

theorem padTake_eq (ub : ℕ) (r : List Bool) :
    padTake ub r = List.ofFn fun b : Fin ub => r.getD b false := by
  apply List.ext_getElem
  · simp only [padTake, List.length_append, List.length_take, List.length_replicate, List.length_ofFn]
    omega
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getD_eq_getElem?_getD]
    simp only [padTake]
    -- by cases on `i < r.length`: inside the taken part, or inside the padding of `false`s
    grind

open Classical in
theorem putL_gen {ub : ℕ} (hub : 0 < ub) (keys : List (List Bool)) (r : List Bool) (t : Tree) :
    putL ub keys r t = if (r.length + ub - 1) / ub = keys.length ∧
      Fits keys (fun k => List.ofFn fun b : Fin ub => r.getD (k * ub + b) false) t then [t] else []
          := by
  induction keys generalizing r with
  | nil =>
    simp only [putL, List.length_nil]
    refine if_congr ?_ rfl rfl
    rw [Nat.div_eq_zero_iff, ← List.length_eq_zero_iff]
    simp only [Fits, List.length_nil, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true, and_true]
    omega
  | cons k ks ih =>
    rw [putL]
    by_cases hr : r = []
    · subst hr
      rw [if_neg (by simp), if_neg]
      rintro ⟨h, -⟩
      rw [List.length_nil, zero_add, Nat.div_eq_of_lt (by omega)] at h
      simp at h
    · rw [ih, ← ite_and]
      have hl : 0 < r.length := List.length_pos_iff.2 hr
      have hc : (r.length + ub - 1) / ub = ((r.drop ub).length + ub - 1) / ub + 1 := by
        rw [List.length_drop]
        rcases le_or_gt ub r.length with h | h
        · have e1 : r.length + ub - 1 = (r.length - ub + ub - 1) + ub := by omega
          rw [e1, Nat.add_div_right _ hub]
        · have e1 : r.length - ub + ub - 1 = ub - 1 := by omega
          have e2 : r.length + ub - 1 = r.length - 1 + ub := by omega
          rw [e1, e2, Nat.add_div_right _ hub, Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
      have hu : (fun i => List.ofFn fun b : Fin ub => (r.drop ub).getD (i * ub + b) false) =
          fun i => List.ofFn fun b : Fin ub => r.getD ((i + 1) * ub + b) false := by
        funext i
        congr 1
        funext b
        simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
        congr 2
        ring
      refine if_congr ?_ rfl rfl
      rw [fits_cons, hc, List.length_cons, hu, zero_mul, padTake_eq]
      simp only [zero_add, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨⟨-, h1⟩, h2, h3⟩
        exact ⟨h2, h1.symm, h3⟩
      · rintro ⟨h2, h1, h3⟩
        exact ⟨⟨hr, h1.symm⟩, h2, h3⟩

open Classical in
theorem putL_eq {ub : ℕ} (hub : 0 < ub) (keys : List (List Bool)) (L : List Bool) (t : Tree) :
    putL ub keys (L ++ [true]) t = if ucount ub L = keys.length ∧
      Fits keys (fun k => uwBits (unitsOf ub L k)) t then [t] else [] := by
  rw [putL_gen hub]
  have hc : ((L ++ [true]).length + ub - 1) / ub = ucount ub L := by
    have e : (L ++ [true]).length + ub - 1 = L.length + ub := by simp
    rw [e, Nat.add_div_right _ hub, ucount]
  rw [hc]
  refine if_congr (and_congr_right fun h => forall₂_congr fun i hi => ?_) rfl rfl
  have : uwBits (unitsOf ub L i) = List.ofFn fun b : Fin ub => (L ++ [true]).getD (i * ub + b) false
      := by
    rw [unitsOf, if_pos (by omega)]
    rfl
  show _ = ofBits (List.ofFn fun b : Fin ub => (L ++ [true]).getD (i * ub + b) false) ↔
    _ = ofBits (uwBits (unitsOf ub L i))
  rw [this]

end Nc.Grp
