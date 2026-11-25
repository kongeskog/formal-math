/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Acc.Prog
import NS1.Main

/-!
# The size of the program of low degree
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

section Size

theorem size_quote (c : Tree) : (Fm.quote c).code.size = c.size + 2 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_id : Fm.id.code.size = 5 := by
  simp only [Fm.code, Tree.size, size_num]

theorem size_hd (a : Fm) : (Fm.hd a).code.size = a.code.size + 6 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_tl (a : Fm) : (Fm.tl a).code.size = a.code.size + 8 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_cons (a b : Fm) : (Fm.cons a b).code.size = a.code.size + b.code.size + 11 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_ite (a b c : Fm) : (Fm.ite a b c).code.size = a.code.size + b.code.size + c.code.size + 14 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_run (a b : Fm) : (Fm.run a b).code.size = a.code.size + b.code.size + 15 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_guess : Fm.guess.code.size = 17 := by
  simp only [Fm.code, Tree.size, size_num]

theorem size_leaf (a : Fm) : (leaf a).code.size = a.code.size + 16 := by
  simp only [leaf, Fm.code, Tree.size, size_num]; ring

theorem size_app (p : Tree) (e : Fm) : (app p e).code.size = p.size + e.code.size + 17 := by
  rw [app, size_run, size_quote]; ring

theorem size_lett (e b : Fm) : (lett e b).code.size = b.code.size + e.code.size + 17 := by
  rw [lett, size_run, size_quote]; ring

theorem size_gwd (M : ℕ) : (gwd M).code.size = 50 * M + 3 := by
  induction M with
  | zero => simp [gwd, size_quote, Tree.size]
  | succ M ih =>
    rw [gwd, size_cons, size_ite, size_guess, size_quote, size_quote, ih]
    simp only [one, Tree.size]
    ring

theorem size_walkF (m : ℕ) : (walkF m).code.size = (stepW.code.size + 17) * m + 5 := by
  induction m with
  | zero => simp [walkF, size_id]
  | succ m ih =>
    rw [walkF, size_lett, ih]
    ring

theorem size_pairsF (m : ℕ) (l : Fm) : (pairsF m l).code.size = l.code.size + (2 * pairB.code.size + 30) * m := by
  induction m generalizing l with
  | zero => simp [pairsF]
  | succ m ih =>
    rw [pairsF, ih, size_app, size_cons, size_quote]
    ring

/-- The size of the program. -/
theorem size_accF : ∃ c : ℕ, ∀ (M m d : ℕ) (out : List Bool), out.length = M →
    (accF M m d out).code.size ≤ c * (M + m + 1) + 2 * d := by
  generalize hc1 : stepW.code.size = c1
  generalize hc2 : leafB.code.size = c2
  generalize hc3 : intB.code.size = c3
  generalize hc4 : pairB.code.size = c4
  generalize hc5 : (wordB lt0 lt1).code.size = c5
  generalize hc6 : lt2.size = c6
  generalize hc7 : (ofBits [true, false]).size = c7
  generalize hc8 : Fm.fail.code.size = c8
  have hloop : ∀ M m, (loopF M m).code.size ≤ 200 * M + (c1 + 17) * m + (c2 + c3 + c8 + 500) := by
    intro M m
    rw [loopF, size_ite, size_ite, leafF, intF, size_lett, size_ite, size_lett, size_cons, size_cons, size_cons, size_lett,
      size_cons, size_gwd, size_walkF]
    simp only [size_hd, size_tl, size_id, size_guess, size_quote, Tree.size, hc1, hc2, hc3, hc8]
    omega
  refine ⟨2 * (200 + c1 + 17 + c2 + c3 + c8 + 500) + (2 * c4 + 30) + 2 * c5 + c6 + c7 + 500, fun M m d out ho => ?_⟩
  have h1 := hloop M m
  have h2 := size_ofBits out
  rw [ho] at h2
  rw [accF, size_ite, size_leaf, size_app, size_cons, size_cons, size_cons, treeF, size_hd, size_pairsF, size_app, size_cons,
    size_cons]
  simp only [size_guess, size_quote, size_id, size_num, hc4, hc5, hc6, hc7, List.map_cons, List.map_nil, listT,
    Tree.size]
  have h3 : (c1 + 17) * m ≤ (c1 + 17) * (M + m + 1) := Nat.mul_le_mul_left _ (by omega)
  have h4 : (2 * c4 + 30) * m ≤ (2 * c4 + 30) * (M + m + 1) := Nat.mul_le_mul_left _ (by omega)
  have h5 : c2 + c3 + c8 + 500 ≤ (c2 + c3 + c8 + 500) * (M + m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h6 : 2 * c5 + c6 + c7 + 400 ≤ (2 * c5 + c6 + c7 + 400) * (M + m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h7 : (2 * (200 + c1 + 17 + c2 + c3 + c8 + 500) + (2 * c4 + 30) + 2 * c5 + c6 + c7 + 500) * (M + m + 1) =
      400 * (M + m + 1) + 2 * ((c1 + 17) * (M + m + 1)) + 2 * ((c2 + c3 + c8 + 500) * (M + m + 1)) +
      (2 * c4 + 30) * (M + m + 1) + (2 * c5 + c6 + c7 + 400) * (M + m + 1) + 100 * (M + m + 1) := by ring
  omega

end Size

end NS1
