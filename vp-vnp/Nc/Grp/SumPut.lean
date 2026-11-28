/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.PutSum
import Nc.Grp.GroupProg
import Nc.Grp.SumSim

/-!
# Comparing several strings; a script as the product of its instructions
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

/-- The units of several strings are the contents at their keys. -/
def FitsAll (ub : ℕ) (P : List (List (List Bool) × List Bool)) (t : Tree) : Prop :=
  ∀ p ∈ P, ucount ub p.2 = p.1.length ∧ Fits p.1 (fun i => uwBits (unitsOf ub p.2 i)) t

open Classical in
theorem putsL_eq {ub : ℕ} (hub : 0 < ub) (P : List (List (List Bool) × List Bool)) (t : Tree) :
    putsL ub (P.map Prod.fst) (P.map fun p => p.2 ++ [true]) t =
      if FitsAll ub P t then [t] else [] := by
  induction P with
  | nil => simp [putsL, FitsAll]
  | cons p P ih =>
    rw [List.map_cons, List.map_cons, putsL, List.headD_cons, List.tail_cons, putL_eq hub]
    by_cases hp : ucount ub p.2 = p.1.length ∧ Fits p.1 (fun i => uwBits (unitsOf ub p.2 i)) t
    · rw [if_pos hp, List.flatMap_cons, List.flatMap_nil, List.append_nil, ih]
      exact if_congr (by simp [FitsAll, hp]) rfl rfl
    · rw [if_neg hp, if_neg fun h => hp (h p List.mem_cons_self)]
      rfl

/-- The first numbers. -/
theorem filter_finRange {U c : ℕ} (h : c ≤ U) :
    (List.finRange U).filter (fun k => k.1 < c) = List.ofFn fun i : Fin c => Fin.castLE h i := by
  have h1 : Function.Injective (List.map (Fin.val : Fin U → ℕ)) := List.map_injective_iff.2 Fin.val_injective
  apply h1
  have h2 : ((List.finRange U).filter (fun k => k.1 < c)).map Fin.val = (List.range U).filter (fun k => k < c) := by
    rw [← List.map_coe_finRange_eq_range, List.filter_map]
    rfl
  have h3 : (List.range U).filter (fun k => k < c) = List.range c := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [List.range_add, List.filter_append]
    have e1 : (List.range c).filter (fun k => k < c) = List.range c :=
      List.filter_eq_self.2 fun k hk => by simpa using hk
    have e2 : ((List.range d).map (c + ·)).filter (fun k => k < c) = [] :=
      List.filter_eq_nil_iff.2 fun k hk => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hk
        simp
    rw [e1, e2, List.append_nil]
  rw [h2, h3, List.map_ofFn]
  apply List.ext_getElem
  · simp
  · intro i h4 h5
    simp

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}

theorem wsum_script_cons (T ub : ℕ) (i : Ins) (l : List Ins) (t : Tree) (Ψ : Tree → A) :
    wsum (scriptSem θ mu cb kinds T ub (i :: l) t) Ψ = wsum (insSem θ mu cb kinds T ub i t) fun t' =>
      wsum (scriptSem θ mu cb kinds T ub l t') Ψ := by
  rw [scriptSem, foldL, wsum_bindW]
  rfl

theorem wsum_script_nil (T ub : ℕ) (t : Tree) (Ψ : Tree → A) :
    wsum (scriptSem (S := S) θ mu cb kinds T ub [] t) Ψ = Ψ t := by
  rw [scriptSem, foldL, wsum_single]

theorem wsum_script_append (T ub : ℕ) (l l' : List Ins) (t : Tree) (Ψ : Tree → A) :
    wsum (scriptSem θ mu cb kinds T ub (l ++ l') t) Ψ =
      wsum (scriptSem θ mu cb kinds T ub l t) fun t' =>
        wsum (scriptSem θ mu cb kinds T ub l' t') Ψ :=
  foldL_append _ _ _ _ _

/-- A list whose results are all `t`. -/
theorem wsum_out {Q : List (A × Tree)} {t : Tree} (h : ∀ q ∈ Q, q.2 = t) (Ψ : Tree → A) :
    wsum Q Ψ = wsum Q (fun _ => 1) * Ψ t := by
  unfold wsum
  rw [← List.sum_map_mul_right]
  congr 1
  refine List.map_congr_left fun q hq => ?_
  rw [h q hq, mul_one]

/-- The instructions do not change the trie: the sum of a script is the product of the sums of its
instructions. -/
theorem wsum_script_prod (T ub : ℕ) (l : List Ins) (t : Tree) (Ψ : Tree → A) :
    wsum (scriptSem θ mu cb kinds T ub l t) Ψ =
      (l.map fun i => wsum (insSem θ mu cb kinds T ub i t) fun _ => 1).prod * Ψ t := by
  induction l with
  | nil => rw [wsum_script_nil, List.map_nil, List.prod_nil, one_mul]
  | cons i l ih =>
    rw [wsum_script_cons, wsum_out (insSem_out mu cb kinds), ih, List.map_cons,
      List.prod_cons, mul_assoc]

end Nc.Grp
