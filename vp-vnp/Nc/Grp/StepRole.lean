/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.StepBase
import Nc.Grp.SumRole

/-!
# The instruction of a role
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {A' K E U0 U1 ub c T : ℕ} {Gr : Type} [DecidableEq Gr]
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}
  {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {key : Cell M U0 U1 → List Bool} {tg : M.R → ℕ}

/-- The keys of the new units of a channel. -/
noncomputable def kNew (o : M.N → Fin U1) (key : Cell M U0 U1 → List Bool) (r : M.R) (ν : (M.kind r.1).CnAt r.2) :
    List (List Bool) := ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k)

theorem kNew_eq (r : M.R) (ν : (M.kind r.1).CnAt r.2) : kNew o key r ν =
    ((List.finRange U1).filter fun k => k.1 < (o ⟨r.1, ν.1⟩).1 + 1).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k) := by
  unfold kNew
  simp only [Nat.lt_succ_iff]
  rfl

/-- What a role compares. -/
noncomputable def PN (o : M.N → Fin U1) (key : Cell M U0 U1 → List Bool) (r : M.R) {B : ℕ}
    (f : Fin B → Bk (M.kind r.1) r.2) : List (List (List Bool) × List Bool) :=
  (cnList (M.kind r.1) r.2).map fun ν => (kNew o key r ν, chS (M.kind r.1) r.2 f ν)

theorem mem_cnList {L : G.Law A} {p : L.Ro} (ν : L.CnAt p) : ν ∈ cnList L p := Finset.mem_toList.2 (mem_univ ν)

theorem getD_append_replicate (l : List Bool) (m k : ℕ) : (l ++ List.replicate m false).getD k false = l.getD k false := by
  rcases lt_or_ge k l.length with h | h
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ h, List.getD_eq_default l _ h]
    simp

/-- Choices in all blocks. -/
def bkEquiv (L : Law A) (p : L.Ro) (B : ℕ) : (Fin B → Bk L p) ≃
    Σ i : Fin B → L.I, ∀ k, ∀ ν : L.CnAt p, Fin (L.len (i k) ν) → Bool where
  toFun f := ⟨fun k => (f k).1, fun k => (f k).2⟩
  invFun z k := ⟨z.1 k, z.2 k⟩
  left_inv _ := rfl
  right_inv _ := rfl

open Classical in
/-- **The instruction of a role** sums to the table of the role at the contents of the trie. -/
theorem wsum_roleIns (hub : 0 < ub) {r : M.R} (hkind : kinds[tg r]? = some ⟨M.kind r.1, r.2⟩)
    (htab : ∀ i y h, ∃ e : WE, e.val θ = (M.kind r.1).tab r.2 i y h) {t : Tree} {σ : Cell M U0 U1 →
        UW ub}
    (h : Rep ub key t σ)
    (hσ : ∀ (ν : (M.kind r.1).CnAt r.2) (k : Fin U1), (o ⟨r.1, ν.1⟩).1 < k.1 → σ (M.rp r, .new ⟨r.1,
        ν.1⟩ k) = none) :
    wsum (insSem (S := S) θ mu cb kinds T ub (roleIns P n o key tg r) t) (fun _ => 1) =
      G.roleAt P n o r fun id => σ (M.rp r, id) := by
  rw [roleIns, insSem, hkind]
  simp only
  have hct : ∀ id, (tget (key (M.rp r, id)) t).path = uwBits (σ (M.rp r, id)) := by
    intro id
    rw [h, path_ofBits]
  have hpres : (∀ es ∈ (univ : Finset ((M.kind r.1).SlAt r.2)).toList.map (fun e =>
      ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse), ∀ k ∈ es, (tget k t).path ≠ []) ↔
      ∀ e : (M.kind r.1).SlAt r.2, ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, σ (M.rp r, id) ≠ none := by
    simp only [List.forall_mem_map, Finset.mem_toList, mem_univ, true_imp_iff, List.mem_reverse]
    refine forall_congr' fun e => forall₂_congr fun id _ => ?_
    rw [hct, uwBits_ne_nil hub]
  rw [G.roleAt, G.role]
  by_cases hp : ∀ e : (M.kind r.1).SlAt r.2, ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, σ (M.rp r, id) ≠ none
  swap
  · rw [roleSem, if_neg fun h => hp (hpres.1 h), wsum_nil, if_neg hp]
  rw [roleSem, if_pos (hpres.2 hp), wsum_bindW, wsum_role _ _ htab, if_pos hp]
  have hsig := Finset.sum_sigma' (univ : Finset (Fin (P.num n o r.1 * ub) → (M.kind r.1).I)) (fun _
      => univ)
    (fun i (g : ∀ k, ∀ ν : (M.kind r.1).CnAt r.2, Fin ((M.kind r.1).len (i k) ν) → Bool) =>
      if ∀ ν : (M.kind r.1).CnAt r.2, ChOk ⟨r.1, ν.1⟩ (o ⟨r.1, ν.1⟩).1
          (chString (M.kind r.1).lab (fun j => (M.kind r.1).len j ν) i fun k => g k ν) (fun id => σ
              (M.rp r, id))
        then ∏ k : Fin (P.num n o r.1 * ub), (M.kind r.1).tab r.2 (i k) (fun e =>
          (slotBits (P.num n o r.1) (P.ids n o ⟨r.1, e.1⟩) fun id => σ (M.rp r, id)).getD k false)
              (g k) else 0)
  rw [hsig, Finset.univ_sigma_univ]
  refine Fintype.sum_equiv (bkEquiv (M.kind r.1) r.2 (P.num n o r.1 * ub)) _ _ fun f => ?_
  -- the streams
  have hins : ∀ e : (M.kind r.1).SlAt r.2, ∀ k : ℕ,
      ((((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map (fun e =>
        ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse)).map fun es =>
          es.reverse.flatMap fun k => (tget k t).path).getD (slIdx (M.kind r.1) r.2 e) []).getD k false =
      (slotBits (P.num n o r.1) (P.ids n o ⟨r.1, e.1⟩) fun id => σ (M.rp r, id)).getD k false := by
    intro e k
    have hlt : (slIdx (M.kind r.1) r.2 e : ℕ) < ((univ : Finset ((M.kind r.1).SlAt r.2)).toList).length :=
      (slIdx (M.kind r.1) r.2 e).2
    have hget : ((univ : Finset ((M.kind r.1).SlAt r.2)).toList)[(slIdx (M.kind r.1) r.2 e : ℕ)]'hlt = e :=
      List.getElem_idxOf hlt
    have hlist : (((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map (fun e =>
        ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse)).map fun es =>
          es.reverse.flatMap fun k => (tget k t).path).getD (slIdx (M.kind r.1) r.2 e) [] =
        (P.ids n o ⟨r.1, e.1⟩).flatMap fun id => uwBits (σ (M.rp r, id)) := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_map]; exact hlt), List.getElem_map,
        List.getElem_map, hget, List.reverse_reverse, List.flatMap_map]
      exact List.flatMap_congr fun id _ => hct id
    rw [hlist, slotBits, getD_append_replicate]
  -- the strings
  have hkeys : ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k)) =
      (PN o key r f).map Prod.fst := by
    rw [PN, List.map_map]
    rfl
  have hstr : (List.ofFn fun j => ((chS (M.kind r.1) r.2 f ((cnList (M.kind r.1) r.2).get j)).reverse).reverse ++ [true]) =
      (PN o key r f).map fun z => z.2 ++ [true] := by
    rw [PN, List.map_map]
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp
  simp only [hins]
  rw [hkeys, hstr, putsL_eq hub]
  have hfit : FitsAll ub (PN o key r f) t ↔ ∀ ν : (M.kind r.1).CnAt r.2, ChOk ⟨r.1, ν.1⟩ (o ⟨r.1,
      ν.1⟩).1
      (chS (M.kind r.1) r.2 f ν) (fun id => σ (M.rp r, id)) := by
    have hν : ∀ ν : (M.kind r.1).CnAt r.2, (ucount ub (chS (M.kind r.1) r.2 f ν) = (kNew o key r
        ν).length ∧
        Fits (kNew o key r ν) (fun i => uwBits (unitsOf ub (chS (M.kind r.1) r.2 f ν) i)) t) ↔
        ChOk ⟨r.1, ν.1⟩ (o ⟨r.1, ν.1⟩).1 (chS (M.kind r.1) r.2 f ν) (fun id => σ (M.rp r, id)) := by
      intro ν
      rw [kNew_eq]
      exact fits_iff hub h (by have := (o ⟨r.1, ν.1⟩).2; omega) (fun k => (M.rp r, .new ⟨r.1, ν.1⟩
          k))
        (fun k hk => hσ ν k hk) _
    rw [FitsAll, PN, List.forall_mem_map]
    exact ⟨fun h ν => (hν ν).1 (h ν (mem_cnList ν)), fun h ν _ => (hν ν).2 (h ν)⟩
  by_cases hc : FitsAll ub (PN o key r f) t
  · rw [if_pos hc]
    simp only [encT, List.map_cons, List.map_nil, wsum_single, mul_one]
    exact (if_pos (hfit.1 hc)).symm
  · rw [if_neg hc]
    simp only [encT, List.map_nil, wsum_nil, mul_zero]
    exact (if_neg fun h => hc (hfit.2 h)).symm

end Nc.Grp
