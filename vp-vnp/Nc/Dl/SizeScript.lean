/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.SizeDeal
import Nc.Plus.Interface

/-!
# The size of a script
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

theorem excess_listTm (σ : List Bool → Tree) (B : ℕ) (ts : List Tm) :
    (listTm ts).excess σ B = (ts.map (Tm.excess σ B)).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [listTm, Tm.excess, ih]

theorem excess_catTm (σ : List Bool → Tree) (B : ℕ) (ts : List Tm) :
    (catTm ts).excess σ B = (ts.map (Tm.excess σ B)).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [catTm, Tm.excess, ih]

variable {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q] {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} {C : Codes S M U0 U1 D pS}
  {tab : SlpTab P grp D pS} {qn : Q → ℕ} {pt : Fin K → Tree} {q : Fin (K + 1) → Q}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : NN K U0} {o : M.N → Fin U1}
  {b : G.Uid (K + K) U0 M.N U1 → UW ub} {st : NmT S M U0 U1 pS → Tree} {tg : M.R → ℕ}
  {bT bub : List Bool} {gt : Fin mm → Tree} {d1 gp : Tree} {X Lc W : ℕ}

/-- **The size of a script**, as the expansion of its template in a final state. A value other
than a part or a content has size at most `19 * (X * Lc)`, so the template counts with its size
times that; a part is read for a base party of the group only, a content for a unit that the
group cuts. -/
theorem size_expand_instTm (hst : Final C tab qn pt q ρ n o b st) (H : SizeHyp C qn tg X Lc)
    (hd1 : ∀ d : Fin D, C.dt d = d1 ↔ d.1 = 1) (hgt : ∀ (d : Fin D) g, C.dt d = gt g ↔ d.1 = g.1)
    (hnum : ∀ y, P.num n o y ≤ X) (hpt : ∀ κ, (pt κ).size ≤ W + 1)
    (hb : ∀ id ∈ P.cur n o E, grp n o (G.hold0 M.np id) ≠ grp n o (G.hold1 M.np id) → b id ≠ none)
    (g : Fin mm) (hT : (instTm C tab tg bT bub gt d1 gp g).tree.size ≤ 740 * (X * Lc) ^ 3) :
    ((instTm C tab tg bT bub gt d1 gp g).expand (byPath C.nm st)).size ≤ 14800 * (X * Lc) ^ 4 +
      ((univ.filter fun p : Fin (K + K) => grp n o (Fin.castAdd A' p) = g).card * W +
      ((P.cur n o E).filter (Nc.Plus.OneIn (G.hold0 M.np) (G.hold1 M.np) (grp n o) g)).card *
        (4 * ub)) := by
  obtain ⟨f1, -, -, f4, -⟩ := H.facts
  have e : 740 * (X * Lc) ^ 3 * (20 * (X * Lc)) = 14800 * (X * Lc) ^ 4 := by ring
  refine (Tm.size_expand_le (byPath C.nm st) (19 * (X * Lc)) _).trans
    (Nat.add_le_add ((Nat.mul_le_mul hT (by omega)).trans_eq e) ?_)
  -- the values other than parts and contents are at most `19 * (X * Lc)`
  have en : ∀ k ≤ X, (num k).size - 19 * (X * Lc) = 0 := fun k hk => by
    rw [size_num]
    omega
  have hbody : ∀ p, (bodyTm C p).excess (byPath C.nm st) (19 * (X * Lc)) = 0 := fun p => by
    simp [bodyTm, gN, Tm.excess, excess_listTm, Function.comp_def, byPath_nm C.nm_inj, hst.flag,
      hst.kR, hst.kC, Nat.sub_eq_zero_of_le, size_flagT H, size_kRT H, size_kCT H]
  have hbase : ∀ p, (basesTm C p).excess (byPath C.nm st) (19 * (X * Lc)) ≤ W := fun p => by
    refine Fin.addCases (fun κ => ?_) (fun κ => ?_) p
    · simp [basesTm, baseTm, gN, Tm.excess, byPath_nm C.nm_inj, hbody, hst.dg, hst.q,
        Nat.sub_eq_zero_of_le, size_dgT H, en, H.hqn]
    · have := hpt κ
      simp only [basesTm, baseTm, gN, Fin.addCases_right, Tm.excess, byPath_nm C.nm_inj, hbody,
        hst.dg, hst.part, Nat.sub_eq_zero_of_le, size_dgT H]
      omega
  have hrole : ∀ r, (roleTm C tab tg d1 r).excess (byPath C.nm st) (19 * (X * Lc)) = 0 :=
    fun r => by
      simp [roleTm, slotTm, ifTm, gN, Tm.excess, excess_listTm, excess_catTm, Function.comp_def,
        byPath_nm C.nm_inj, hst.num, hst.ch, Nat.sub_eq_zero_of_le, size_chT H, en, hnum]
  -- the conditions
  have hg : ∀ p, (C.dt (tab.fn (tab.kgrp p) (n, o)) = gt g ↔ grp n o p = g) := fun p => by
    rw [hgt, tab.hgrp]
    exact Fin.ext_iff.symm
  have hcur : ∀ id, C.dt (tab.fn (tab.kcur id) (n, o)) = d1 ↔ id ∈ P.cur n o E := fun id => by
    rw [hd1, tab.hcur]
    split_ifs with hc <;> simp [hc]
  -- a content is read for a unit that the group cuts
  have hend : ∀ id, (endTm C tab gt d1 g id).excess (byPath C.nm st) (19 * (X * Lc)) ≤
      if id ∈ (P.cur n o E).filter (Nc.Plus.OneIn (G.hold0 M.np) (G.hold1 M.np) (grp n o) g) then
        4 * ub else 0 := fun id => by
    have hcont : id ∈ P.cur n o E → grp n o (G.hold0 M.np id) ≠ grp n o (G.hold1 M.np id) →
        (st (.cont id)).size ≤ 4 * ub + 1 := fun hc hne => by
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hb id hc hne)
      rw [hst.cont id v hv]
      simpa using size_ofBits (List.ofFn v)
    simp only [endTm, ifTm, oneTm, listTm, gN, Tm.excess, byPath_nm C.nm_inj, hst.slp, hg, hcur,
      Finset.mem_filter, Nc.Plus.OneIn]
    by_cases hc : id ∈ P.cur n o E
    · by_cases h0 : grp n o (G.hold0 M.np id) = g <;> by_cases h1 : grp n o (G.hold1 M.np id) = g
      · simp [hc, h0, h1]
      · have := hcont hc fun h => h1 (h ▸ h0)
        rw [if_pos hc, if_pos h0, if_neg h1, if_pos ⟨hc, Or.inl ⟨h0, h1⟩⟩]
        omega
      · have := hcont hc fun h => h0 (h.trans h1)
        rw [if_pos hc, if_neg h0, if_pos h1, if_pos ⟨hc, Or.inr ⟨h0, h1⟩⟩]
        omega
      · simp [hc, h0, h1]
    · simp [hc]
  -- the three lists of the script
  simp only [instTm, scriptTm, Tm.excess, excess_catTm, List.map_append, List.sum_append,
    List.map_map, Function.comp_def, ifTm, listTm, byPath_nm C.nm_inj, hst.slp, hg, hrole, zero_add,
    add_zero, ite_self, List.map_const', List.sum_replicate, smul_zero]
  refine Nat.add_le_add ?_ ?_
  · rw [← Fin.sum_univ_def, ← Finset.sum_filter]
    exact Finset.sum_le_card_nsmul _ _ W fun p _ => hbase p
  · rw [G.allIds, Finset.sum_map_toList]
    refine (Finset.sum_le_sum fun id _ => hend id).trans ?_
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]

end Nc.Dl
