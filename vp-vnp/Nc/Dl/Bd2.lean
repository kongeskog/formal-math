/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Bd1

/-!
# Bounds for the last steps and the templates
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

variable {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) {m mb : ℕ}
  (tab : SlpTab P grp D pS) (pt : Fin K → Tree) (qn : Q → ℕ) (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D)

/-- The states after the steps 1 to 8. -/
theorem mem_steps18 (hK : 0 < K) [Nonempty Q] [Nonempty (Fin U1)] {σ : List Bool → Tree}
    (hσ : σ ∈ execAll m (steps18 C tab qn i e hU0 hU1) (byPath C.nm (S0 pt))) :
    ∃ (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1)
      (st : NmT S M U0 U1 pS → Tree), tab.valid n ∧ (∀ x, P.good n o x) ∧ Mid C tab pt qn q ρ n o st ∧
      σ = byPath C.nm st := by
  classical
  obtain ⟨st, hf, hs⟩ := sum_steps18 (m := m) C tab pt qn i e hU0 hU1 hK
  by_contra hno
  have h := hs ℤ fun σ' => if σ' = σ then 1 else 0
  have hR : (∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K), ∑ n : NN K U0, ∑ o : M.N → Fin U1,
          if ValidRows ρ ∧ tab.valid n ∧ ∀ x, P.good n o x then
            (if byPath C.nm (st q ρ n o) = σ then (1 : ℤ) else 0) else 0
        else 0) = 0 := by
    refine Finset.sum_eq_zero fun q _ => ?_
    split_ifs
    swap
    · rfl
    refine Finset.sum_eq_zero fun ρ _ => Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun o _ => ?_
    -- both conditions together give the witness that `hno` excludes (`hf`, `h5.2`, `h6`)
    grind
  rw [hR] at h
  have hpos : (0 : ℤ) < ((execAll m (steps18 C tab qn i e hU0 hU1) (byPath C.nm (S0 pt))).map
      fun σ' => if σ' = σ then (1 : ℤ) else 0).sum := by
    refine lt_of_lt_of_le (b := (if σ = σ then (1 : ℤ) else 0)) (by simp) ?_
    refine List.single_le_sum (fun x hx => ?_) _ (List.mem_map.2 ⟨σ, hσ, rfl⟩)
    obtain ⟨σ', -, rfl⟩ := List.mem_map.1 hx
    split_ifs <;> norm_num
  omega

section Nine

variable {C} {Lc : ℕ} (hnm : ∀ y, (C.nm y).length ≤ Lc)

include hnm

/-- The cost of the steps 9. -/
theorem cost9 {q : Fin (K + 1) → Q} {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : NN K U0} {o : M.N → Fin U1}
    {st : NmT S M U0 U1 pS → Tree} (hst : Mid C tab pt qn q ρ n o st) :
    ∃ I' : List DStep → (List Bool → Tree) → Prop, ∃ c' : DStep → ℕ,
      (∀ s sts σ, I' (s :: sts) σ → s.cost m mb σ ≤ c' s ∧ ∀ σ' ∈ s.exec m σ, I' sts σ') ∧
      I' (steps9 C) (byPath C.nm st) ∧ ((steps9 C).map fun s => c' s + 30).sum ≤
        Fintype.card (G.Uid (K + K) U0 M.N U1) * (90 * Lc + 230) +
        (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)).card * ((m + 1) * (60 * mb + 100)) := by
  classical
  refine ⟨fun rest σ => (∀ s ∈ rest, ∃ id : G.Uid (K + K) U0 M.N U1, s = DStep.bits (C.nm (.cut id)) (C.nm (.cont id))) ∧
    ∀ id, σ (C.nm (.cut id)) = st (.cut id), fun s => s.cost m mb (byPath C.nm st), ?_, ⟨?_, fun id => ?_⟩, ?_⟩
  · rintro s sts σ ⟨h1, h2⟩
    obtain ⟨id, rfl⟩ := h1 s List.mem_cons_self
    refine ⟨?_, fun σ' hσ' => ⟨fun s hs => h1 s (List.mem_cons_of_mem _ hs), fun id' => ?_⟩⟩
    · simp only [DStep.cost, h2, byPath_nm C.nm_inj]
      exact le_rfl
    · simp only [DStep.exec] at hσ'
      split_ifs at hσ' with hc
      · rw [List.mem_singleton] at hσ'
        rw [hσ', h2]
      · rw [List.mem_map] at hσ'
        obtain ⟨u, -, rfl⟩ := hσ'
        rw [Function.update_of_ne fun h => by simpa using C.nm_inj h, h2]
  · intro s hs
    rw [steps9, List.mem_map] at hs
    obtain ⟨id, -, rfl⟩ := hs
    exact ⟨id, rfl⟩
  · rw [byPath_nm C.nm_inj]
  · rw [steps9, List.map_map]
    have h1 : (((univ : Finset (G.Uid (K + K) U0 M.N U1)).toList.map ((fun s : DStep => s.cost m mb (byPath C.nm st) + 30) ∘
        fun id => DStep.bits (C.nm (.cut id)) (C.nm (.cont id))))).sum =
        ∑ id : G.Uid (K + K) U0 M.N U1, ((DStep.bits (C.nm (.cut id)) (C.nm (.cont id))).cost m mb (byPath C.nm st) + 30) :=
      Finset.sum_map_toList _ _
    rw [h1]
    calc ∑ id : G.Uid (K + K) U0 M.N U1, ((DStep.bits (C.nm (.cut id)) (C.nm (.cont id))).cost m mb (byPath C.nm st) + 30)
        ≤ ∑ id : G.Uid (K + K) U0 M.N U1, ((90 * Lc + 230) + if id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o)
            (P.cur n o E) then (m + 1) * (60 * mb + 100) else 0) := by
          refine Finset.sum_le_sum fun id _ => ?_
          have a1 := hnm (.cut id)
          have a2 := hnm (.cont id)
          obtain ⟨cc, h1, h2⟩ := hst.cut id
          rw [DStep.cost, byPath_nm C.nm_inj, h1]
          by_cases hc : id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)
          · rw [if_pos hc, if_neg (bit_ne_nil.2 (h2.2 hc))]
            omega
          · have : cc = false := by
              by_contra hcc
              exact hc (h2.1 (by simpa using hcc))
            rw [if_neg hc, this, if_pos (show bit false = .nil from rfl)]
            omega
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.card_univ, Finset.sum_ite_mem,
            Finset.univ_inter, Finset.sum_const, smul_eq_mul]

end Nine

end Nc.Dl
