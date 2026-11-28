/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.GrpSteps

/-!
# The tables of the parties of a group
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open Finset Nc.G Nc.Cut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K E U0 U1 ub c cap : ℕ} {Gr : Type} [DecidableEq Gr]
  {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {cb : Option Γ → Fin c → Bool}
  {M : Sys F (K + K + A') E} {P : G.Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}

/-- A cell of the group is a cell of a base party, for a unit that it writes or reads, or a cell of
a role, for a new unit. -/
theorem dom_cases {c : Cell M U0 U1} (hc : c ∈ dom n o grp g) :
    (∃ p b, ∃ i : Fin U0, grp (Fin.castAdd A' p) = g ∧ i.1 < (n p b).1 ∧
      c = (Fin.castAdd A' p, .init p b i)) ∨
    (∃ p b, ∃ i : Fin U0, grp (Fin.castAdd A' p) = g ∧ i.1 < (n b p).1 ∧
      c = (Fin.castAdd A' p, .init b p i)) ∨
    ∃ (r : M.R) (ν : (M.kind r.1).CnAt r.2) (i : Fin U1), grp (M.rp r) = g ∧ i ≤ o ⟨r.1, ν.1⟩ ∧
      c = (M.rp r, .new ⟨r.1, ν.1⟩ i) := by
  obtain ⟨a, id⟩ := c
  obtain ⟨h1, h2, h3⟩ : grp a = g ∧ id ∈ G.Plan.seenAt n o E ∧
      Holds (G.hold0 M.np) (G.hold1 M.np) a id := mem_dom.1 hc
  cases id with
  | init a' b' k =>
    have hk := G.Plan.init_mem_seenAt.1 h2
    rcases h3 with h3 | h3
    · have h3 : a = Fin.castAdd A' a' := h3
      subst h3
      exact Or.inl ⟨a', b', k, h1, hk, rfl⟩
    · have h3 : a = Fin.castAdd A' b' := h3
      subst h3
      exact Or.inr (Or.inl ⟨b', a', k, h1, hk, rfl⟩)
  | new ν k =>
    have hk := (G.Plan.new_mem_seenAt.1 h2).2
    obtain ⟨d, rfl⟩ : ∃ d, a = M.rp (M.nr ν d) := by
      rcases h3 with h3 | h3
      exacts [⟨false, h3⟩, ⟨true, h3⟩]
    exact Or.inr (Or.inr ⟨M.nr ν d, ⟨ν.2, by cases d <;> simp [Sys.nr, Law.cnEnd]⟩, k, h1, hk, rfl⟩)

/-- The product of the tables of the base parties and of the roles of a group is the product of the
tables of its parties. -/
theorem prod_tab (y : Cell M U0 U1 → UW ub) :
    ((baseList grp g).map fun p =>
      G.tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p
        fun id => y (Fin.castAdd A' p, id)).prod *
      ((roleList grp g M).map fun r => G.roleAt P n o r fun id => y (M.rp r, id)).prod =
      ∏ a ∈ univ.filter (fun a => grp a = g), G.tabFinal mu T cb P q x ρ n o a fun id => y (a, id) := by
  classical
  have e1 : ((baseList grp g).map fun p =>
      G.tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p
        fun id => y (Fin.castAdd A' p, id)).prod =
      ∏ p ∈ univ.filter (fun p => grp (Fin.castAdd A' p) = g),
        G.tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p fun id => y (Fin.castAdd A' p, id) := by
    rw [← List.prod_toFinset _ nodup_baseList]
    refine Finset.prod_congr ?_ fun p _ => rfl
    ext p
    simp [mem_baseList]
  have hnd : (roleList grp g M).Nodup := pairwise_roleList.imp fun h => h.1
  have e2 : ((roleList grp g M).map fun r => G.roleAt P n o r fun id => y (M.rp r, id)).prod =
      ∏ r ∈ univ.filter (fun r => grp (M.rp r) = g), G.roleAt P n o r fun id => y (M.rp r, id) := by
    rw [← List.prod_toFinset _ hnd]
    refine Finset.prod_congr ?_ fun r _ => rfl
    ext r
    simp [mem_roleList]
  rw [e1, e2]
  have e3 : ∀ a, (G.tabFinal mu T cb P q x ρ n o a fun id => y (a, id)) =
      G.initAll mu T cb A' q x ρ n a (fun id => y (a, id)) *
        ∏ r : M.R, if M.rp r = a then G.roleAt P n o r (fun id => y (a, id)) else 1 := by
    intro a
    rw [G.tabFinal_eq, G.partyTab]
  rw [Finset.prod_congr rfl fun a _ => e3 a, Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_filter, Finset.prod_filter]
    have h := Fin.prod_univ_add (fun a : Fin (K + K + A') => if grp a = g then
      G.initAll mu T cb A' q x ρ n a (fun id => y (a, id)) else 1)
    refine Eq.trans ?_ h.symm
    have h1 : (∏ p : Fin A', if grp (Fin.natAdd (K + K) p) = g then
        G.initAll mu T cb A' q x ρ n (Fin.natAdd (K + K) p) (fun id => y (Fin.natAdd (K + K) p, id)) else 1) = 1 := by
      refine Finset.prod_eq_one fun p _ => ?_
      rw [G.initAll, Fin.addCases_right, ite_self]
    rw [h1, mul_one]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [G.initAll, Fin.addCases_left]
  · rw [Finset.prod_comm, Finset.prod_filter]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Finset.prod_ite_eq]
    simp only [mem_filter, mem_univ, true_and]

end Nc.Grp
