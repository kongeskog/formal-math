/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.G.Exact

/-!
# The cells, the base parties and the roles of a group
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open Finset Nc.G Nc.Cut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K E U0 U1 ub c cap : ℕ} {Gr : Type} [DecidableEq Gr]

section

variable (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (cb : Option Γ → Fin c → Bool)
  {M : Sys F (K + K + A') E} (P : G.Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
  (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
  (o : M.N → Fin U1) (grp : Fin (K + K + A') → Gr) (g : Gr)

/-- Cells. -/
abbrev Cell (M : Sys F (K + K + A') E) (U0 U1 : ℕ) := Fin (K + K + A') × G.Uid (K + K) U0 M.N U1

/-- The cells of the group. -/
def dom : Finset (Cell M U0 U1) := univ.filter fun c =>
  grp c.1 = g ∧ c.2 ∈ G.Plan.seenAt n o E ∧ Holds (G.hold0 M.np) (G.hold1 M.np) c.1 c.2

/-- What a role chooses in a block. -/
abbrev Bk (L : Law F) (p : L.Ro) := Σ i : L.I, ∀ ν : L.CnAt p, Fin (L.len i ν) → Bool

/-- The string of a channel. -/
def chS (L : Law F) (p : L.Ro) {B : ℕ} (f : Fin B → Bk L p) (ν : L.CnAt p) : List Bool :=
  chString L.lab (fun j => L.len j ν) (fun k => (f k).1) (fun k => (f k).2 ν)

/-- The base parties of the group. -/
def baseList : List (Fin (K + K)) := (List.finRange (K + K)).filter fun p => grp (Fin.castAdd A' p) = g

/-- All roles, in the order of the moves. -/
noncomputable def allRoles (M : Sys F (K + K + A') E) : List M.R := (List.finRange E).flatMap fun x =>
  (univ : Finset (M.kind x).Ro).toList.map (Sigma.mk x)

/-- The roles of the group. -/
noncomputable def roleList (M : Sys F (K + K + A') E) : List M.R := (allRoles M).filter fun r => grp (M.rp r) = g

end

section facts

variable {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {cb : Option Γ → Fin c → Bool}
  {M : Sys F (K + K + A') E} {P : G.Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}

theorem mem_dom {c : Cell M U0 U1} : c ∈ dom n o grp g ↔
    grp c.1 = g ∧ c.2 ∈ G.Plan.seenAt n o E ∧ Holds (G.hold0 M.np) (G.hold1 M.np) c.1 c.2 := by
  simp [dom]

theorem mem_baseList {p : Fin (K + K)} : p ∈ baseList (A' := A') grp g ↔ grp (Fin.castAdd A' p) = g := by
  simp [baseList]

theorem mem_allRoles (r : M.R) : r ∈ allRoles M := by
  obtain ⟨x, p⟩ := r
  exact List.mem_flatMap.2 ⟨x, List.mem_finRange x, List.mem_map.2 ⟨p, Finset.mem_toList.2 (mem_univ p), rfl⟩⟩

theorem mem_roleList {r : M.R} : r ∈ roleList grp g M ↔ grp (M.rp r) = g := by
  simp [roleList, mem_allRoles]

theorem nodup_baseList : (baseList (A' := A') (K := K) grp g).Nodup := (List.nodup_finRange _).filter _

theorem pairwise_allRoles : (allRoles M).Pairwise fun r r' => r ≠ r' ∧ r.1 ≤ r'.1 := by
  unfold allRoles
  rw [List.pairwise_flatMap]
  refine ⟨fun x _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine (Finset.nodup_toList _).imp fun {p p'} h => ⟨fun h' => h ?_, le_rfl⟩
    exact eq_of_heq (Sigma.mk.inj h').2
  · refine (List.pairwise_lt_finRange E).imp fun {x x'} hx r hr r' hr' => ?_
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hr
    obtain ⟨p', -, rfl⟩ := List.mem_map.1 hr'
    exact ⟨fun h => hx.ne (Sigma.mk.inj h).1, hx.le⟩

theorem pairwise_roleList : (roleList grp g M).Pairwise fun r r' => r ≠ r' ∧ r.1 ≤ r'.1 :=
  pairwise_allRoles.filter _

theorem role_eq_of_rp {x : Fin E} {p p' : (M.kind x).Ro} (h : M.rp ⟨x, p⟩ = M.rp ⟨x, p'⟩) : p = p' :=
  M.inj x h

theorem holds_cnAt {r : M.R} (ν : (M.kind r.1).CnAt r.2) (k : Fin U1) :
    Holds (G.hold0 M.np) (G.hold1 M.np) (M.rp r) (G.Uid.new ⟨r.1, ν.1⟩ k : G.Uid (K + K) U0 M.N U1) := by
  obtain ⟨x, p⟩ := r
  obtain ⟨ν, h | h⟩ := ν
  · exact Or.inl (congrArg (M.part x) h.symm)
  · exact Or.inr (congrArg (M.part x) h.symm)

end facts

end Nc.Grp
