/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.Group

/-!
# The program GROUP: the theorem

For a fixed automaton and a fixed list of roles of laws there is one formula GROUP. Its plain sum at the script of a group
is the value of the group.
-/


-- `grpT` and `GroupOK` are stated here so that `exists_group` can conclude `GroupOK` directly.
-- They keep their `Nc.Dl` names because the rest of `Nc/Dl` and the paper statements use them.
namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut

/-- The time of GROUP at a script. -/
def grpT (bT bub : List Bool) (l : List Grp.Ins) : ℕ :=
  (bT.length + 1) * (Grp.bval bT + 1) + (bub.length + 1) * (Grp.bval bub + 1) +
    (l.map (Grp.insCost (Grp.bval bT) (Grp.bval bub))).sum + l.length

/-- **What GROUP does** (the conclusion of `Nc.Grp.exists_group`). -/
def GroupOK {A : Type} [CommRing A] (θ : List Bool → A) {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S]
    [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ} (mu : Letter S Unit Γ → Matrix Q Q A)
    (cb : Option Γ → Fin c → Bool) (kinds : List (Σ L : G.Law A, L.Ro)) (qn : Q → ℕ) (GROUP : Fm) (κ : ℕ) : Prop :=
  ∀ {A' K E U0 U1 cap : ℕ} {Gr : Type} [DecidableEq Gr] [Fintype Gr]
    {M : Sys A (K + K + A') E} (P : G.Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
    (o : M.N → Fin U1) (grp : Fin (K + K + A') → Gr) (g : Gr) (key : Grp.Cell M U0 U1 → List Bool)
    (dkey : Fin (K + K) × Fin U0 → List Bool) (tg : M.R → ℕ) (bT bub : List Bool)
    (b : G.Uid (K + K) U0 M.N U1 → UW (Grp.bval bub)),
    Function.Injective (Sum.elim key dkey) → 0 < Grp.bval bub → P.Ok cap → (∀ κ, (x κ).length ≤ Grp.bval bT) →
    (∀ s p, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) → (∀ r, kinds[tg r]? = some ⟨M.kind r.1, r.2⟩) →
    Plain θ (κ * grpT bT bub (Grp.script qn cb P q x ρ n o grp g key dkey tg b))
      (.cons GROUP.code (Grp.scriptT bT bub (Grp.script qn cb P q x ρ n o grp g key dkey tg b))) ∧
    pv θ (.cons GROUP.code (Grp.scriptT bT bub (Grp.script qn cb P q x ρ n o grp g key dkey tg b))) =
      G.grpVal mu (Grp.bval bT) cb P q x ρ n o grp g b

end Nc.Dl

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}

/-- **GROUP.** -/
theorem exists_group (mu : Letter S Unit Γ → Matrix Q Q A) (cb : Option Γ → Fin c → Bool)
    (kinds : List (Σ L : G.Law A, L.Ro)) (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q')
    (htab : ∀ z ∈ kinds, ∀ i y h, ∃ e : WE, e.val θ = z.1.tab z.2 i y h) :
    ∃ (GROUP : Fm) (κ : ℕ), Nc.Dl.GroupOK θ mu cb kinds (fun z => (qn Q z : ℕ)) GROUP κ := by
  obtain ⟨F, κ, hF⟩ := ex_group (S := S) (θ := θ) mu cb kinds (by simp [sepOf])
  refine ⟨F, κ, fun {A' K E U0 U1 cap Gr} _ _ {M} P q x ρ n o grp g key dkey tg bT bub b hkey hub hP hx hρ hkind => ?_⟩
  have h1 := hF bT bub (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b) (insOk_script hkind b)
  have htab' : ∀ (r : M.R) i y h, ∃ e : WE, e.val θ = (M.kind r.1).tab r.2 i y h := fun r =>
    htab ⟨M.kind r.1, r.2⟩ (List.mem_of_getElem? (hkind r))
  have h2 := wsum_script (cb := cb) (kinds := kinds) (tg := tg) hkey hub hP hmu hx hρ hkind htab' (q := q) (o := o) (n := n)
    (grp := grp) (g := g) b
  obtain ⟨p1, p2⟩ := h1.plain
  refine ⟨p1, ?_⟩
  rw [p2, ← h2, wsum, List.map_map]
  congr 1
  exact List.map_congr_left fun z _ => by simp

end Nc.Grp
