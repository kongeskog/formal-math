/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Bd2

/-!
# Bounds for the templates
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

theorem ok_listTm {σ : List Bool → Tree} {L : ℕ} {ts : List Tm} (h : ∀ t ∈ ts, t.Ok σ L) :
    (listTm ts).Ok σ L := by
  induction ts with
  | nil => trivial
  | cons t ts ih => exact ⟨h t List.mem_cons_self, ih fun s hs => h s (List.mem_cons_of_mem _ hs)⟩

theorem ok_catTm {σ : List Bool → Tree} {L : ℕ} {ts : List Tm}
    (h : ∀ t ∈ ts, (t.expand σ).toList.length ≤ L ∧ t.Ok σ L) : (catTm ts).Ok σ L := by
  induction ts with
  | nil => trivial
  | cons t ts ih =>
    exact ⟨(h t List.mem_cons_self).1, (h t List.mem_cons_self).2,
      ih fun s hs => h s (List.mem_cons_of_mem _ hs)⟩

variable {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} {C : Codes S M U0 U1 D pS}
  {tab : SlpTab P grp D pS} {qn : Q → ℕ} {pt : Fin K → Tree} {q : Fin (K + 1) → Q}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : NN K U0} {o : M.N → Fin U1}
  {b : G.Uid (K + K) U0 M.N U1 → UW ub} {st : NmT S M U0 U1 pS → Tree} {tg : M.R → ℕ} {bT bub : List Bool}
  {gt : Fin mm → Tree} {d1 gp : Tree} {X : ℕ}

/-- **The cost of the templates**: they append lists of at most `X` members, so the cost is
linear in the size. -/
theorem cost_instTm (hU0X : U0 + 1 ≤ X) (g : Fin mm) :
    (instTm C tab tg bT bub gt d1 gp g).cost (byPath C.nm st) ≤
      (instTm C tab tg bT bub gt d1 gp g).tree.size * (62 * X + 250) := by
  have hX : 1 ≤ X := by omega
  have names : ∀ {α : Type} (l : List α) (f : α → NmT S M U0 U1 pS),
      (listTm (l.map fun a => gN C (f a))).Ok (byPath C.nm st) X := fun l f =>
    ok_listTm fun t ht => by obtain ⟨a, -, rfl⟩ := List.mem_map.1 ht; trivial
  have one : ∀ (k : List Bool) (id : G.Uid (K + K) U0 M.N U1),
      ((oneTm C k id).expand (byPath C.nm st)).toList.length ≤ X := fun k id => by
    rw [oneTm, expand_listTm, toList_listT]
    simpa using hX
  refine Tm.cost_le _ ⟨trivial, trivial, ok_catTm fun t ht => ?_⟩
  simp only [List.mem_append, List.mem_map] at ht
  obtain (⟨p, -, rfl⟩ | ⟨r, -, rfl⟩) | ⟨id, -, rfl⟩ := ht
  · refine ⟨?_, ⟨?_, trivial⟩, trivial⟩
    · rw [expand_ifTm]
      split_ifs
      · rw [expand_listTm, toList_listT]
        simpa using hX
      · simp
    · have body : ∀ p, (bodyTm C p).Ok (byPath C.nm st) X := fun p =>
        ⟨names _ _, by rw [List.ofFn_eq_map]; exact names _ _,
          by rw [List.ofFn_eq_map]; exact names _ _⟩
      refine Fin.addCases (fun κ => ?_) (fun κ => ?_) p
      · rw [baseTm, Fin.addCases_left]
        exact ⟨trivial, ⟨trivial, trivial⟩, body _⟩
      · rw [baseTm, Fin.addCases_right]
        exact ⟨trivial, trivial, body _⟩
  · refine ⟨?_, ⟨⟨trivial, trivial, ok_listTm fun t ht => ?_, names _ _⟩, trivial⟩, trivial⟩
    · rw [expand_ifTm]
      split_ifs
      · rw [expand_listTm, toList_listT]
        simpa using hX
      · simp
    · obtain ⟨e, -, rfl⟩ := List.mem_map.1 ht
      refine ok_catTm fun t ht => ?_
      obtain ⟨id, -, rfl⟩ := List.mem_map.1 ht
      refine ⟨?_, trivial, trivial⟩
      rw [expand_ifTm]
      split_ifs
      · simpa [Tm.expand] using hX
      · simp
  · refine ⟨?_, ⟨⟨trivial, ⟨⟨trivial, trivial, trivial⟩, trivial⟩⟩,
      ⟨⟨trivial, trivial, trivial⟩, trivial⟩, trivial⟩, trivial⟩
    rw [endTm, expand_ifTm]
    split_ifs
    · simp only [Tm.expand]
      split_ifs
      · simpa using hX
      · exact one _ _
      · rw [expand_ifTm]
        split_ifs
        · exact one _ _
        · simp
    · simp

end Nc.Dl
