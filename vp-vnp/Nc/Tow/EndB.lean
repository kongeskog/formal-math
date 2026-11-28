/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.EndA

/-!
# The tower plan: units between a node and its parent
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b J m Uu AA : ℕ} {T : Tower h b J} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R ch FL → ℕ}

/-- The parent of a chamber, as a node. -/
noncomputable def parN (Lf : ∀ j, T.Ed j → ℕ) (j : ℕ) (c : T.X j) : Nd T :=
  if hj : j + 1 ≤ J then nd hj (hostj Lf c) else none

theorem num_inn (j : Fin J) (i : Fin h) (e : T.Ed j) (hx : okR R ch (.inn j i e))
    (hne : num lhat n o (.inl ⟨.inn j i e, hx⟩) ≠ 0) :
    i = imin (lev (load lhat n o)) j.1 := by
  classical
  rw [num_eq, numF] at hne
  split_ifs at hne with ha
  · exact (isMin_iff _ j.castSucc i).1 ha
  · exact absurd rfl hne


theorem num_mid (j : Fin J) (e : T.Ed j) (s : Fin 4) (hx : okR R ch (.mid j e s))
    (hne : num lhat n o (.inl ⟨.mid j e s, hx⟩) ≠ 0) :
    T.ty e = imin (lev (load lhat n o)) j.1 := by
  obtain ⟨hx0, h1⟩ := num_mid_le FL lhat n o j e s hx
  have h2 := (num_mid0 (FL := FL) (lhat := lhat) (n := n) (o := o) j e hx0).2
  by_contra hcon
  have h3 : ¬ IsMin (load lhat n o) j.castSucc (T.ty e) :=
    fun hm => hcon ((isMin_iff _ j.castSucc _).1 hm)
  have := h2 h3
  omega

/-- A chamber and its parent hold the units of a channel without target. -/
theorem done_hold {x : RM T m AA} (hx : okR R ch x) {β : Bool} (hd : tgR R ch x β = .done)
    (hne : num lhat n o (.inl ⟨x, hx⟩) ≠ 0) :
    ∃ (j : ℕ) (hj : j ≤ J) (c : T.X j), hN (⟨.inl ⟨x, hx⟩, β⟩ : NM R ch FL) =
        s(nd hj c, parN (lev (load lhat n o)) j c) := by
  have e0 : ∀ β : Bool, hN (⟨.inl ⟨x, hx⟩, β⟩ : NM R ch FL) =
      if β then s(tri R ch x 1, tri R ch x 2) else s(tri R ch x 0, tri R ch x 1) := by
    intro β
    cases β <;> rfl
  rw [e0]
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · exfalso
    obtain ⟨hac, hs⟩ := hx
    cases β
    · simp only [tgR] at hd
      exact (edgeO_hold (R := R) (ch := ch) (AA := AA) (m := m) (c := ch a) (c' := ch c) (γ := γ) (s := s.1) (by omega)).1 hd
    · simp only [tgR] at hd
      split_ifs at hd
      exact (edgeO_hold (R := R) (ch := ch) (AA := AA) (m := m) (c := ch a) (c' := ch c) (γ := γ) (s := s.1 + 1) hs).1 hd
  · have hi := num_inn j i e hx hne
    have hjJ := j.2
    have hpar : ∀ c : T.X j.1, parN (lev (load lhat n o)) j.1 c =
        nd j.2 (hst i c) := by
      intro c
      unfold parN
      rw [dif_pos (by omega : j.1 + 1 ≤ J), hi]
      rfl
    cases β
    · refine ⟨j.1, j.2.le, T.e0 e, ?_⟩
      rw [hpar]
      rfl
    · refine ⟨j.1, j.2.le, T.e1 e, ?_⟩
      rw [hpar]
      have h1 : T.vx i (T.e0 e) = T.vx i (T.e1 e) := by
        rw [T.nr_vx0 i ⟨e, hx⟩, T.nr_vx1 i ⟨e, hx⟩]
      have h2 : hst i (T.e0 e) = hst i (T.e1 e) := by
        unfold hst
        rw [h1]
      change s(nd j.2 (hst i (T.e0 e)), nd j.2.le (T.e1 e)) = _
      rw [h2, Sym2.eq_swap]
  · have hi := num_mid j e s hx hne
    have hjJ := j.2
    have hpar : ∀ c : T.X j.1, parN (lev (load lhat n o)) j.1 c =
        nd j.2 (hst (T.ty e) c) := by
      intro c
      unfold parN
      rw [dif_pos (by omega : j.1 + 1 ≤ J), hi]
      rfl
    cases β
    · refine ⟨j.1, j.2.le, T.e0 e, ?_⟩
      rw [hpar]
      fin_cases s
      · rfl
      · simp [tgR] at hd
      · simp [tgR] at hd
      · simp [tgR] at hd
    · refine ⟨j.1, j.2.le, T.e1 e, ?_⟩
      rw [hpar]
      fin_cases s
      · simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at hd
        split_ifs at hd
      · simp [tgR] at hd
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hd
        split_ifs at hd with hq
        rw [not_not] at hq
        change s(nd j.2 (T.π (T.e1 e)), nd j.2.le (T.e1 e)) = _
        rw [hq, Sym2.eq_swap]
      · change s(nd j.2 (hst (T.ty e) (T.e1 e)), nd j.2.le (T.e1 e)) = _
        rw [Sym2.eq_swap]
  · have hpar : ∀ c : T.X J, parN (lev (load lhat n o)) J c = none := by
      intro c
      unfold parN
      rw [dif_neg (by omega)]
    cases β
    · refine ⟨J, le_rfl, T.e0 e, ?_⟩
      rw [hpar]
      rfl
    · refine ⟨J, le_rfl, T.e1 e, ?_⟩
      rw [hpar]
      change s(none, nd le_rfl (T.e1 e)) = _
      rw [Sym2.eq_swap]

end Nc.Tow
