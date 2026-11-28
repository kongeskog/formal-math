/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Flow

/-!
# The tower plan: holders of units
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b J m Uu AA : ℕ} {T : Tower h b J} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T}

/-- The nodes that hold the units of a channel. -/
noncomputable def hN (ν : NM R FL (ch := ch)) : Sym2 (Nd T) :=
  s(partM ν.1 ((kindM FL ν.1).c ν.2), partM ν.1 ((kindM FL ν.1).d ν.2))

/-- The nodes that hold an initial unit. -/
def hB (ch : Fin AA ↪ T.X 0) (a c : Fin AA) : Sym2 (Nd T) := s(nd (Nat.zero_le _) (ch a), nd (Nat.zero_le _) (ch c))

/-- The nodes that hold the units with a target. -/
noncomputable def hT (R : Routes T m Uu) (ch : Fin AA ↪ T.X 0) : Tg T m AA → Sym2 (Nd T)
  | .done => s(none, none)
  | .edge j e => s(nd (Nat.le_of_lt_succ j.2) (T.e0 e), nd (Nat.le_of_lt_succ j.2) (T.e1 e))
  | .nxt x => s(tri R ch x 0, tri R ch x 2)
  | .seg j i ω q => q.map fun f => nd j.2 (atv i ω f)

theorem edgeO_hold {c c' γ : T.X 0} {s : ℕ} (hs : s < R.pl c c' γ) :
    (edgeO ((R.path c c' γ)[s]?) : Tg T m AA) ≠ .done ∧
    hT R ch (edgeO ((R.path c c' γ)[s]?) : Tg T m AA) =
      s(nd (Nat.zero_le _) (R.pn c c' γ s), nd (Nat.zero_le _) (R.pn c c' γ (s + 1))) := by
  obtain ⟨e, h1, h2, -⟩ := R.exists_edge c c' γ hs
  rw [h1]
  refine ⟨by simp [edgeO], ?_⟩
  have := congrArg (Sym2.map (nd (Nat.zero_le _))) h2
  simp only [Sym2.map_mk] at this
  exact this

/-- Initial units. -/
theorem hB_eq {a c : Fin AA} {k : ℕ} (hd : tgB R ch a c k ≠ .done) : hB ch a c = hT R ch (tgB R ch a c k) := by
  unfold tgB at hd ⊢
  by_cases hac : a = c
  · rw [if_pos hac] at hd
    exact absurd rfl hd
  · rw [if_neg hac] at hd ⊢
    have hne : ch a ≠ ch c := fun hh => hac (ch.injective hh)
    have hpos := R.pl_pos hne (gam ch a k)
    have hle := (R.pl_le (ch a) (ch c) (gam ch a k)).trans (R.length_path _ _ _)
    by_cases hs : 0 < 2 * m ∧ 1 < R.pl (ch a) (ch c) (gam ch a k)
    · rw [dif_pos hs]
      rfl
    · rw [dif_neg hs]
      have h1 : R.pl (ch a) (ch c) (gam ch a k) = 1 := by
        by_contra h1
        exact hs ⟨by omega, by omega⟩
      rw [(edgeO_hold hpos).2]
      have h2 := R.pn_pl (ch a) (ch c) (gam ch a k)
      rw [h1] at h2
      rw [h2]
      rfl

theorem seg_hold {j : ℕ} (hj : j < J) (i : Fin h) (c : T.X j) :
    (s(T.co i (hst i c), T.co i c) : Sym2 T.Fl).map
      (fun f => nd hj (atv i (T.πV (T.vx i c)) f)) =
      s(nd hj (hst i c), nd hj (T.π c)) := by
  rw [Sym2.map_mk]
  have h1 : atv i (T.πV (T.vx i c)) (T.co i (hst i c)) = hst i c := by
    rw [← T.host_vx hj i (T.vx i c)]
    exact atv_eq i _
  have h2 : atv i (T.πV (T.vx i c)) (T.co i c) = T.π c := by
    rw [← T.π_vx i c, ← T.π_co i c]
    exact atv_eq i _
  simp only [h1, h2]

/-- Units of channels. -/
theorem hN_eq (ν : NM R FL (ch := ch)) (hd : tgM ν.1 ν.2 ≠ .done) : hN ν = hT R ch (tgM ν.1 ν.2) := by
  rcases ν with ⟨⟨x, hx⟩ | l, ν⟩
  · revert hd
    revert ν
    intro (ν : Bool) hd
    have e0 : hN (⟨.inl ⟨x, hx⟩, ν⟩ : NM R FL) =
        if ν then s(tri R ch x 1, tri R ch x 2) else s(tri R ch x 0, tri R ch x 1) := by
      cases ν <;> rfl
    rw [e0]
    change tgR R ch x ν ≠ .done at hd
    change _ = hT R ch (tgR R ch x ν)
    rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
    · obtain ⟨hac, hs⟩ := hx
      have hle := (R.pl_le (ch a) (ch c) γ).trans (R.length_path _ _ _)
      cases ν
      · simp only [tgR, Bool.false_eq_true, if_false]
        rw [(edgeO_hold (by omega)).2]
        rfl
      · simp only [tgR, if_true]
        by_cases hs2 : s.1 + 1 < 2 * m ∧ s.1 + 2 < R.pl (ch a) (ch c) γ
        · rw [dif_pos hs2]
          rfl
        · rw [dif_neg hs2, (edgeO_hold hs).2]
          have h1 : R.pl (ch a) (ch c) γ = s.1 + 1 + 1 := by
            by_contra h1
            exact hs2 ⟨by omega, by omega⟩
          have h2 := R.pn_pl (ch a) (ch c) γ
          rw [h1] at h2
          rw [h2]
          rfl
    · exact absurd rfl hd
    · cases ν
      · simp only [Bool.false_eq_true, if_false]
        fin_cases s
        · exact absurd rfl hd
        · exact (seg_hold j.2 (T.ty e) (T.e0 e)).symm
        · have h1 := T.π_ends e
          have h2 := congrArg (Sym2.map (nd j.2)) h1
          simp only [Sym2.map_mk] at h2
          exact h2.symm
        · refine Eq.trans ?_ (seg_hold j.2 (T.ty e) (T.e1 e)).symm
          exact Sym2.eq_swap
      · simp only [if_true]
        fin_cases s
        · simp only [Fin.zero_eta, tgR, Matrix.cons_val_zero]
          by_cases hh : hst (T.ty e) (T.e0 e) ≠ T.π (T.e0 e)
          · rw [if_pos hh]
            rfl
          · rw [if_neg hh]
            rw [not_not] at hh
            change s(nd j.2 (hst (T.ty e) (T.e0 e)), nd j.2.le (T.e1 e)) =
              s(nd j.2 (T.π (T.e0 e)), nd j.2.le (T.e1 e))
            rw [hh]
        · rfl
        · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hd ⊢
          by_cases hh : T.π (T.e1 e) ≠ hst (T.ty e) (T.e1 e)
          · rw [if_pos hh]
            rfl
          · rw [if_neg hh] at hd
            exact absurd rfl hd
        · exact absurd rfl hd
    · exact absurd rfl hd
  · change s(nd l.1.2 (atv l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).c ν))),
      nd l.1.2 (atv l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).d ν)))) = _
    set p := (T.nr l.2.1).symm (l.2.2.1, FL.cn l.2.2.2 ν) with hp
    have hp2 : T.nr l.2.1 p = (l.2.2.1, FL.cn l.2.2.2 ν) := by rw [hp, Equiv.apply_symm_apply]
    have h0 := T.nr_vx0 l.2.1 p
    have h1 := T.nr_vx1 l.2.1 p
    have h2 := T.nr_co l.2.1 p
    rw [hp2] at h0 h1 h2
    have h3 := (FL.ends l.2.2.2 ν).trans h2.symm
    have h4 := congrArg (Sym2.map fun f => nd l.1.2 (atv l.2.1 l.2.2.1 f)) h3
    simp only [Sym2.map_mk] at h4
    rw [h4]
    have e1 : atv l.2.1 l.2.2.1 (T.co l.2.1 (T.e0 p.1)) = T.e0 p.1 := by
      have := atv_eq l.2.1 (T.e0 p.1)
      rwa [h0] at this
    have e2 : atv l.2.1 l.2.2.1 (T.co l.2.1 (T.e1 p.1)) = T.e1 p.1 := by
      have := atv_eq l.2.1 (T.e1 p.1)
      rwa [h1] at this
    rw [e1, e2]
    rfl

end Nc.Tow
