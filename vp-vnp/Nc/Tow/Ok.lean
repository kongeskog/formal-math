/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Plan

/-!
# The tower plan obeys the rules
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}

/-- Active relays are determined by their targets. -/
theorem inpR_unique {L : Tg T m AA → ℕ} {x x' : RM T m AA} (hx : okR T R ch x) (hx' : okR T R ch x')
    (ha : ActR L x) (ha' : ActR L x') (he : inpR T x = inpR T x') : x = x' := by
  -- equal targets are edges of one stage, or one relay: the active type of an edge is unique
  -- (`isMin_eq`), `okR` excludes it for `inn`, and the last stage is not an earlier one
  rcases x with _ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e <;>
    rcases x' with _ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e' <;>
    simp only [inpR, ActR, okR] at * <;> (try split_ifs at he) <;> simp at he <;>
    grind [isMin_eq, Fin.castSucc_lt_last]

/-- A relay gives its units at an edge or at a relay, never at an end segment or at the root. -/
theorem inpR_ne {x : RM T m AA} : inpR T x ≠ .done ∧ ∀ j i ω q, inpR T x ≠ .seg j i ω q := by
  cases x <;> simp [inpR]
  split_ifs <;> simp

section Plan

variable {n : Fin AA → Fin AA → Fin (U0 + 1)} {o : (sys R FL Pl).N → Fin U1}

/-- The target of the units of a slot. -/
def inpZ : ZM R FL (ch := ch) → Tg T m AA
  | ⟨.inl x, _⟩ => inpR T x.1
  | ⟨.inr l, e⟩ => .seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e)

-- `consM_inl` and `consM_inr` are in `Nc/Tow/Plan.lean`, next to `consM`, so that `Slp4` can use them too.

/-- A unit consumed at the slot `z` is allowed, and its target is the slot's target. -/
theorem consM_al {z : ZM R FL (ch := ch)} {u : Un R FL Pl U0 U1} (hu : u ∈ consM R FL Pl lhat n o z) :
    AlU R FL Pl lhat n o u ∧ tgU R FL Pl u = inpZ z := by
  rcases z with ⟨x | l, e⟩
  · exact ((consM_inl x e u).1 hu).2
  · have := ((consM_inr l e u).1 hu).2
    exact ⟨this.1, this.2.1⟩

/-- A unit is given at one slot at most. -/
theorem consM_unique {z z' : ZM R FL (ch := ch)} {u : Un R FL Pl U0 U1} (hu : u ∈ consM R FL Pl lhat n o z)
    (hu' : u ∈ consM R FL Pl lhat n o z') : z = z' := by
  rcases z with ⟨x | l, e⟩ <;> rcases z' with ⟨x' | l', e'⟩
  · obtain ⟨h1, -, h2⟩ := (consM_inl x e u).1 hu
    obtain ⟨h1', -, h2'⟩ := (consM_inl x' e' u).1 hu'
    have hx : x = x' := Subtype.ext (inpR_unique x.2 x'.2 h1 h1' (h2.symm.trans h2'))
    subst hx
    rfl
  · obtain ⟨-, -, h2⟩ := (consM_inl x e u).1 hu
    obtain ⟨-, -, h2', -⟩ := (consM_inr l' e' u).1 hu'
    exact absurd (h2.symm.trans h2') (inpR_ne.2 _ _ _ _)
  · obtain ⟨-, -, h2, -⟩ := (consM_inr l e u).1 hu
    obtain ⟨-, -, h2'⟩ := (consM_inl x' e' u).1 hu'
    exact absurd (h2'.symm.trans h2) (inpR_ne.2 _ _ _ _)
  · obtain ⟨h1, -, h2, h3, h4⟩ := (consM_inr l e u).1 hu
    obtain ⟨h1', -, h2', h3', h4'⟩ := (consM_inr l' e' u).1 hu'
    obtain ⟨j, i, ω, d⟩ := l
    obtain ⟨j', i', ω', d'⟩ := l'
    have he := h2.symm.trans h2'
    simp only [Tg.seg.injEq] at he
    obtain ⟨hj, hi, hω, hq⟩ := he
    subst hj
    subst hi
    have := eq_of_heq hω
    subst this
    -- the direction is the first one that fits, for both slots
    have hd : d = d' := pick_eq _ (l := ⟨j, i, ω, d⟩) h1 h1'
    subst hd
    -- the slot is the rank of the unit divided by the number of units
    have hs : su FL d e = su FL d e' :=
      (Nat.div_eq_of_lt_le h3 h4).symm.trans (Nat.div_eq_of_lt_le h3' h4')
    have hee : e = e' :=
      rk_inj (fun a b hab => (Fintype.equivFin (FL.L d).Sl).injective (Fin.ext hab)) (mem_univ _)
        (mem_univ _) hq hs
    subst hee
    rfl

/-- The number of units of a slot. -/
theorem card_consM (z : ZM R FL (ch := ch)) :
    (consM R FL Pl lhat n o z : Finset (Un R FL Pl U0 U1)).card ≤ num R ch FL lhat (nn n) (oo R FL Pl o) z.1 := by
  classical
  rcases z with ⟨x | l, e⟩
  · rw [num_eq, consM, numF]
    split_ifs with ha
    · rw [load_eq]
    · simp
  · rw [consM]
    split_ifs with ha
    · refine (card_rk_le (ix_inj (R := R) (FL := FL) (Pl := Pl)) (Al R FL Pl lhat n o)
        (Tg.seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e) : Tg T m AA) _ _).trans ?_
      rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
    · simp

/-- A move that is earlier in time than the move at index `x` has a smaller index. -/
theorem lt_of_time {mv : Mv T R ch FL} {x : Fin (Fintype.card (Mv T R ch FL))}
    (h : timeM R ch FL mv < timeM R ch FL (eE R FL x)) : (eE R FL).symm mv < x := by
  simpa using eE_lt R FL h

section Causal

variable {o' : (sys R FL Pl).N → Fin U1} {t : ℕ}

/-- The units given at a slot depend only on the outcomes of earlier moves. -/
theorem consM_congr (hb : 0 < b) (z : ZM R FL (ch := ch))
    (hag : ∀ mv' : Mv T R ch FL, timeM R ch FL mv' < timeM R ch FL z.1 →
      ∀ c, oo R FL Pl o ⟨mv', c⟩ = oo R FL Pl o' ⟨mv', c⟩) :
    (consM R FL Pl lhat n o z : Finset (Un R FL Pl U0 U1)) = consM R FL Pl lhat n o' z := by
  -- whether a unit that is due by then is allowed
  have hal {u : Un R FL Pl U0 U1} (hu : tgTime (tgU R FL Pl u) ≤ timeM R ch FL z.1) :
      AlU R FL Pl lhat n o u ↔ AlU R FL Pl lhat n o' u := by
    cases u with
    | init a c k => exact Iff.rfl
    | new ν k =>
      have h1 : timeM R ch FL (eN R FL Pl ν).1 < timeM R ch FL z.1 :=
        (tg_time (eN R FL Pl ν)).trans_le hu
      change k.1 < alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) ↔
        k.1 < alv R ch FL lhat (nn n) (oo R FL Pl o') (eN R FL Pl ν)
      unfold alv
      rw [num_congr hb fun mv' hmv' c => hag mv' (hmv'.trans h1) c,
        alvN_congr (fun c => hag _ h1 c)]
  ext u
  rcases z with ⟨x | l, e⟩
  · rw [consM_inl, consM_inl, actR_congr fun τ hτ => load_congr hb hτ hag]
    exact and_congr_right fun _ => and_congr_left fun h => hal (h ▸ inp_time x.1)
  · have hrk (hu : tgU R FL Pl u = .seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e)) :
        rkU R FL Pl lhat n o u = rkU R FL Pl lhat n o' u := by
      unfold rkU
      exact rk_congr fun v hv =>
        mem_Al.trans ((hal ((hv.trans hu).symm ▸ le_rfl)).trans mem_Al.symm)
    rw [consM_inr, consM_inr, pick_congr fun q => load_congr hb le_rfl hag, num_congr hb hag]
    refine and_congr_right fun _ => ⟨fun ⟨h1, h2, h3⟩ => ?_, fun ⟨h1, h2, h3⟩ => ?_⟩
    · rw [hrk h2] at h3
      exact ⟨(hal (h2 ▸ le_rfl)).1 h1, h2, h3⟩
    · rw [← hrk h2] at h3
      exact ⟨(hal (h2 ▸ le_rfl)).2 h1, h2, h3⟩

/-- The outcomes of the channels of a move agree if they agree on the channels of its index. -/
theorem oo_congr {P : Fin (Fintype.card (Mv T R ch FL)) → Prop}
    (ho : ∀ ν : (sys R FL Pl).N, P ν.1 → o ν = o' ν) {mv : Mv T R ch FL} (h : P ((eE R FL).symm mv))
    (c) : oo R FL Pl o ⟨mv, c⟩ = oo R FL Pl o' ⟨mv, c⟩ := by
  unfold oo
  rw [ho]
  convert h
  rw [Equiv.eq_symm_apply, ← eN_fst, Equiv.apply_symm_apply]

end Causal

/-- **The plan obeys the rules.** -/
theorem plan_ok (hb : 0 < b) {cap : ℕ}
    (hcap : ∀ (n : Fin AA → Fin AA → Fin (U0 + 1)) (o : (sys R FL Pl).N → Fin U1) mv,
      num R ch FL lhat (nn n) (oo R FL Pl o) mv ≤ cap) : (plan R FL Pl lhat U0 U1).Ok cap where
  causal n o o' z ho := consM_congr hb _ fun mv h => oo_congr (P := (· < z.1)) ho (lt_of_time h)
  causal' n o o' x ho := num_congr hb fun mv h => oo_congr (P := (· < x)) ho (lt_of_time h)
  causal'' n o o' x ho :=
    good_congr hb (fun mv h => oo_congr (P := (· < x)) (fun ν h' => ho ν h'.le) (lt_of_time h))
      (oo_congr (P := (· ≤ x)) ho (by simp))
  sub n o z u hu := by
    -- units that are given are current: seen before the move, and not given at an earlier slot
    obtain ⟨h1, h2⟩ := consM_al hu
    rw [Plan.cur, mem_sdiff]
    constructor
    · unfold Plan.seenAt
      rw [mem_union, mem_biUnion]
      cases u with
      | init a c k =>
        left
        simp only [seen0, mem_filter, mem_univ, true_and, decide_eq_true_eq]
        exact h1.2
      | new ν k =>
        right
        refine ⟨ν.1, mem_filter.2 ⟨mem_univ _, ?_⟩, ?_⟩
        · have h4 : tgTime (inpZ (eZ R FL Pl z)) ≤ timeM R ch FL (eZ R FL Pl z).1 := by
            rcases eZ R FL Pl z with ⟨x | l, e⟩
            · exact inp_time x.1
            · exact le_rfl
          have h5 := (tg_time (eN R FL Pl ν)).trans_le ((congrArg tgTime h2).le.trans h4)
          simpa [eN_fst] using lt_of_time h5
        · simp only [newUnits, mem_filter, mem_univ, true_and, decide_eq_true_eq]
          have h3 : k.1 < alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) := h1
          have h4 : alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) ≤ (o ν).1 := by
            refine (alvN_le _ _).trans ?_
            unfold oo
            rw [Equiv.symm_apply_apply]
          rw [Fin.le_def]
          omega
    · intro hmem
      obtain ⟨z', hz', hu'⟩ := mem_biUnion.1 hmem
      have hlt := (mem_filter.1 hz').2
      have hu' : u ∈ consM R FL Pl lhat n o (eZ R FL Pl z') := hu'
      rw [(eZ R FL Pl).injective (consM_unique hu hu')] at hlt
      exact lt_irrefl _ hlt
  hold n o z u hu := by
    -- both pairs are the ends of the target of the unit, put in place
    have hu : u ∈ consM R FL Pl lhat n o (eZ R FL Pl z) := hu
    obtain ⟨-, h2⟩ := consM_al hu
    have hd : tgU R FL Pl u ≠ .done := by
      rw [h2]
      rcases eZ R FL Pl z with ⟨x | l, e⟩
      · exact inpR_ne.1
      · simp [inpZ]
    have h3 : s(hold0 (sys R FL Pl).np u, hold1 (sys R FL Pl).np u) =
        (hT R ch (tgU R FL Pl u)).map Pl.pt := by
      cases u with
      | init a c k =>
        change _ = (hT R ch (tgB T R ch a c k)).map Pl.pt
        rw [← hB_eq (ch := ch) (R := R) hd, hB, Sym2.map_mk]
        simp only [Pl.pt_base]
        rfl
      | new ν k =>
        change _ = (hT R ch (tgM R ch FL (eN R FL Pl ν).1 (eN R FL Pl ν).2)).map Pl.pt
        rw [← hN_eq (eN R FL Pl ν) hd, hN, Sym2.map_mk]
        rfl
    have h4 : s((sys R FL Pl).zp z false, (sys R FL Pl).zp z true) =
        (hT R ch (tgU R FL Pl u)).map Pl.pt := by
      rw [h2, zp_eq, zp_eq]
      generalize eZ R FL Pl z = w
      rcases w with ⟨⟨x, hx⟩ | l, e⟩
      · change s(Pl.pt (tri T R ch x 0), Pl.pt (tri T R ch x 2)) = (hT R ch (inpR T x)).map Pl.pt
        have h1 : hT R ch (inpR T x) = s(tri T R ch x 0, tri T R ch x 2) := by
          rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
          · rfl
          · rfl
          · rw [inpR_mid]
            split_ifs with hs
            · subst hs; rfl
            · rfl
          · rfl
        rw [h1, Sym2.map_mk]
      · change s(Pl.pt (nd T (l.1 + 1) l.1.2
            (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).a e)))),
          Pl.pt (nd T (l.1 + 1) l.1.2
            (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).b e))))) = _
        simp only [inpZ, hT, pr, Sym2.map_mk]
    rw [← h4, Sym2.eq_iff] at h3
    exact h3.imp id And.symm
  card n o z := card_consM (eZ R FL Pl z)
  cap n o x := hcap n o _

end Plan

end Nc.Tow
