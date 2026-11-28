/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Net

/-!
# The tower plan: numbers

`num mv` is the number of units given in a move, `alv ν` the number of alive units of a channel, `ld τ` the number
of alive units with target `τ`, as functions of the numbers `n` of initial units and of the outcomes `o`.
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b J m Uu AA : ℕ} {T : Tower h b J} (R : Routes T m Uu)
  (ch : Fin AA ↪ T.X 0) (FL : FlagLaws F T) (lhat : ℕ) (n : Fin AA → Fin AA → ℕ)
  (o : NM R ch FL → ℕ)

noncomputable instance : DecidableEq (NM R ch FL) := Classical.decEq _

noncomputable instance : Fintype (NM R ch FL) :=
  inferInstanceAs (Fintype (Σ mv : Mv R ch FL, (kindM FL mv).Cn))

/-- Every base party has at most `lhat` units at the beginning. -/
def Valid : Prop := ∀ a, ∑ c, (if c = a then 0 else n a c + n c a) ≤ lhat

instance : Decidable (Valid lhat n) := by unfold Valid; infer_instance

/-- Initial units with target `τ`. -/
noncomputable def bt (τ : Tg T m AA) : ℕ :=
  if Valid lhat n then ∑ a, ∑ c, ((range (n a c)).filter fun k => tgB R ch a c k = τ).card else 0

variable {R ch FL}

/-- The outcome of a law move is good for `t` units. -/
def GoodL (l : LMv FL) (t : ℕ) : Prop :=
  b * ∑ ν : (FL.L l.2.2.2).Cn, (o ⟨Sum.inr l, ν⟩) ^ 2 ≤ FL.G₁ * t ^ 2

instance (l : LMv FL) (t : ℕ) : Decidable (GoodL o l t) := by unfold GoodL; infer_instance

/-- The number of alive units of a channel, if `t` units are given in its move. -/
def alvN : NM R ch FL → ℕ → ℕ
  | ⟨.inl x, ν⟩, t => if o ⟨.inl x, ν⟩ = t then t else 0
  | ⟨.inr l, ν⟩, t => if GoodL o l t then o ⟨.inr l, ν⟩ else min (o ⟨.inr l, ν⟩) t

/-- The number of alive units with target `τ`. -/
noncomputable def ld (N : Mv R ch FL → ℕ) (τ : Tg T m AA) : ℕ :=
  bt R ch lhat n τ + ∑ ν : NM R ch FL, if tgM ν.1 ν.2 = τ then alvN o ν (N ν.1) else 0

/-- The squares of the loads of a type. -/
def sqs (L : Tg T m AA → ℕ) (j : Fin (J + 1)) (i : Fin h) : ℕ :=
  ∑ e : T.Ed j, if T.ty e = i then L (.edge j e) ^ 2 else 0

/-- The type `i` is chosen at stage `j`. -/
def IsMin (L : Tg T m AA → ℕ) (j : Fin (J + 1)) (i : Fin h) : Prop :=
  (∀ i', sqs L j i ≤ sqs L j i') ∧ ∀ i' < i, ¬ ∀ i'', sqs L j i' ≤ sqs L j i''

/-- The first index with the smallest value is unique (`IsMin` is the case `f = sqs L j`). -/
theorem firstMin_eq {h : ℕ} {f : Fin h → ℕ} {i i' : Fin h}
    (h1 : (∀ k, f i ≤ f k) ∧ ∀ k < i, ¬ ∀ k', f k ≤ f k')
    (h2 : (∀ k, f i' ≤ f k) ∧ ∀ k < i', ¬ ∀ k', f k ≤ f k') : i = i' := by
  rcases lt_trichotomy i i' with hlt | heq | hlt
  · exact absurd h1.1 (h2.2 i hlt)
  · exact heq
  · exact absurd h2.1 (h1.2 i' hlt)

/-- The chosen type is unique. -/
theorem isMin_eq {L : Tg T m AA → ℕ} {j : Fin (J + 1)} {i i' : Fin h} (h1 : IsMin L j i)
    (h2 : IsMin L j i') : i = i' := firstMin_eq h1 h2

/-- The relay is active. -/
def ActR (L : Tg T m AA → ℕ) : RM T m AA → Prop
  | .inn j i _ => IsMin L j.castSucc i
  | .mid j e s => s = 0 → IsMin L j.castSucc (T.ty e)
  | _ => True

/-- The pair of a slot. -/
def pr (d : FL.Di) (e : (FL.L d).Sl) : Sym2 T.Fl := s(FL.ro d ((FL.L d).a e), FL.ro d ((FL.L d).b e))

/-- The number of slots on a pair. -/
def slo (d : FL.Di) (q : Sym2 T.Fl) : ℕ := (univ.filter fun e : (FL.L d).Sl => pr d e = q).card

/-- The end segments fit into `t` units at every slot. -/
def Fits (L : Tg T m AA → ℕ) (l : LMv FL) (t : ℕ) : Prop :=
  ∀ q : Sym2 T.Fl, ¬ q.IsDiag → L (.seg l.1 l.2.1 l.2.2.1 q) ≤ slo l.2.2.2 q * t

/-- The same vertex with another kind of law. -/
def withD (l : LMv FL) (d : FL.Di) : LMv FL := ⟨l.1, l.2.1, l.2.2.1, d⟩

/-- The number of units at a vertex. -/
noncomputable def tmin (L : Tg T m AA → ℕ) (l : LMv FL) : ℕ := sInf {t | ∃ d, Fits L (withD l d) t}

/-- The kind of law that is used at a vertex. -/
def Pick (L : Tg T m AA → ℕ) (l : LMv FL) : Prop :=
  Fits L l (tmin L l) ∧ ∀ d, (Fintype.equivFin FL.Di d) < (Fintype.equivFin FL.Di l.2.2.2) →
    ¬ Fits L (withD l d) (tmin L l)

/-- The chosen kind of law is unique. -/
theorem pick_eq {L : Tg T m AA → ℕ} {l : LMv FL} {d : FL.Di} (h1 : Pick L l)
    (h2 : Pick L (withD l d)) : l.2.2.2 = d := by
  rcases lt_trichotomy (Fintype.equivFin FL.Di d) (Fintype.equivFin FL.Di l.2.2.2) with
      hlt | heq | hlt
  · exact absurd h2.1 (h1.2 d hlt)
  · exact ((Fintype.equivFin FL.Di).injective heq).symm
  · exact absurd h1.1 (h2.2 l.2.2.2 hlt)

open Classical in
/-- The number of units of a move, from the loads. -/
noncomputable def numF (L : Tg T m AA → ℕ) : Mv R ch FL → ℕ
  | .inl x => if ActR L x.1 then L (inpR x.1) else 0
  | .inr l => if Pick L l then tmin L l else 0

/-- The numbers of units of the moves with times less than `τ`. -/
noncomputable def numS : ℕ → Mv R ch FL → ℕ
  | 0, _ => 0
  | τ + 1, mv => if timeM mv = τ then numF (ld lhat n o (numS τ)) mv else numS τ mv

/-- The end of time. -/
def tend (J m : ℕ) : ℕ := 2 * m + 6 * J + 1

/-- The number of units of a move. -/
noncomputable def num (mv : Mv R ch FL) : ℕ := numS lhat n o (tend J m) mv

/-- The number of alive units of a channel. -/
noncomputable def alv (ν : NM R ch FL) : ℕ := alvN o ν (num lhat n o ν.1)

/-- The number of alive units with target `τ`. -/
noncomputable def load (τ : Tg T m AA) : ℕ := ld lhat n o (num lhat n o) τ

/-- The outcome of a move is good: exact for relays; not too long and not too short for laws. -/
def GoodMv : Mv R ch FL → Prop
  | .inl x => ∀ ν : (kindM FL (.inl x)).Cn, o ⟨.inl x, ν⟩ = num lhat n o (.inl x)
  | .inr l => GoodL o l (num lhat n o (.inr l)) ∧
      ∀ ν : (kindM FL (.inr l)).Cn, num lhat n o (.inr l) ≤ o ⟨.inr l, ν⟩

variable {lhat n o}

theorem alvN_inl (x : {x : RM T m AA // okR R ch x}) (ν : (kindM FL (.inl x)).Cn) (t : ℕ) :
    alvN o ⟨.inl x, ν⟩ t = if o ⟨.inl x, ν⟩ = t then t else 0 := rfl

theorem alvN_inr (l : LMv FL) (ν : (kindM FL (.inr l)).Cn) (t : ℕ) :
    alvN o ⟨.inr l, ν⟩ t = if GoodL o l t then o ⟨.inr l, ν⟩ else min (o ⟨.inr l, ν⟩) t := rfl

theorem goodMv_inl (x : {x : RM T m AA // okR R ch x}) : GoodMv lhat n o (.inl x) ↔
    ∀ ν : (kindM FL (.inl x)).Cn, o ⟨.inl x, ν⟩ = num lhat n o (.inl x) := Iff.rfl

theorem goodMv_inr (l : LMv FL) : GoodMv lhat n o (.inr l) ↔
    GoodL o l (num lhat n o (.inr l)) ∧
      ∀ ν : (kindM FL (.inr l)).Cn, num lhat n o (.inr l) ≤ o ⟨.inr l, ν⟩ := Iff.rfl

theorem alv_inr (l : LMv FL) (ν : (FL.L l.2.2.2).Cn) : alv lhat n o ⟨.inr l, ν⟩ =
    if GoodL o l (num lhat n o (.inr l)) then o ⟨.inr l, ν⟩
    else min (o ⟨.inr l, ν⟩) (num lhat n o (.inr l)) := rfl

theorem inpR_mid (j : Fin J) (e : T.Ed j) (s : Fin 4) : inpR (.mid j e s : RM T m AA) =
    if s = 0 then .edge j.castSucc e else .nxt (.mid j e s) := rfl

theorem alvN_le (ν : NM R ch FL) (t : ℕ) : alvN o ν t ≤ o ν := by
  rcases ν with ⟨x | l, ν⟩
  · rw [alvN_inl]
    split_ifs with h
    · exact h.ge
    · exact Nat.zero_le _
  · rw [alvN_inr]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _

theorem alvN_zero (ν : NM R ch FL) : alvN o ν 0 = 0 := by
  rcases ν with ⟨x | l, ν⟩
  · rw [alvN_inl]
    split_ifs <;> rfl
  · rw [alvN_inr]
    split_ifs with h
    · unfold GoodL at h
      have h1 : b * ∑ ν : (FL.L l.2.2.2).Cn, (o ⟨Sum.inr l, ν⟩) ^ 2 = 0 := by simpa using h
      have h2 : ∑ ν : (FL.L l.2.2.2).Cn, (o ⟨Sum.inr l, ν⟩) ^ 2 = 0 := by
        rcases Nat.mul_eq_zero.1 h1 with h3 | h3
        · have := T.b_pos; omega
        · exact h3
      have h3 := (Finset.sum_eq_zero_iff.1 h2) ν (mem_univ _)
      exact pow_eq_zero_iff (by norm_num) |>.1 h3
    · exact Nat.min_zero _

theorem timeM_lt (mv : Mv R ch FL) : timeM mv < tend J m := by
  unfold tend
  rcases mv with ⟨x, hx⟩ | l
  · change timeR x < _
    rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
    · have := s.2; simp only [timeR]; omega
    · have := j.2; simp only [timeR]; omega
    · have := j.2; have := s.2; simp only [timeR]; omega
    · simp only [timeR]; omega
  · have := l.1.2
    simp only [timeM]; omega

theorem numS_zero_of_le {τ : ℕ} {mv : Mv R ch FL} (h : τ ≤ timeM mv) : numS lhat n o τ mv = 0 := by
  induction τ with
  | zero => rfl
  | succ τ ih =>
    rw [numS, if_neg (by omega)]
    exact ih (by omega)

theorem numS_stable {τ : ℕ} {mv : Mv R ch FL} (h : timeM mv < τ) :
    numS lhat n o τ mv =
      numF (ld lhat n o (numS lhat n o (timeM mv))) mv := by
  induction τ with
  | zero => omega
  | succ τ ih =>
    rw [numS]
    by_cases h1 : timeM mv = τ
    · rw [if_pos h1, h1]
    · rw [if_neg h1]
      exact ih (by omega)

theorem numS_eq (τ : ℕ) (mv : Mv R ch FL) :
    numS lhat n o τ mv = if timeM mv < τ then num lhat n o mv else 0 := by
  split_ifs with h
  · rw [numS_stable h, num, numS_stable (timeM_lt mv)]
  · exact numS_zero_of_le (not_lt.1 h)

/-- The time until which all channels with this target have been made. -/
def tgTime : Tg T m AA → ℕ
  | .done => tend J m
  | .edge j _ => 2 * m + 6 * j
  | .nxt x => timeR x
  | .seg j _ _ _ => 2 * m + 6 * j + 4

theorem edgeO_time (e : Option (T.Ed 0)) : 2 * m ≤ tgTime (edgeO e : Tg T m AA) := by
  cases e
  · simp only [edgeO, tgTime, tend]; omega
  · simp [edgeO, tgTime]

theorem tg_time (ν : NM R ch FL) : timeM ν.1 < tgTime (tgM ν.1 ν.2) := by
  rcases ν with ⟨⟨x, hx⟩ | l, ν⟩
  · change timeR x < tgTime (tgR R ch x ν)
    rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
    · have hs := s.2
      cases ν
      · refine lt_of_lt_of_le ?_ (edgeO_time _)
        exact hs
      · simp only [tgR]
        split_ifs
        · simp only [tgTime, timeR]; omega
        · refine lt_of_lt_of_le ?_ (edgeO_time _)
          exact hs
    · have := j.2
      simp only [tgR, tgTime, timeR, tend]; omega
    · have := j.2
      cases ν
      · fin_cases s
        · simp only [Fin.zero_eta, tgR, Matrix.cons_val_zero, tgTime, timeR, tend]
          change 2 * m + 6 * j.1 + 0 < _
          omega
        · simp [tgR, tgTime, timeR]
        · change 2 * m + 6 * j.1 + 2 < 2 * m + 6 * (j.1 + 1)
          omega
        · simp [tgR, tgTime, timeR]
      · fin_cases s
        · simp only [tgR, timeR, Fin.zero_eta, Matrix.cons_val_zero]
          split_ifs <;> simp [tgTime, timeR]
        · simp [tgR, tgTime, timeR]
        · simp only [tgR, timeR, Fin.reduceFinMk, Matrix.cons_val]
          split_ifs
          · simp [tgTime, timeR]
          · change 2 * m + 6 * j.1 + 2 < 2 * m + 6 * J + 1
            omega
        · change 2 * m + 6 * j.1 + 3 < 2 * m + 6 * J + 1
          omega
    · simp only [tgR, tgTime, timeR, tend]; omega
  · have := l.1.2
    simp only [tgM, tgTime, timeM, Fin.val_succ]
    omega

theorem ld_numS {τ : Tg T m AA} {t : ℕ} (h : tgTime τ ≤ t) :
    ld lhat n o (numS lhat n o t) τ = load lhat n o τ := by
  unfold load ld
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs with hν
  · have := tg_time ν
    rw [hν] at this
    rw [numS_eq, if_pos (by omega)]
  · rfl

theorem inp_time (x : RM T m AA) : tgTime (inpR x) ≤ timeR x := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · simp [inpR, tgTime]
  · simp [inpR, tgTime, timeR]
  · rw [inpR_mid]
    split_ifs with hs
    · simp [tgTime, timeR]
    · simp [tgTime]
  · simp [inpR, tgTime, timeR]

section

-- Two load functions `L` and `L'` that agree on the relevant tags.
variable {L L' : Tg T m AA → ℕ}

theorem sqs_congr {j : Fin (J + 1)} (hL : ∀ e, L (.edge j e) = L' (.edge j e)) (i : Fin h) :
    sqs L j i = sqs L' j i := by
  unfold sqs
  simp only [hL]

theorem isMin_congr {j : Fin (J + 1)} (hL : ∀ e, L (.edge j e) = L' (.edge j e)) (i : Fin h) :
    IsMin L j i ↔ IsMin L' j i := by
  unfold IsMin
  simp only [sqs_congr hL]

theorem fits_congr {l : LMv FL}
    (hL : ∀ q, L (.seg l.1 l.2.1 l.2.2.1 q) = L' (.seg l.1 l.2.1 l.2.2.1 q)) (s : ℕ) :
    Fits L l s ↔ Fits L' l s := by
  unfold Fits
  simp only [hL]

theorem tmin_congr {l : LMv FL}
    (hL : ∀ q, L (.seg l.1 l.2.1 l.2.2.1 q) = L' (.seg l.1 l.2.1 l.2.2.1 q)) :
    tmin L l = tmin L' l := by
  unfold tmin
  congr 1
  ext s
  simp only [Set.mem_setOf_eq]
  exact exists_congr fun d => fits_congr (l := withD l d) hL s

theorem pick_congr {l : LMv FL}
    (hL : ∀ q, L (.seg l.1 l.2.1 l.2.2.1 q) = L' (.seg l.1 l.2.1 l.2.2.1 q)) :
    Pick L l ↔ Pick L' l := by
  unfold Pick
  rw [tmin_congr hL, fits_congr hL]
  refine and_congr_right fun _ => forall_congr' fun d => imp_congr_right fun _ => not_congr ?_
  exact fits_congr (l := withD l d) hL _

theorem actR_congr {x : RM T m AA}
    (hL : ∀ τ, tgTime τ ≤ timeR x → L τ = L' τ) : ActR L x ↔ ActR L' x := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · exact Iff.rfl
  · exact isMin_congr (fun e => hL _ (by simp [tgTime, timeR])) i
  · exact imp_congr_right fun _ => isMin_congr (fun e => hL _ (by simp [tgTime, timeR])) _
  · exact Iff.rfl

theorem numF_congr {mv : Mv R ch FL}
    (hL : ∀ τ, tgTime τ ≤ timeM mv → L τ = L' τ) : numF L mv = numF L' mv := by
  classical
  rcases mv with ⟨x, hx⟩ | l
  · unfold numF
    simp only [actR_congr (x := x) hL, hL _ (inp_time x)]
  · unfold numF
    have h1 : ∀ q, L (.seg l.1 l.2.1 l.2.2.1 q) = L' (.seg l.1 l.2.1 l.2.2.1 q) := fun q => hL _ le_rfl
    simp only [pick_congr h1, tmin_congr h1]

end

/-- **The numbers of units.** -/
theorem num_eq (mv : Mv R ch FL) :
    num lhat n o mv = numF (load lhat n o) mv := by
  rw [num, numS_stable (timeM_lt mv)]
  exact numF_congr fun τ hτ => ld_numS hτ

section Causal

variable {o' : NM R ch FL → ℕ}

theorem alvN_congr {ν : NM R ch FL} (hν : ∀ c, o ⟨ν.1, c⟩ = o' ⟨ν.1, c⟩) (t : ℕ) :
    alvN o ν t = alvN o' ν t := by
  rcases ν with ⟨x | l, ν⟩
  · rw [alvN_inl, alvN_inl, hν]
  · have hν' : ∀ c : (FL.L l.2.2.2).Cn, o ⟨.inr l, c⟩ = o' ⟨.inr l, c⟩ := hν
    have hg : GoodL o l t ↔ GoodL o' l t := by
      unfold GoodL
      rw [Finset.sum_congr rfl fun c _ => by rw [hν' c]]
    rw [alvN_inr, alvN_inr, hν]
    exact if_congr hg rfl rfl

theorem ld_congr {N : Mv R ch FL → ℕ}
    (hN : ∀ mv, N mv ≠ 0 → ∀ c, o ⟨mv, c⟩ = o' ⟨mv, c⟩) (τ : Tg T m AA) :
    ld lhat n o N τ = ld lhat n o' N τ := by
  unfold ld
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs
  · by_cases h0 : N ν.1 = 0
    · rw [h0, alvN_zero, alvN_zero]
    · exact alvN_congr (hN ν.1 h0) _
  · rfl

theorem numS_congr {t : ℕ} (ho : ∀ mv : Mv R ch FL, timeM mv < t →
    ∀ c, o ⟨mv, c⟩ = o' ⟨mv, c⟩) :
    numS lhat n o t = numS lhat n o' t := by
  induction t with
  | zero => funext mv; rfl
  | succ t ih =>
    have ih' := ih fun mv hmv => ho mv (by omega)
    funext mv
    rw [numS, numS, ← ih']
    split_ifs with h1
    · refine numF_congr fun τ _ => ld_congr ?_ τ
      intro mv' hmv'
      refine ho mv' ?_
      by_contra hcon
      exact hmv' (numS_zero_of_le (by omega))
    · rfl

theorem num_congr {mv : Mv R ch FL}
    (ho : ∀ mv' : Mv R ch FL, timeM mv' < timeM mv → ∀ c, o ⟨mv', c⟩ = o' ⟨mv', c⟩) :
    num lhat n o mv = num lhat n o' mv := by
  rw [num, num, numS_stable (timeM_lt mv), numS_stable (timeM_lt mv), numS_congr ho]
  refine numF_congr fun τ _ => ld_congr ?_ τ
  intro mv' hmv'
  refine ho mv' ?_
  by_contra hcon
  exact hmv' (numS_zero_of_le (by omega))

theorem load_congr {τ : Tg T m AA} {t : ℕ} (hτ : tgTime τ ≤ t)
    (ho : ∀ mv' : Mv R ch FL, timeM mv' < t → ∀ c, o ⟨mv', c⟩ = o' ⟨mv', c⟩) :
    load lhat n o τ = load lhat n o' τ := by
  rw [← ld_numS hτ, ← ld_numS hτ, numS_congr ho]
  refine ld_congr ?_ τ
  intro mv' hmv'
  refine ho mv' ?_
  by_contra hcon
  exact hmv' (numS_zero_of_le (by omega))

theorem good_congr {mv : Mv R ch FL}
    (ho : ∀ mv' : Mv R ch FL, timeM mv' < timeM mv → ∀ c, o ⟨mv', c⟩ = o' ⟨mv', c⟩)
    (ho' : ∀ c, o ⟨mv, c⟩ = o' ⟨mv, c⟩) : GoodMv lhat n o mv ↔ GoodMv lhat n o' mv := by
  have hnum := num_congr (lhat := lhat) (n := n) ho
  rcases mv with x | l
  · simp only [goodMv_inl, hnum, ho']
  · have ho'' : ∀ c : (FL.L l.2.2.2).Cn, o ⟨.inr l, c⟩ = o' ⟨.inr l, c⟩ := ho'
    simp only [goodMv_inr, GoodL, hnum, ho', ho'']

end Causal

end Nc.Tow
