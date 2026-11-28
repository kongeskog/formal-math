/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.EndB

/-!
# The tower plan: possible outcomes, units between a node and its parent
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

section Ends

variable {F : Type} [CommRing F] {h b D J m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}

/-- The outcome of a move is possible. -/
def PossM (lhat : ℕ) (n : Fin AA → Fin AA → ℕ)
    (o : NM R ch FL → ℕ) (ub : ℕ) (mv : Mv R ch FL) : Prop :=
  ∃ i : Fin (num lhat n o mv * ub) → (kindM FL mv).I, ∀ ν,
    o ⟨mv, ν⟩ = (∑ k, ((kindM FL mv).lam + (kindM FL mv).len (i k) ν)) / ub

section

variable {n : Fin AA → Fin AA → ℕ} {o : NM R ch FL → ℕ} {ub : ℕ}

theorem poss_inl (hub : 0 < ub) {x : {x : RM T m AA // okR R ch x}} (hp : PossM lhat n o ub (.inl x))
    (ν : (kindM FL (.inl x)).Cn) : o ⟨.inl x, ν⟩ = num lhat n o (.inl x) := by
  obtain ⟨i, hi⟩ := hp
  rw [hi ν]
  have h1 : ∀ k, ((kindM FL (.inl x)).lam + (kindM FL (.inl x)).len (i k) ν) = 1 := fun _ => rfl
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one]
  exact Nat.mul_div_cancel _ hub

theorem poss_inr (hub : 0 < ub) {l : LMv FL} (hp : PossM lhat n o ub (.inr l)) :
    GoodL o l (num lhat n o (.inr l)) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin (num lhat n o (.inr l) * ub) → (FL.L l.2.2.2).I, ∀ ν : (FL.L l.2.2.2).Cn,
    o ⟨.inr l, ν⟩ = (∑ k, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν)) / ub := hp
  unfold GoodL
  revert i
  generalize num lhat n o (.inr l) = t
  intro i hi
  have hi' : ∀ ν : (FL.L l.2.2.2).Cn, o ⟨.inr l, ν⟩ * ub ≤ ∑ k, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν) := by
    intro ν
    rw [hi ν]
    exact Nat.div_mul_le_self _ _
  have h1 : ∑ ν : (FL.L l.2.2.2).Cn, (o ⟨.inr l, ν⟩ * ub) ^ 2 ≤
      (t * ub) * ∑ k : Fin (t * ub), ∑ ν : (FL.L l.2.2.2).Cn, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν) ^ 2 := by
    calc _ ≤ ∑ ν : (FL.L l.2.2.2).Cn, (∑ k : Fin (t * ub), ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν)) ^ 2 :=
          Finset.sum_le_sum fun ν _ => Nat.pow_le_pow_left (hi' ν) 2
      _ ≤ ∑ ν : (FL.L l.2.2.2).Cn, (t * ub) * ∑ k : Fin (t * ub), ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν) ^ 2 := by
          refine Finset.sum_le_sum fun ν _ => ?_
          have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin (t * ub))))
            (f := fun k => ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν))
          rwa [card_univ, Fintype.card_fin] at this
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  have h2 : b * ∑ k : Fin (t * ub), ∑ ν : (FL.L l.2.2.2).Cn, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν) ^ 2 ≤
      (t * ub) * FL.G₁ := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ _k : Fin (t * ub), FL.G₁ := Finset.sum_le_sum fun k _ => FL.L2 l.2.2.2 (i k)
      _ = _ := by simp
  have h3 : (b * ∑ ν : (FL.L l.2.2.2).Cn, o ⟨.inr l, ν⟩ ^ 2) * ub ^ 2 ≤ (FL.G₁ * t ^ 2) * ub ^ 2 := by
    have e1 : (b * ∑ ν : (FL.L l.2.2.2).Cn, o ⟨.inr l, ν⟩ ^ 2) * ub ^ 2 =
        b * ∑ ν : (FL.L l.2.2.2).Cn, (o ⟨.inr l, ν⟩ * ub) ^ 2 := by
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun ν _ => by rw [mul_pow]
    rw [e1]
    calc _ ≤ b * ((t * ub) * ∑ k : Fin (t * ub), ∑ ν : (FL.L l.2.2.2).Cn, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν) ^ 2) :=
          Nat.mul_le_mul_left _ h1
      _ = (t * ub) * (b * ∑ k : Fin (t * ub), ∑ ν : (FL.L l.2.2.2).Cn, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len (i k) ν) ^ 2) := by ring
      _ ≤ (t * ub) * ((t * ub) * FL.G₁) := Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h3 (by positivity)

/-- Possible outcomes are good. -/
theorem poss_good (hub : 0 < ub) {mv : Mv R ch FL} (hp : PossM lhat n o ub mv) : GoodMv lhat n o mv := by
  rcases mv with x | l
  · exact fun ν => poss_inl hub hp ν
  · refine ⟨poss_inr hub hp, fun ν => ?_⟩
    obtain ⟨i, hi⟩ := hp
    rw [hi ν, Nat.le_div_iff_mul_le hub]
    calc num lhat n o (.inr l) * ub = ∑ _k : Fin (num lhat n o (.inr l) * ub), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun k _ => (FL.lam_pos l.2.2.2).trans (Nat.le_add_right _ _)

/-- If the outcomes are good, all full units are alive. -/
theorem alv_good (ν : NM R _ FL) (hp : GoodMv lhat n o ν.1) : alv lhat n o ν = o ν := by
  rcases ν with ⟨x | l, ν⟩
  · have h1 : o ⟨.inl x, ν⟩ = num lhat n o (.inl x) := hp ν
    unfold alv
    rw [alvN_inl, if_pos h1, h1]
  · have h1 : GoodL o l (num lhat n o (.inr l)) := hp.1
    unfold alv
    rw [alvN_inr, if_pos h1]

end

variable {n : Fin AA → Fin AA → Fin (U0 + 1)} {o : (sys R FL Pl).N → Fin U1}

open Classical in
/-- The alive units between a chamber and its parent. -/
noncomputable def AsU (lhat : ℕ)
    (n : Fin AA → Fin AA → Fin (U0 + 1)) (o : (sys R FL Pl).N → Fin U1) (s : Σ j : Fin (J + 1), T.X j) : Finset (Un R FL Pl U0 U1) :=
  univ.filter fun u => ∃ (ν : (sys R FL Pl).N) (kk : Fin U1), u = Uid.new ν kk ∧
    kk.1 < alv lhat (nn n) (oo o) (eN R FL Pl ν) ∧ IsCh (eN R FL Pl ν) s

theorem mem_AsU_new {ν : (sys R FL Pl).N} {kk : Fin U1} {s : Σ j : Fin (J + 1), T.X j} :
    (Uid.new ν kk : Un R FL Pl U0 U1) ∈ AsU lhat n o s ↔
      kk.1 < alv lhat (nn n) (oo o) (eN R FL Pl ν) ∧ IsCh (eN R FL Pl ν) s := by
  classical
  unfold AsU
  rw [mem_filter]
  constructor
  · rintro ⟨-, ν', k', he, h1, h2⟩
    obtain ⟨rfl, rfl⟩ := Uid.new.inj he
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mem_univ _, ν, kk, rfl, h1, h2⟩

theorem mem_AsU_init {a c : Fin AA} {kk : Fin U0} {s : Σ j : Fin (J + 1), T.X j} :
    (Uid.init a c kk : Un R FL Pl U0 U1) ∉ AsU lhat n o s := by
  classical
  unfold AsU
  rw [mem_filter]
  rintro ⟨-, ν', k', he, -⟩
  cases he

theorem card_AsU (hb : 0 < b) (hh : 0 < h) (s : Σ j : Fin (J + 1), T.X j) :
    (AsU lhat n o s : Finset (Un R FL Pl U0 U1)).card ≤ fb (lev (load lhat (nn n) (oo o))) s.1.1 s.2 := by
  classical
  obtain ⟨j, c⟩ := s
  have h1 : (AsU lhat n o ⟨j, c⟩ : Finset (Un R FL Pl U0 U1)).card =
      ∑ u : Un R FL Pl U0 U1, if u ∈ AsU lhat n o ⟨j, c⟩ then 1 else 0 := by
    rw [← card_filter, filter_mem_eq_inter, univ_inter]
  rw [h1, sum_units]
  have h2 : (∑ a, ∑ c', ∑ kk, if (Uid.init a c' kk : Un R FL Pl U0 U1) ∈ AsU lhat n o ⟨j, c⟩ then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c' _ => Finset.sum_eq_zero fun kk _ => if_neg mem_AsU_init
  rw [h2, Nat.zero_add]
  refine le_trans ?_ (sum_child (n := nn n) (o := oo o) hb hh j.1
    (Nat.le_of_lt_succ j.2) c)
  rw [← Equiv.sum_comp (eN R FL Pl)]
  refine Finset.sum_le_sum fun ν _ => ?_
  have hle : alv lhat (nn n) (oo o) (eN R FL Pl ν) ≤ U1 := (alvN_le _ _).trans (o _).2.le
  by_cases hc : IsCh (eN R FL Pl ν) ⟨j, c⟩
  · refine le_trans ?_ (le_of_eq (if_pos hc).symm)
    calc (∑ kk : Fin U1, if (Uid.new ν kk : Un R FL Pl U0 U1) ∈ AsU lhat n o ⟨j, c⟩ then 1 else 0) ≤
        ∑ kk : Fin U1, if kk.1 < alv lhat (nn n) (oo o) (eN R FL Pl ν) then 1 else 0 := by
          refine Finset.sum_le_sum fun kk _ => ?_
          by_cases h3 : (Uid.new ν kk : Un R FL Pl U0 U1) ∈ AsU lhat n o ⟨j, c⟩
          · rw [if_pos h3, if_pos (mem_AsU_new.1 h3).1]
          · rw [if_neg h3]; exact Nat.zero_le _
      _ = ((univ : Finset (Fin U1)).filter fun kk => kk.1 < alv lhat (nn n) (oo o) (eN R FL Pl ν)).card := by
          rw [card_filter]
      _ ≤ _ := (card_fin_lt' _ _ hle).le
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    exact Finset.sum_eq_zero fun kk _ => if_neg fun hm => hc (mem_AsU_new.1 hm).2

open Classical in
/-- Dead units of good outcomes: the last unit of every channel. -/
noncomputable def deadU (U0 : ℕ) (o : (sys R FL Pl).N → Fin U1) :
    Finset (Un R FL Pl U0 U1) := univ.image fun ν => Uid.new ν (o ν)

end Ends

end Nc.Tow
