/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Ever3
import Nc.Tow.Plan
import Nc.G.RouteFacts

/-!
# The units that a party ever holds, and the units of zeros
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000

namespace Nc.G

open Finset

section Held

variable {F : Type} [CommRing F] {A A' E U0 U1 : ℕ}

/-- The number of initial units of a party. -/
def initN (n : Fin A → Fin A → Fin (U0 + 1)) (p : Fin (A + A')) : ℕ :=
  ∑ a, ∑ c, ((if Fin.castAdd A' a = p then (n a c).1 else 0) + if Fin.castAdd A' c = p then (n a c).1 else 0)

theorem sum_fin_le (N c : ℕ) (p : Prop) [Decidable p] :
    (∑ k : Fin N, if p ∧ k.1 < c then 1 else 0) ≤ if p then c else 0 := by
  by_cases hp : p
  · simp only [hp, true_and, if_true]
    rw [← card_filter, Fin.card_filter_val_lt]
    exact min_le_right _ _
  · simp [hp]

open Classical in
/-- The units of a party, by their channels. -/
theorem held_le_chan (M : Sys F (A + A') E) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1) (p : Fin (A + A')) :
    ((Plan.seenAt n o E : Finset (Uid A U0 M.N U1)).filter (Holds (hold0 M.np) (hold1 M.np) p)).card ≤
      initN n p + ∑ ν : M.N, ∑ d : Bool, if M.np ν d = p then (o ν).1 + 1 else 0 := by
  have h1 : ((Plan.seenAt n o E : Finset (Uid A U0 M.N U1)).filter (Holds (hold0 M.np) (hold1 M.np) p)).card ≤
      ∑ u : Uid A U0 M.N U1, ∑ d : Bool, if cparty M.np u d = p ∧ unum u < ucnt n o u then 1 else 0 := by
    rw [card_filter]
    refine (Finset.sum_le_sum fun u hu => ?_).trans (Finset.sum_le_sum_of_subset (subset_univ _))
    have h4 := Plan.mem_seenAt_end.1 hu
    split_ifs with h3
    · rw [Fintype.sum_bool]
      rcases h3 with h3 | h3
      · have h5 : cparty M.np u false = p := h3.symm
        rw [if_pos (⟨h5, h4⟩ : cparty M.np u false = p ∧ unum u < ucnt n o u)]
        exact Nat.le_add_left _ _
      · have h5 : cparty M.np u true = p := h3.symm
        rw [if_pos (⟨h5, h4⟩ : cparty M.np u true = p ∧ unum u < ucnt n o u)]
        exact Nat.le_add_right _ _
    · exact Nat.zero_le _
  refine h1.trans ?_
  rw [Tow.sum_units]
  refine add_le_add ?_ ?_
  · unfold initN
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => ?_
    rw [Finset.sum_comm, Fintype.sum_bool, Nat.add_comm]
    exact add_le_add (sum_fin_le U0 (n a c).1 (Fin.castAdd A' a = p)) (sum_fin_le U0 (n a c).1 (Fin.castAdd A' c = p))
  · refine Finset.sum_le_sum fun ν _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun d _ => sum_fin_le U1 ((o ν).1 + 1) (M.np ν d = p)

end Held

end Nc.G

namespace Nc.Tow

open Finset Nc.G

/-- Sums over a subtype. -/
theorem sum_sub_le {κ : Type*} [Fintype κ] (p : κ → Prop) [Fintype {x // p x}] (f : κ → ℕ) :
    ∑ x : {x // p x}, f x.1 ≤ ∑ x, f x := by
  classical
  rw [← Finset.sum_subtype (univ.filter p) (by simp) f]
  exact Finset.sum_le_sum_of_subset (subset_univ _)

variable {F : Type} [CommRing F] {h b J m Uu AA A' U0 U1 : ℕ} {T : Tower h b J} (R : Routes T m Uu)
  {ch : Fin AA ↪ T.X 0} (FL : FlagLaws F T) (Pl : Place T ch A') (lhat : ℕ)
  (n : Fin AA → Fin AA → Fin (U0 + 1)) (o : (sys R FL Pl).N → Fin U1)

open Classical in
/-- The number of units that a party ever holds. -/
noncomputable def heldN (p : Fin (AA + A')) : ℕ :=
  ((Plan.seenAt n o (Fintype.card (Mv T R ch FL)) : Finset (Un R FL Pl U0 U1)).filter
    (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) p)).card

/-- The number of ends of channels at a party. -/
noncomputable def chanN (p : Fin (AA + A')) : ℕ := ∑ ν : (sys R FL Pl).N, ∑ d : Bool,
  if (sys R FL Pl).np ν d = p then 1 else 0

variable {R FL Pl lhat n o}

section

variable
  -- every move is good (`GoodMv`): relays exact, laws neither too long nor too short
  (hg : ∀ mv, GoodMv lhat (nn n) (oo o) mv)

include hg in
/-- The outcome of a law move is not large. -/
theorem law_le (l : LMv T FL) (ν : (FL.L l.2.2.2).Cn) :
    oo o ⟨.inr l, ν⟩ ≤ FL.G₁ * num lhat (nn n) (oo o) (.inr l) := by
  have h1 := (hg (.inr l)).1
  unfold GoodL at h1
  set t := num lhat (nn n) (oo o) (.inr l) with ht
  have h2 : (oo o ⟨.inr l, ν⟩) ^ 2 ≤ ∑ ν : (FL.L l.2.2.2).Cn, (oo o ⟨Sum.inr l, ν⟩) ^ 2 :=
    Finset.single_le_sum (f := fun ν : (FL.L l.2.2.2).Cn => (oo o ⟨Sum.inr l, ν⟩) ^ 2)
      (fun _ _ => Nat.zero_le _) (mem_univ ν)
  have h3 : (oo o ⟨.inr l, ν⟩) ^ 2 ≤ FL.G₁ * t ^ 2 := by
    refine h2.trans (le_trans ?_ h1)
    exact Nat.le_mul_of_pos_left _ T.b_pos
  have h4 : (oo o ⟨.inr l, ν⟩) ^ 2 ≤ (FL.G₁ * t) ^ 2 := by
    refine h3.trans ?_
    rw [mul_pow]
    refine Nat.mul_le_mul_right _ ?_
    rw [pow_two]
    exact Nat.le_mul_self _
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h4

include hg in
open Classical in
/-- The units of a law move at a node. -/
theorem law_node (l : LMv T FL) (P : Nd T) : (∑ ν : (FL.L l.2.2.2).Cn, ∑ d : Bool,
    if nd T (l.1 + 1) l.1.2 (atv l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).cnEnd ν d))) = P then
      oo o ⟨.inr l, ν⟩ else 0) ≤ 2 * Fintype.card T.Nr * FL.G₁ *
    ∑ f : T.Fl, if nd T (l.1 + 1) l.1.2 (atv l.2.1 l.2.2.1 f) = P then
      num lhat (nn n) (oo o) (.inr l) else 0 := by
  set t := num lhat (nn n) (oo o) (.inr l) with ht
  set S := ∑ f : T.Fl, if nd T (l.1 + 1) l.1.2 (atv l.2.1 l.2.2.1 f) = P then t else 0 with hS
  have h5 : ∀ (ν : (FL.L l.2.2.2).Cn) (d : Bool),
      (if nd T (l.1 + 1) l.1.2 (atv l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).cnEnd ν d)))
          = P then oo o ⟨.inr l, ν⟩ else 0) ≤ FL.G₁ * S := by
    intro ν d
    split_ifs with hP
    · refine (law_le hg l ν).trans (Nat.mul_le_mul_left _ ?_)
      refine le_trans ?_ (Finset.single_le_sum (f := fun f : T.Fl =>
        if nd T (l.1 + 1) l.1.2 (atv l.2.1 l.2.2.1 f) = P then t else 0) (fun _ _ => Nat.zero_le _)
        (mem_univ (FL.ro l.2.2.2 ((FL.L l.2.2.2).cnEnd ν d))))
      simp only [hP, if_true]
      exact le_rfl
    · exact Nat.zero_le _
  calc _ ≤ ∑ _ν : (FL.L l.2.2.2).Cn, ∑ _d : Bool, FL.G₁ * S :=
        Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun d _ => h5 ν d
    _ = Fintype.card (FL.L l.2.2.2).Cn * (2 * (FL.G₁ * S)) := by
        rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, card_univ, card_univ, Fintype.card_bool]
    _ = _ := by
        rw [Fintype.card_congr (FL.cn l.2.2.2)]
        ring

include hg

open Classical in
/-- **The units that a party ever holds.** -/
theorem held_le (P : Nd T) : heldN R FL Pl n o (Pl.pt P) ≤ initN (A' := A') n (Pl.pt P) + chanN R FL Pl (Pl.pt P) +
    2 * NR lhat (nn n) (oo o) P +
    2 * Fintype.card T.Nr * FL.G₁ * NL lhat (nn n) (oo o) P := by
  refine (held_le_chan (sys R FL Pl) n o (Pl.pt P)).trans ?_
  have h1 : (∑ ν : (sys R FL Pl).N, ∑ d : Bool, if (sys R FL Pl).np ν d = Pl.pt P then (o ν).1 + 1 else 0) =
      chanN R FL Pl (Pl.pt P) + ∑ ν : (sys R FL Pl).N, ∑ d : Bool,
        if (sys R FL Pl).np ν d = Pl.pt P then (o ν).1 else 0 := by
    unfold chanN
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> omega
  have h2 : (∑ ν : (sys R FL Pl).N, ∑ d : Bool, if (sys R FL Pl).np ν d = Pl.pt P then (o ν).1 else 0) =
      ∑ ν : NM R FL (ch := ch), ∑ d : Bool,
        if partM R ch FL ν.1 ((kindM R ch FL ν.1).cnEnd ν.2 d) = P then oo o ν else 0 := by
    rw [← Equiv.sum_comp (eN R FL Pl)]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun d _ => ?_
    have h3 : oo o (eN R FL Pl ν) = (o ν).1 := by
      unfold oo
      rw [Equiv.symm_apply_apply]
    rw [h3]
    refine if_congr ?_ rfl rfl
    rw [np_eq]
    exact Pl.pt.injective.eq_iff
  rw [h1, h2]
  have h4 : (∑ ν : NM R FL (ch := ch), ∑ d : Bool,
      if partM R ch FL ν.1 ((kindM R ch FL ν.1).cnEnd ν.2 d) = P then oo o ν else 0) ≤
      2 * NR lhat (nn n) (oo o) P +
      2 * Fintype.card T.Nr * FL.G₁ * NL lhat (nn n) (oo o) P := by
    change (∑ ν : (Σ mv : Mv T R ch FL, (kindM R ch FL mv).Cn), ∑ d : Bool,
      if partM R ch FL ν.1 ((kindM R ch FL ν.1).cnEnd ν.2 d) = P then oo o ν else 0) ≤ _
    rw [Fintype.sum_sigma, Fintype.sum_sum_type]
    refine add_le_add ?_ ?_
    · -- relays
      have h5 : ∀ x : {x : RM T m AA // okR T R ch x}, (∑ ν : Bool, ∑ d : Bool,
          if tri T R ch x.1 (if d then (if ν then 2 else 1) else (if ν then 1 else 0)) = P then
            oo o ⟨.inl x, ν⟩ else 0) ≤
          2 * ∑ q : Fin 3, if tri T R ch x.1 q = P then nR lhat (nn n) (oo o) x.1 else 0 := by
        intro x
        have h6 : nR lhat (nn n) (oo o) x.1 = num lhat (nn n) (oo o) (.inl x) := by
          unfold nR
          rw [dif_pos x.2]
        rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fin.sum_univ_three, h6]
        simp only [show ∀ ν : Bool, _ = _ from hg (.inl x), if_true, Bool.false_eq_true, if_false]
        split_ifs <;> omega
      have h7 : (∑ x : {x : RM T m AA // okR T R ch x}, 2 * ∑ q : Fin 3, if tri T R ch x.1 q = P then
          nR lhat (nn n) (oo o) x.1 else 0) ≤ 2 * NR lhat (nn n) (oo o) P := by
        rw [← Finset.mul_sum]
        refine Nat.mul_le_mul_left _ ?_
        exact sum_sub_le (fun x => okR T R ch x) fun x => ∑ q : Fin 3, if tri T R ch x q = P then
          nR lhat (nn n) (oo o) x else 0
      refine le_trans (Finset.sum_le_sum fun x _ => ?_) h7
      refine le_trans (le_of_eq ?_) (h5 x)
      refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun d _ => ?_
      cases ν <;> cases d <;> rfl
    · -- laws
      unfold NL
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun l _ => law_node hg l P
  omega

end

end Nc.Tow
