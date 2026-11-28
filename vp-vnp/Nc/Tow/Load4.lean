/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Load0
import Nc.Tow.Load3

/-!
# The tower plan: bounds for all stages
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b J m Uu AA : ℕ} {T : Tower h b J} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R ch FL → ℕ}

namespace Tower

variable {j : ℕ}

/-- Units at a chamber. -/
def bet (n : T.Ed j → ℕ) (c : T.X j) : ℕ := ∑ e, if T.e0 e = c ∨ T.e1 e = c then n e else 0

theorem card_at (c : T.X j) : (univ.filter fun e : T.Ed j => T.e0 e = c ∨ T.e1 e = c).card ≤ h := by
  have h1 : (univ.filter fun e : T.Ed j => T.e0 e = c ∨ T.e1 e = c).card =
      ∑ i : Fin h, (univ.filter fun e : T.Ed j => T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c)).card := by
    rw [card_eq_sum_card_fiberwise (f := fun e : T.Ed j => T.ty e) (fun _ _ => mem_coe.2 (mem_univ _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [filter_filter]
    congr 1
    ext e
    simp only [mem_filter, mem_univ, true_and]
    exact and_comm
  rw [h1]
  calc _ ≤ ∑ _i : Fin h, 1 := Finset.sum_le_sum fun i _ => T.deg j c i
    _ = h := by simp

/-- Units at a chamber. -/
theorem bet_sq_le (n : T.Ed j → ℕ) (c : T.X j) : T.bet n c ^ 2 ≤ h * ∑ e, n e ^ 2 := by
  unfold bet
  rw [← Finset.sum_filter]
  exact (sq_sum_le _ _ (T.card_at c)).trans
    (Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (subset_univ _)))

theorem sum_bet (n : T.Ed j → ℕ) : ∑ c, T.bet n c = 2 * ∑ e, n e := by
  unfold bet
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h1 : ∀ c, (if T.e0 e = c ∨ T.e1 e = c then n e else 0) =
      (if T.e0 e = c then n e else 0) + if T.e1 e = c then n e else 0 := by
    intro c
    have hne := T.e_ne e
    by_cases h0 : T.e0 e = c
    · have h1 : ¬ T.e1 e = c := fun hh => hne (h0.trans hh.symm)
      simp [h0, h1]
    · by_cases h1 : T.e1 e = c <;> simp [h0, h1]
  rw [Finset.sum_congr rfl fun c _ => h1 c, Finset.sum_add_distrib]
  simp
  ring

/-- All units of a stage. -/
theorem sum_bet_sq_le (n : T.Ed j → ℕ) :
    (∑ c, T.bet n c) ^ 2 ≤ 2 * (h * (Fintype.card (T.X j) * ∑ e, n e ^ 2)) := by
  rw [sum_bet, mul_pow, ← Nat.mul_assoc h, ← two_card_ed]
  exact (Nat.mul_le_mul_left _ (sq_sum_le univ n card_univ.le)).trans (le_of_eq (by ring))

end Tower

/-- Loads of a stage. -/
noncomputable def lds (lhat : ℕ) (n : Fin AA → Fin AA → ℕ)
    (o : NM R ch FL → ℕ) (j : Fin (J + 1)) : T.Ed j → ℕ := fun e => load lhat n o (.edge j e)

/-- The bound for the loads after the start. -/
def nhat (T : Tower h b J) (Uu AA lhat : ℕ) : ℕ := Uu * (lhat / Fintype.card (T.X 0) + 2 * AA)

/-- The bound for the norms: the squares of the loads of a stage, times the number of its chambers, add up to at
most the square of this number. -/
def kbar (FL : FlagLaws F T) (Uu AA lhat : ℕ) : ℕ :=
  Fintype.card (T.X 0) * (h * nhat T Uu AA lhat + 4 * FL.C₁ * FL.a₁)

/-- The conditions against the number of types, the degree and the laws; the factor of a stage is 1/2. -/
structure THypR (FL : FlagLaws F T) : Prop where
  gain : 4 * (1 + 8 * FL.C₁) ≤ h
  three : 3 ≤ b

section

variable (hH : THypR FL)

include hH in
/-- **The norms of the loads**, as squares: `K_j + 16 C₁ a₁² |X^(j)|²` falls by the factor 4 in every stage. -/
theorem kap_le : ∀ j : ℕ, ∀ hj : j < J + 1, 4 ^ j * (Fintype.card (T.X j) * ∑ e, lds lhat n o ⟨j, hj⟩ e ^ 2 +
    8 * FL.C₁ * (2 * FL.a₁ ^ 2) * Fintype.card (T.X j) ^ 2) ≤ kbar FL Uu AA lhat ^ 2 := by
  intro j
  induction j with
  | zero =>
    intro hj
    have h1 : ∑ e : T.Ed 0, lds lhat n o 0 e ^ 2 ≤ h * Fintype.card (T.X 0) * nhat T Uu AA lhat ^ 2 := by
      refine (Finset.sum_le_card_nsmul _ _ _ fun e _ => Nat.pow_le_pow_left (Paper.thm_tree_start e) 2).trans ?_
      rw [smul_eq_mul, card_univ]
      exact Nat.mul_le_mul_right _ ((Nat.le_mul_of_pos_left _ two_pos).trans Tower.two_card_ed.le)
    have h2 : h ≤ h ^ 2 := Nat.le_self_pow two_ne_zero h
    have h3 : FL.C₁ ≤ FL.C₁ ^ 2 := Nat.le_self_pow two_ne_zero _
    unfold kbar
    calc _ ≤ Fintype.card (T.X 0) * (h * Fintype.card (T.X 0) * nhat T Uu AA lhat ^ 2) +
          8 * FL.C₁ * (2 * FL.a₁ ^ 2) * Fintype.card (T.X 0) ^ 2 := by
          rw [pow_zero, one_mul]
          gcongr
          exact h1
      _ = Fintype.card (T.X 0) ^ 2 * (h * nhat T Uu AA lhat ^ 2 + 16 * FL.C₁ * FL.a₁ ^ 2) := by ring
      _ ≤ Fintype.card (T.X 0) ^ 2 * (h ^ 2 * nhat T Uu AA lhat ^ 2 + 16 * FL.C₁ ^ 2 * FL.a₁ ^ 2 +
          2 * (h * nhat T Uu AA lhat) * (4 * FL.C₁ * FL.a₁)) := by
          refine Nat.mul_le_mul_left _ (le_trans ?_ (Nat.le_add_right _ _))
          gcongr
      _ = _ := by ring
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := Paper.thm_tree_kappa (R := R) (ch := ch) (lhat := lhat) (n := n) (o := o) hH.gain ⟨j, by omega⟩
    have h3 : 5 ≤ b ^ 2 := (Nat.pow_le_pow_left hH.three 2).trans' (by norm_num)
    refine le_trans ?_ h1
    rw [pow_succ, mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    rw [T.card_X j (by omega)]
    calc _ = 4 * (Fintype.card (T.X (j + 1)) * ∑ e, lds lhat n o ⟨j + 1, hj⟩ e ^ 2) +
          8 * FL.C₁ * (2 * FL.a₁ ^ 2) * (4 * Fintype.card (T.X (j + 1)) ^ 2) := by ring
      _ ≤ b * Fintype.card (T.X (j + 1)) * ∑ e, lds lhat n o ⟨j, by omega⟩ e ^ 2 +
          8 * FL.C₁ * (2 * FL.a₁ ^ 2) * Fintype.card (T.X (j + 1)) ^ 2 +
          8 * FL.C₁ * (2 * FL.a₁ ^ 2) * (4 * Fintype.card (T.X (j + 1)) ^ 2) := by
          refine Nat.add_le_add_right ?_ _
          rw [← T.card_X j (by omega)]
          exact h2
      _ = b * Fintype.card (T.X (j + 1)) * ∑ e, lds lhat n o ⟨j, by omega⟩ e ^ 2 +
          8 * FL.C₁ * (2 * FL.a₁ ^ 2) * (5 * Fintype.card (T.X (j + 1)) ^ 2) := by ring
      _ ≤ b * Fintype.card (T.X (j + 1)) * ∑ e, lds lhat n o ⟨j, by omega⟩ e ^ 2 +
          8 * FL.C₁ * (2 * FL.a₁ ^ 2) * (b ^ 2 * Fintype.card (T.X (j + 1)) ^ 2) := by gcongr
      _ = _ := by ring

include hH in
/-- The squares of the loads of a stage. -/
theorem sum_sq_le (j : Fin (J + 1)) : ∑ e, lds lhat n o j e ^ 2 ≤ kbar FL Uu AA lhat ^ 2 := by
  rcases isEmpty_or_nonempty (T.Ed j) with he | ⟨⟨e⟩⟩
  · rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact Nat.zero_le _
  · have hX : 0 < Fintype.card (T.X j) := Fintype.card_pos_iff.2 ⟨T.e0 e⟩
    refine le_trans ?_ (kap_le (R := R) (ch := ch) (lhat := lhat) (n := n) (o := o) hH j.1 j.2)
    exact (Nat.le_mul_of_pos_left _ hX).trans
      ((Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_left _ (pow_pos four_pos _)))

include hH in
/-- **Units between a node and its parent**, with the gain `g` of the tower: `g ^ q` is at most the number of
chambers, where the degree `b` is at most `2 ^ q`. -/
theorem bet_mul_le {q g : ℕ} (hq : 2 ≤ q) (hb : b ≤ 2 ^ q) (hg : g ^ q ≤ Fintype.card (T.X 0))
    (j : Fin (J + 1)) (c : T.X j) : T.bet (lds lhat n o j) c * g ≤ h * kbar FL Uu AA lhat := by
  have hX : 0 < Fintype.card (T.X j) := Fintype.card_pos_iff.2 ⟨c⟩
  have h1 := kap_le (R := R) (ch := ch) (lhat := lhat) (n := n) (o := o) hH j.1 j.2
  -- the gain: `g² ≤ 4 ^ j |X^(j)|`
  have h3 : (g ^ 2) ^ q ≤ (4 ^ j.1 * Fintype.card (T.X j)) ^ q := by
    calc (g ^ 2) ^ q = (g ^ q) ^ 2 := pow_right_comm _ _ _
      _ ≤ (b ^ j.1 * Fintype.card (T.X j)) ^ 2 :=
          Nat.pow_le_pow_left (hg.trans (Tower.card_X_pow j.1 (Nat.le_of_lt_succ j.2)).le) 2
      _ = (b ^ 2) ^ j.1 * Fintype.card (T.X j) ^ 2 := by ring
      _ ≤ (4 ^ q) ^ j.1 * Fintype.card (T.X j) ^ q :=
          Nat.mul_le_mul (Nat.pow_le_pow_left
            ((Nat.pow_le_pow_left hb 2).trans (pow_right_comm 2 q 2).le) _) (Nat.pow_le_pow_right hX hq)
      _ = _ := by ring
  have h4 := (Nat.pow_le_pow_iff_left (by omega)).1 h3
  refine (Nat.pow_le_pow_iff_left two_ne_zero).1 ?_
  calc (T.bet (lds lhat n o j) c * g) ^ 2 = T.bet (lds lhat n o j) c ^ 2 * g ^ 2 := mul_pow _ _ _
    _ ≤ h * (∑ e, lds lhat n o j e ^ 2) * (4 ^ j.1 * Fintype.card (T.X j)) :=
        Nat.mul_le_mul (T.bet_sq_le _ c) h4
    _ = h * (4 ^ j.1 * (Fintype.card (T.X j) * ∑ e, lds lhat n o j e ^ 2)) := by ring
    _ ≤ h ^ 2 * kbar FL Uu AA lhat ^ 2 :=
        Nat.mul_le_mul (Nat.le_self_pow two_ne_zero h)
          ((Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans h1)
    _ = _ := (mul_pow _ _ _).symm

include hH in
/-- **Units of a stage.** -/
theorem sum_bet_le_kbar (j : Fin (J + 1)) :
    2 ^ j.1 * ∑ c, T.bet (lds lhat n o j) c ≤ 2 * (h * kbar FL Uu AA lhat) := by
  have h1 := kap_le (R := R) (ch := ch) (lhat := lhat) (n := n) (o := o) hH j.1 j.2
  refine (Nat.pow_le_pow_iff_left two_ne_zero).1 ?_
  calc (2 ^ j.1 * ∑ c, T.bet (lds lhat n o j) c) ^ 2 = 4 ^ j.1 * (∑ c, T.bet (lds lhat n o j) c) ^ 2 := by
        rw [mul_pow, pow_right_comm]
        rfl
    _ ≤ 4 ^ j.1 * (2 * (h * (Fintype.card (T.X j) * ∑ e, lds lhat n o j e ^ 2))) :=
        Nat.mul_le_mul_left _ (T.sum_bet_sq_le _)
    _ = 2 * h * (4 ^ j.1 * (Fintype.card (T.X j) * ∑ e, lds lhat n o j e ^ 2)) := by ring
    _ ≤ (2 * h) ^ 2 * kbar FL Uu AA lhat ^ 2 :=
        Nat.mul_le_mul (Nat.le_self_pow two_ne_zero _)
          ((Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans h1)
    _ = _ := by ring

end

end Nc.Tow
