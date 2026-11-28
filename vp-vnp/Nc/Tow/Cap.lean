/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Load4

/-!
# The number of units of a move; all units between nodes and their parents
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b J m Uu AA : ℕ} {T : Tower h b J} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R ch FL → ℕ}

/-- The bound for the number of units of a move. -/
def capN (FL : FlagLaws F T) (U0 Uu AA lhat : ℕ) : ℕ := U0 + 2 + 2 * b * kbar FL Uu AA lhat

section

variable (hH : THypR FL)

include hH

/-- **The numbers of units of the moves are bounded.** -/
theorem num_le_cap {U0 : ℕ} (hn : ∀ a c, n a c ≤ U0) (mv : Mv R ch FL) :
    num lhat n o mv ≤ capN FL U0 Uu AA lhat := by
  have hS := sum_sq_le (R := R) (ch := ch) (lhat := lhat) (n := n) (o := o) hH
  have hedge : ∀ (j : Fin (J + 1)) (e : T.Ed j),
      load lhat n o (.edge j e) ≤ capN FL U0 Uu AA lhat := by
    intro j e
    have h1 : load lhat n o (.edge j e) ≤ kbar FL Uu AA lhat :=
      (Nat.pow_le_pow_iff_left two_ne_zero).1 ((Finset.single_le_sum
        (f := fun e => lds lhat n o j e ^ 2) (fun _ _ => Nat.zero_le _) (mem_univ e)).trans (hS j))
    have h2 : kbar FL Uu AA lhat ≤ 2 * b * kbar FL Uu AA lhat :=
      Nat.le_mul_of_pos_left _ (Nat.mul_pos two_pos T.b_pos)
    unfold capN
    omega
  rcases mv with ⟨x, hx⟩ | l
  · rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
    · have h1 := num_start_le (FL := FL) (lhat := lhat) (n := n) (o := o) a c γ s hx
      have h2 := Bt_le (ch := ch) (lhat := lhat) (n := n) a c γ
      have h3 : n a c / Fintype.card (T.X 0) ≤ U0 := (Nat.div_le_self _ _).trans (hn a c)
      unfold capN
      omega
    · exact (num_inl _).trans (hedge j.castSucc e)
    · obtain ⟨hx0, h1⟩ := num_mid_le FL lhat n o j e s hx
      exact h1.trans ((num_mid0 j e hx0).1.trans (hedge j.castSucc e))
    · exact (num_inl _).trans (hedge (Fin.last J) e)
  · obtain ⟨j, i, ω, d⟩ := l
    -- the end segments at one vertex are at most four times the loads of the stage,
    -- so `2 b kbar` units fit
    have h1 : ∑ q, load lhat n o (.seg j i ω q) ^ 2 ≤ 2 * (2 * kbar FL Uu AA lhat ^ 2) := by
      calc _ ≤ ∑ q, T.nEnd i (lds lhat n o j.castSucc) ω q ^ 2 :=
            Finset.sum_le_sum fun q _ => Nat.pow_le_pow_left (seg_le j i ω q) 2
        _ ≤ ∑ ω, ∑ q, T.nEnd i (lds lhat n o j.castSucc) ω q ^ 2 :=
            Finset.single_le_sum (f := fun ω => ∑ q, T.nEnd i (lds lhat n o j.castSucc) ω q ^ 2)
              (fun _ _ => Nat.zero_le _) (mem_univ ω)
        _ ≤ _ := (Tower.sum_end_sq j.2).trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2
            ((Finset.sum_le_sum_of_subset (subset_univ _)).trans (hS j.castSucc))))
    have h2 := FL.L1 (fun q => load lhat n o (.seg j i ω q)) (2 * b * kbar FL Uu AA lhat) (by
      calc _ ≤ b ^ 2 * (2 * (2 * kbar FL Uu AA lhat ^ 2)) := Nat.mul_le_mul_left _ h1
        _ = (2 * b * kbar FL Uu AA lhat) ^ 2 := by ring
        _ ≤ (FL.a₁ * (2 * b * kbar FL Uu AA lhat)) ^ 2 :=
            Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ FL.a₁_pos) 2
        _ ≤ _ := Nat.le_mul_of_pos_left _ two_pos)
    exact (num_inr_le _).trans ((Nat.sInf_le (s := {t | ∃ d', Fits (load lhat n o)
      (withD (⟨j, i, ω, d⟩ : LMv FL) d') t}) h2).trans (Nat.le_add_left _ _))

/-- All units between nodes and their parents. -/
theorem sum_bet_le :
    ∑ j : Fin (J + 1), ∑ c, T.bet (lds lhat n o j) c ≤ 4 * (h * kbar FL Uu AA lhat) := by
  calc _ ≤ ∑ j : Fin (J + 1), 2 * (h * kbar FL Uu AA lhat) / 2 ^ j.1 :=
        Finset.sum_le_sum fun j _ => (Nat.le_div_iff_mul_le (pow_pos two_pos _)).2
          ((Nat.mul_comm _ _).le.trans (sum_bet_le_kbar hH j))
    _ = ∑ j ∈ range (J + 1), 2 * (h * kbar FL Uu AA lhat) / 2 ^ j :=
        Fin.sum_univ_eq_sum_range (fun j => 2 * (h * kbar FL Uu AA lhat) / 2 ^ j) _
    _ ≤ 2 * (h * kbar FL Uu AA lhat) * 2 / (2 - 1) := Nat.geom_sum_le le_rfl _ _
    _ = _ := by omega

end

end Nc.Tow
