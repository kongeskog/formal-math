/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.G.PlayThm
import Nc.Tow.Slp4
import Nc.Tow.Slp5
import Nc.Tow.EndC
import Nc.Tow.CapOk
import Nc.Tow.Cards
import Nc.Tow.Ever7
import Nc.Tow.PlaceE
import NS1.Accel

/-!
# The conditions on a tower and its laws, and the numbers that follow
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000

namespace Nc.Tow

open Finset Nc.G
open NS1 (lg)

variable {F : Type} [CommRing F] {h b J m Uu : ℕ} {T : Tower h b J}

/-- The roles of the relay and of finitely many laws. -/
noncomputable def kindList (F : Type) [CommRing F] (laws : List (Law F)) : List (Σ L : Law F, L.Ro) :=
  (relay F :: laws).flatMap fun L => (univ : Finset L.Ro).toList.map fun p => ⟨L, p⟩

/-- The conditions on the tower and the laws, with one constant. -/
structure TCst (FL : FlagLaws F T) (laws : List (Law F)) (c q : ℕ) : Prop extends THypR FL where
  h_le : h ≤ c
  b_le : b ≤ c
  nr_le : Fintype.card T.Nr ≤ c
  g_le : FL.G₁ ≤ c
  di_le : Fintype.card FL.Di ≤ c
  fl_le : Fintype.card (Sym2 T.Fl) ≤ c
  sl_le : ∀ d, Fintype.card (FL.L d).Sl ≤ c
  bot : Fintype.card (T.X J) ≤ c
  bot_pos : 0 < Fintype.card (T.X J)
  cst : 2 * h + 4 * FL.C₁ * FL.a₁ ≤ c
  pq : 2 ≤ q
  pow : b ≤ 2 ^ q
  mem : ∀ d, FL.L d ∈ laws
  len : ∀ L ∈ laws, L.Le c ∧ L.lam ≤ c

/-- The bound for the norms, a natural number. -/
def kapB (c m X lh : ℕ) : ℕ := c * (m * X * (lh + 2 * X ^ 2))

/-- The bound for the numbers of units of moves. -/
def capB (c m X lh U0 : ℕ) : ℕ := U0 + 2 + 3 * c * kapB c m X lh

section

variable {FL : FlagLaws F T} {laws : List (Law F)} {c q U0 : ℕ} (hC : TCst FL laws c q)
include hC

theorem TCst.X_pos : 0 < Fintype.card (T.X 0) := by
  have h1 := Tower.card_X_le (T := T) J le_rfl
  have := hC.bot_pos
  omega

theorem TCst.c_pos : 1 ≤ c := T.h_pos.trans_le hC.h_le

/-- The norms at the start, for routes that use every edge at most `2 X₀ m` times. -/
theorem kbar_kapB {AA lh : ℕ} (hm : 1 ≤ m) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m)
    (hAA : AA ≤ Fintype.card (T.X 0)) : kbar FL Uu AA lh ≤ kapB c m (Fintype.card (T.X 0)) lh := by
  have hX := hC.X_pos
  unfold kbar kapB nhat
  generalize Fintype.card (T.X 0) = X at *
  have h1 : X * (lh / X) ≤ lh := Nat.mul_div_le lh X
  have h2 : 1 ≤ m * (lh + 2 * X ^ 2) := Nat.mul_pos hm (by positivity)
  calc X * (h * (Uu * (lh / X + 2 * AA)) + 4 * FL.C₁ * FL.a₁) ≤
      X * (h * (2 * X * m * (lh / X + 2 * X)) + 4 * FL.C₁ * FL.a₁ * (m * (lh + 2 * X ^ 2))) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (by gcongr) (Nat.le_mul_of_pos_right _ h2))
    _ = X * (h * (2 * m * (X * (lh / X) + 2 * X ^ 2)) + 4 * FL.C₁ * FL.a₁ * (m * (lh + 2 * X ^ 2))) := by ring
    _ ≤ X * (h * (2 * m * (lh + 2 * X ^ 2)) + 4 * FL.C₁ * FL.a₁ * (m * (lh + 2 * X ^ 2))) := by gcongr
    _ = (2 * h + 4 * FL.C₁ * FL.a₁) * (m * X * (lh + 2 * X ^ 2)) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hC.cst

theorem capN_capB {AA lh : ℕ} (hm : 1 ≤ m) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hAA : AA ≤ Fintype.card (T.X 0)) :
    capN FL U0 Uu AA lh ≤ capB c m (Fintype.card (T.X 0)) lh U0 := by
  unfold capN capB
  refine Nat.add_le_add_left ?_ _
  calc 2 * b * kbar FL Uu AA lh ≤ 3 * c * kapB c m (Fintype.card (T.X 0)) lh :=
    Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) hC.b_le) (kbar_kapB hC hm hUu hAA)

end

/-- Names of targets. -/
theorem card_Tg_le {V : ℕ} (hV : 1 ≤ V) (hh : h ≤ V) (hm : m ≤ V) (hJ : J ≤ V)
    {AA : ℕ} (hAA : AA ≤ V) (hX : Fintype.card (T.X 0) ≤ V) (hfl : Fintype.card (Sym2 T.Fl) ≤ V) :
    Fintype.card (Tg T m AA) ≤ 12 * V ^ 5 := by
  rw [← Fintype.card_congr (proxy_equiv% (Tg T m AA)), Fintype.card_sum, Fintype.card_sum, Fintype.card_sum, Fintype.card_unit,
    Fintype.card_sigma, Fintype.card_sigma]
  have h1 : ∑ j : Fin (J + 1), Fintype.card (T.Ed j) ≤ 2 * V ^ 3 := by
    calc _ ≤ ∑ _j : Fin (J + 1), V * V := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine (Tower.card_ed_le (Nat.le_of_lt_succ j.2)).trans ?_
          gcongr
      _ = (J + 1) * (V * V) := by simp
      _ ≤ (2 * V) * (V * V) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * V ^ 3 := by ring
  have h2 := (card_RM_le (T := T) (m := m) (AA := AA)).trans
    (rmN_le (X0 := Fintype.card (T.X 0)) hV hh hm hJ hAA hX)
  have h3 : ∑ j : Fin J, Fintype.card (Σ i : Fin h, Σ _ : T.V (j + 1) i, Sym2 T.Fl) ≤ V ^ 4 := by
    calc _ ≤ ∑ _j : Fin J, V * (V * V) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Fintype.card_sigma]
          calc _ ≤ ∑ _i : Fin h, V * V := by
                refine Finset.sum_le_sum fun i _ => ?_
                rw [Fintype.card_sigma, sum_const, card_univ, smul_eq_mul]
                exact Nat.mul_le_mul ((Tower.card_V_le j.2 i).trans hX) hfl
            _ = h * (V * V) := by simp
            _ ≤ V * (V * V) := Nat.mul_le_mul_right _ hh
      _ = J * (V * (V * V)) := by simp
      _ ≤ V * (V * (V * V)) := Nat.mul_le_mul_right _ hJ
      _ = V ^ 4 := by ring
  have h4 : V ^ 4 ≤ V ^ 5 := Nat.pow_le_pow_right hV (by norm_num)
  have h6 : V ^ 3 ≤ V ^ 4 := Nat.pow_le_pow_right hV (by norm_num)
  have h5 : 1 ≤ V ^ 5 := Nat.one_le_pow _ _ hV
  omega

section Numbers

/-- The depth of a tower is logarithmic. -/
theorem two_pow_le {h b J : ℕ} {T : Tower h b J} (hD : 2 ≤ b) (hX : 0 < Fintype.card (T.X J)) :
    2 ^ J ≤ Fintype.card (T.X 0) := by
  rw [Tower.card_X_pow J le_rfl]
  exact (Nat.pow_le_pow_left hD J).trans (Nat.le_mul_of_pos_right _ hX)

theorem depth_le {J X c K : ℕ} (hJ : 2 ^ J ≤ X) (hX : X ≤ c * (2 * K)) : J + 1 ≤ (2 * c + 1) * lg K := by
  have hl : 1 ≤ lg K := Nat.succ_le_succ (Nat.zero_le _)
  have h1 : K < 2 ^ lg K := Nat.lt_pow_succ_log_self (by norm_num) K
  have h2 : 2 * c < 2 ^ (2 * c) := Nat.lt_two_pow_self
  have h3 : 2 ^ J < 2 ^ (2 * c + lg K) := by
    calc 2 ^ J ≤ c * (2 * K) := hJ.trans hX
      _ = 2 * c * K := by ring
      _ < 2 ^ (2 * c) * 2 ^ lg K := Nat.mul_lt_mul'' h2 h1
      _ = _ := (pow_add _ _ _).symm
  have h4 : J < 2 * c + lg K := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h3
  have h5 : 2 * c ≤ 2 * c * lg K := Nat.le_mul_of_pos_right _ hl
  linarith

theorem m_le {c m J K : ℕ} (hm : m ≤ c * (J + 1) ^ 7) (hJ : J + 1 ≤ (2 * c + 1) * lg K) : m ≤ c * ((2 * c + 1) ^ 7 * lg K ^ 7) := by
  refine hm.trans (Nat.mul_le_mul_left _ ?_)
  rw [← mul_pow]
  exact Nat.pow_le_pow_left hJ 7

end Numbers

end Nc.Tow
