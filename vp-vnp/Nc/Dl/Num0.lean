/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Does

/-!
# Inequalities between the numbers of one cut
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

/-- The numbers of one cut. `m` bounds all polylogarithmic factors and constants, `X` everything that depends on `K`
only (and on `U0`). -/
structure CutNums (v K τ s k T ℓ ub lh X Lc m c ιb bd ev mm : ℕ) : Prop where
  v_pos : 1 ≤ v
  m_ge : 10000 ≤ m
  m_le : m ≤ v
  k_pos : 2 ≤ k
  kK : k ≤ K
  KT : K * T ≤ τ * m
  ℓeq : ℓ = s / K + 1
  ub_pos : 1 ≤ ub
  ub_le : ub ≤ T + 1
  lhub : lh * ub ≤ m * T
  Lc_le : Lc + 1 ≤ m
  c_le : 4 * c + 8 ≤ m
  K_X : K ≤ X
  X_ge : 1 ≤ X
  ιb_le : ιb * k ≤ m * K
  ιbX : ιb ≤ X
  bd_le : bd * ub * v ^ 300 ≤ τ * m ^ 2
  ev_le : ev * ub * k ≤ τ * m ^ 2
  mm_le : mm ≤ k * m
  mmX : mm ≤ X
  small : X ^ 6 * m ^ 20 * v ^ 300 ≤ τ

namespace CutNums

variable {v K τ s k T ℓ ub lh X Lc m c ιb bd ev mm : ℕ} (h : CutNums v K τ s k T ℓ ub lh X Lc m c ιb bd ev mm)

include h

theorem m_pos : 1 ≤ m := le_trans (by norm_num) h.m_ge

theorem Xpow {a b : ℕ} (hab : a ≤ b) : X ^ a ≤ X ^ b := Nat.pow_le_pow_right h.X_ge hab

theorem mpow {a b : ℕ} (hab : a ≤ b) : m ^ a ≤ m ^ b := Nat.pow_le_pow_right h.m_pos hab

/-- A constant up to 10000 is at most one more factor m. -/
theorem mc (t a b c : ℕ) (hc : c ≤ 10000) (hab : a < b) : t * m ^ a * c ≤ t * m ^ b := by
  grw [hc, h.m_ge, ← h.mpow hab, pow_succ, mul_assoc]

/-- Small things are small. -/
theorem X6 : X ^ 6 * m ^ 20 * v ^ 256 ≤ τ :=
  (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right h.v_pos (by norm_num))).trans h.small

theorem X6t : X ^ 6 * m ^ 20 ≤ τ := (Nat.le_mul_of_pos_right _ (Nat.pow_pos h.v_pos)).trans h.X6

theorem Xm_le {a b : ℕ} (ha : a ≤ 6) (hb : b ≤ 20) : X ^ a * m ^ b ≤ X ^ 6 * m ^ 20 :=
  Nat.mul_le_mul (h.Xpow ha) (h.mpow hb)

/-- The boundary of a group, in bits. -/
theorem bdub : bd * ub * v ^ 256 ≤ τ := by
  refine Nat.le_of_mul_le_mul_right (c := m ^ 2) ?_ (Nat.pow_pos h.m_pos)
  calc bd * ub * v ^ 256 * m ^ 2 ≤ bd * ub * v ^ 256 * v ^ 44 :=
        Nat.mul_le_mul_left _
          ((Nat.pow_le_pow_left h.m_le 2).trans (Nat.pow_le_pow_right h.v_pos (by norm_num)))
    _ = bd * ub * v ^ 300 := by rw [Nat.mul_assoc, ← pow_add]
    _ ≤ τ * m ^ 2 := h.bd_le

/-- **Time of the pieces.** -/
theorem time {κ : ℕ} (hκ : κ ≤ m) : κ * (2 * (Lc + 1) * (T + ub + 2) + ιb * T + 1000 * (ev + ιb * lh) * (ub + Lc + 1) +
    X ^ 4 * 1000 * (Lc + 1)) * k ≤ τ * m ^ 10 := by
  have hm := h.m_pos
  have hm4 := h.m_ge
  have hXk : ∀ a b, a ≤ 5 → b ≤ 20 → X ^ a * m ^ b * k ≤ τ := by
    intro a b ha hb
    grw [h.kK, h.K_X, ← h.X6t, ← h.Xm_le (show a + 1 ≤ 6 by omega) hb, pow_succ]
    ring_nf; rfl
  have hTk : T * k ≤ τ * m := by grw [h.kK, mul_comm T, h.KT]
  have hmk : m * k ≤ τ := by simpa using hXk 0 1 (by norm_num) (by norm_num)
  have A1 : 2 * (Lc + 1) * (T + ub + 2) * k ≤ τ * m ^ 7 := by
    grw [h.Lc_le, h.ub_le, ← h.mc τ 2 7 10 (by norm_num) (by norm_num)]
    linarith [Nat.mul_le_mul_left m hTk, Nat.le_mul_of_pos_right τ (Nat.pow_pos hm (n := 2))]
  have A2 : ιb * T * k ≤ τ * m ^ 7 := by
    grw [mul_right_comm, h.ιb_le, mul_assoc, h.KT, ← h.mpow (show 2 ≤ 7 by norm_num)]
    ring_nf; rfl
  have A3 : 1000 * (ev + ιb * lh) * (ub + Lc + 1) * k ≤ τ * m ^ 7 := by
    have hu : ub + Lc + 1 ≤ ub * (m * 2) := by nlinarith [h.ub_pos, h.Lc_le]
    have e1 : ev * ub * k * m ≤ τ * m ^ 4 := by
      grw [h.ev_le, ← h.mpow (show 3 ≤ 4 by norm_num)]; ring_nf; rfl
    have e2 : ιb * k * (lh * ub) * m ≤ τ * m ^ 4 := by
      grw [h.ιb_le, h.lhub, show m * K * (m * T) * m = m ^ 3 * (K * T) by ring, h.KT]; ring_nf; rfl
    grw [hu]
    linarith [h.mc τ 4 7 4000 (by norm_num) (by norm_num)]
  have A4 : X ^ 4 * 1000 * (Lc + 1) * k ≤ τ := by
    grw [h.Lc_le, (by omega : 1000 ≤ m), ← hXk 4 2 (by norm_num) (by norm_num)]; ring_nf; rfl
  grw [mul_assoc, add_mul, add_mul, add_mul, A1, A2, A3, A4, hκ]
  linarith [h.mc τ 8 10 4 (by norm_num) (by norm_num),
    Nat.le_mul_of_pos_right (τ * m) (Nat.pow_pos hm (n := 7))]

/-- **Size of the pieces.** -/
theorem size : (14800 * (X * Lc) ^ 4 + ιb * ℓ * (4 * c + 2) + bd * (4 * ub)) * k * v ^ 256 ≤
    (s * v ^ 256 + τ * k) * m ^ 10 := by
  have hk := h.k_pos
  have hL := h.Lc_le
  have B1 : ιb * ℓ * k ≤ m * s + m * K := by
    grw [h.ℓeq, mul_right_comm, h.ιb_le, mul_add, mul_assoc, Nat.mul_div_le, mul_one]
  have S1 : 14800 * (X * Lc) ^ 4 * k + m * K * m ≤ X ^ 6 * m ^ 20 := by
    grw [h.kK, h.K_X, ← h.Xm_le (show 5 ≤ 6 by norm_num) (show 6 ≤ 20 by norm_num),
      ← h.mc (X ^ 5) 5 6 10000 (by norm_num) (by norm_num),
      ← h.mc (X ^ 5) 4 5 2 (by norm_num) (by norm_num), show Lc ≤ m by omega]
    linarith [Nat.mul_le_mul (h.Xpow (show 1 ≤ 5 by norm_num)) (h.mpow (show 2 ≤ 4 by norm_num)),
      Nat.zero_le (X ^ 5 * m ^ 4)]
  have S2 : ιb * ℓ * (4 * c + 2) * k ≤ (m * s + m * K) * m := by
    grw [mul_right_comm, B1, show 4 * c + 2 ≤ m by have := h.c_le; omega]
  have S3 : bd * (4 * ub) * k * v ^ 256 ≤ 4 * (τ * k) := by
    grw [← h.bdub]; ring_nf; rfl
  linarith [h.X6, S3, Nat.mul_le_mul_right (v ^ 256) S1, Nat.mul_le_mul_right (v ^ 256) S2,
    h.mc (τ * k) 0 10 5 (by norm_num) (by norm_num), Nat.le_mul_of_pos_right τ (by omega : 0 < k),
    Nat.mul_le_mul_left (s * v ^ 256) (h.mpow (show 2 ≤ 10 by norm_num))]

/-- **Time of the dealing program.** -/
theorem deal : dealB Lc X K mm ub (mm * bd) (11 * X ^ 2) s * v ^ 256 ≤
    (s * v ^ 256 + τ * k) * m ^ 10 := by
  have hm := h.m_pos
  have hk := h.k_pos
  have hL := h.Lc_le
  have hm1 := h.m_ge
  -- the units of the boundaries
  have D1 : mm * bd * ((ub + 1) * (60 * Lc + 100)) * v ^ 256 ≤ τ * k * m ^ 3 := by
    grw [show ub + 1 ≤ 2 * ub by have := h.ub_pos; omega, show 60 * Lc + 100 ≤ 100 * m by omega,
      h.mm_le]
    linarith [Nat.mul_le_mul_left (k * m ^ 2) h.bdub,
      h.mc (τ * k) 2 3 200 (by norm_num) (by norm_num)]
  -- small things: with K, mm ≤ X and Lc ≤ m a polynomial in X and m; each of its monomials is at
  -- most X ^ 5 * m ^ 3, and its coefficients sum to less than 10000 ^ 2
  have D2 : (K * (60 * Lc + 100) + K * (60 * Lc + 130) +
      11 * X ^ 2 * (stepB Lc X + 30) + X * (90 * Lc + 230) + mm * (tmB' Lc X + 60) +
      300) * v ^ 256 ≤ τ * k := by
    grw [← Nat.le_mul_of_pos_right τ (by omega : 0 < k), ← h.X6,
      ← h.Xm_le (show 5 ≤ 6 by norm_num) (show 5 ≤ 20 by norm_num), h.K_X, h.mmX]
    gcongr ?_ * _
    have f : ∀ i j, i ≤ 5 → j ≤ 3 → X ^ i * m ^ j ≤ X ^ 5 * m ^ 3 := fun i j hi hj =>
      Nat.mul_le_mul (h.Xpow hi) (h.mpow hj)
    unfold stepB tmB'
    grw [show Lc ≤ m by omega]
    linarith [f 0 0 (by norm_num) (by norm_num), f 1 0 (by norm_num) (by norm_num),
      f 1 1 (by norm_num) (by norm_num), f 2 0 (by norm_num) (by norm_num),
      f 4 2 (by norm_num) (by norm_num), f 4 3 (by norm_num) le_rfl,
      h.mc (X ^ 5) 3 4 10000 (by norm_num) (by norm_num),
      h.mc (X ^ 5) 4 5 10000 (by norm_num) (by norm_num)]
  unfold dealB
  linarith [Nat.mul_le_mul_left (s * v ^ 256) (show 60 * Lc + 160 ≤ m ^ 10 by
      nlinarith [h.mpow (show 2 ≤ 10 by norm_num)]),
    h.mc (τ * k) 3 10 2 (by norm_num) (by norm_num),
    Nat.le_mul_of_pos_right (τ * k) (Nat.pow_pos hm (n := 3))]

end CutNums

end Nc.Dl
