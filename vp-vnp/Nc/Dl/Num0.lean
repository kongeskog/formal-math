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
  have hmg := h.m_ge
  have hL := h.Lc_le
  have hXk a b (ha : a ≤ 5) (hb : b ≤ 20) : X ^ a * m ^ b * k ≤ τ := by
    grw [h.kK, h.K_X, ← h.X6t, ← h.Xm_le (show a + 1 ≤ 6 by omega) hb]
    ring_nf; rfl
  have hTk : T * k ≤ τ * m := by grw [h.kK, mul_comm, h.KT]
  have e1 : k ≤ τ * m := by grw [← hm]; simpa using hXk 0 0 (by norm_num) (by norm_num)
  -- a constant at most `m` before a power of `m`
  have mc a b c (hc : c ≤ m) (hab : a < b) : τ * m ^ a * c ≤ τ * m ^ b := by
    grw [hc, mul_assoc, ← pow_succ, h.mpow hab]
  have A1 : 2 * (Lc + 1) * (T + ub + 2) * k ≤ τ * m ^ 7 := by
    calc _ ≤ 2 * m * (T + (T + 1) + 2) * k := by grw [hL, h.ub_le]
      _ = 2 * m * (2 * (T * k) + 3 * k) := by ring
      _ ≤ 2 * m * (2 * (τ * m) + 3 * (τ * m)) := by grw [hTk, e1]
      _ = τ * m ^ 2 * 10 := by ring
      _ ≤ _ := mc 2 7 _ (by omega) (by omega)
  have A2 : ιb * T * k ≤ τ * m ^ 7 := by
    grw [mul_right_comm, h.ιb_le, mul_assoc, h.KT, ← h.mpow (show 2 ≤ 7 by norm_num)]
    ring_nf; rfl
  have hu : ub + Lc + 1 ≤ ub * (m * m) := by
    linarith [Nat.le_mul_of_pos_right ub hm, Nat.le_mul_of_pos_left m h.ub_pos,
      Nat.mul_le_mul_left (ub * m) hmg]
  have hev : ev * ub * k * (m * m) ≤ τ * m ^ 6 := by
    grw [h.ev_le, ← h.mpow (show 4 ≤ 6 by norm_num)]
    ring_nf; rfl
  have hιb : ιb * k * (lh * ub) * (m * m) ≤ τ * m ^ 6 := by
    calc _ ≤ m ^ 4 * (K * T) := by grw [h.ιb_le, h.lhub]; ring_nf; rfl
      _ ≤ _ := by grw [h.KT, ← h.mpow (show 5 ≤ 6 by norm_num)]; ring_nf; rfl
  have A3 : 1000 * (ev + ιb * lh) * (ub + Lc + 1) * k ≤ τ * m ^ 7 := by
    calc _ ≤ 1000 * (ev * ub * k * (m * m) + ιb * k * (lh * ub) * (m * m)) := by
          grw [hu]; ring_nf; rfl
      _ ≤ τ * m ^ 6 * 2000 := by grw [hev, hιb]; ring_nf; rfl
      _ ≤ _ := mc 6 7 _ (by omega) (by omega)
  have A4 : X ^ 4 * 1000 * (Lc + 1) * k ≤ τ * m ^ 7 := by
    grw [hL, show 1000 ≤ m by omega, ← mc 0 7 1 hm (by omega),
      ← hXk 4 2 (by norm_num) (by norm_num)]
    ring_nf; rfl
  calc _ = κ * (2 * (Lc + 1) * (T + ub + 2) * k + ιb * T * k +
        1000 * (ev + ιb * lh) * (ub + Lc + 1) * k +
        X ^ 4 * 1000 * (Lc + 1) * k) := by ring
    _ ≤ m * (τ * m ^ 7 + τ * m ^ 7 + τ * m ^ 7 + τ * m ^ 7) := by
      grw [hκ, A1, A2, A3, A4]
    _ = τ * m ^ 8 * 4 := by ring
    _ ≤ _ := mc 8 10 _ (by omega) (by omega)

/-- **Size of the pieces.** -/
theorem size : (X + 1 + (200 * X ^ 3 * Lc + ιb * ℓ * (4 * c + 2) + bd * (4 * ub))) * k * v ^ 256 ≤
    (s * v ^ 256 + τ * k) * m ^ 10 := by
  have hm := h.m_pos
  have hmg := h.m_ge
  have hk := h.k_pos
  have hX : 1 ≤ X := h.X_ge
  have hL := h.Lc_le
  have B1 : ιb * k * ℓ ≤ m * s + m * K := by
    calc _ ≤ m * (K * (s / K)) + m * K := by grw [h.ℓeq, h.ιb_le]; ring_nf; rfl
      _ ≤ _ := by grw [Nat.mul_div_le]
  have S1 : (X + 1 + 200 * X ^ 3 * Lc) * k + m * K * m ≤ X ^ 6 * m ^ 20 := by
    have e1 : X ≤ X ^ 3 * m ^ 2 := by
      grw [← hm, ← Nat.le_self_pow (show 3 ≠ 0 by norm_num) X]; simp
    have e2 : 1 ≤ X ^ 3 * m ^ 2 := hX.trans e1
    have e3 : 200 * X ^ 3 * Lc ≤ X ^ 3 * m ^ 2 := by
      grw [show 200 ≤ m by omega, show Lc ≤ m by omega]; ring_nf; rfl
    have e5 : m * X * m ≤ X ^ 3 * m ^ 2 * X := by
      grw [← Nat.one_le_pow 3 X hX]; ring_nf; rfl
    calc _ ≤ X ^ 3 * m ^ 2 * X * 4 := by
          grw [h.kK, h.K_X, e5, show X + 1 + 200 * X ^ 3 * Lc ≤ 3 * (X ^ 3 * m ^ 2) by omega]
          ring_nf; rfl
      _ ≤ X ^ 3 * m ^ 2 * X * m := by gcongr; omega
      _ = X ^ 4 * m ^ 3 := by ring
      _ ≤ _ := h.Xm_le (by norm_num) (by norm_num)
  have S2 : ιb * ℓ * (4 * c + 2) * k ≤ (m * s + m * K) * m := by
    grw [← B1, ← show 4 * c + 2 ≤ m by have := h.c_le; omega]; ring_nf; rfl
  have S3 : bd * (4 * ub) * k * v ^ 256 ≤ 4 * (τ * k) := by
    grw [← h.bdub]; ring_nf; rfl
  have hm10 : m ^ 2 * (s * v ^ 256) ≤ m ^ 10 * (s * v ^ 256) := by
    grw [h.mpow (show 2 ≤ 10 by norm_num)]
  have h5 : 5 * (τ * k) ≤ m ^ 10 * (τ * k) := by
    grw [← Nat.le_self_pow (show 10 ≠ 0 by norm_num) m, show 5 ≤ m by omega]
  have hτk : τ ≤ τ * k := Nat.le_mul_of_pos_right _ (by omega)
  calc _ = ((X + 1 + 200 * X ^ 3 * Lc) * k + ιb * ℓ * (4 * c + 2) * k) * v ^ 256 +
          bd * (4 * ub) * k * v ^ 256 := by
          ring
    _ ≤ (m ^ 2 * s + X ^ 6 * m ^ 20) * v ^ 256 + 4 * (τ * k) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (by linarith)) S3
    _ ≤ _ := by linarith [h.X6]

/-- **Time of the dealing program.** -/
theorem deal : dealB Lc X K mm ub (mm * bd) (4 * (X * X) + 10 * X) s * v ^ 256 ≤
    (s * v ^ 256 + τ * k) * m ^ 10 := by
  have hm := h.m_pos
  have hk := h.k_pos
  have hX : 1 ≤ X := h.X_ge
  have hL := h.Lc_le
  have hm1 := h.m_ge
  -- the units of the boundaries
  have D1 : mm * bd * ((ub + 1) * (60 * Lc + 100)) * v ^ 256 ≤ τ * k * m ^ 3 := by
    calc _ ≤ mm * (bd * ub * v ^ 256) * (200 * m) := by
          grw [show ub + 1 ≤ ub + ub by have := h.ub_pos; omega,
            show 60 * Lc + 100 ≤ 100 * m by omega]
          ring_nf; rfl
      _ ≤ _ := by grw [h.mm_le, h.bdub, show 200 ≤ m by omega]; ring_nf; rfl
  -- small things
  have D2 : (K * (60 * Lc + 100) + K * (60 * Lc + 130) + (4 * (X * X) + 10 * X) * (stepB Lc X + 30) + X * (90 * Lc + 230) +
      mm * (tmB' Lc X + 60) + 300) * v ^ 256 ≤ τ * k := by
    grw [← show 1 ≤ k by omega, ← h.X6,
      ← h.Xm_le (show 4 ≤ 6 by norm_num) (show 4 ≤ 20 by norm_num), mul_one]
    gcongr
    have hK := h.K_X
    have x1 : X ≤ X ^ 4 := Nat.le_self_pow (by norm_num) X
    have x3 : X ^ 3 ≤ X ^ 4 := h.Xpow (by norm_num)
    have f1 : K * (60 * Lc + 100) ≤ X ^ 4 * (100 * m) := Nat.mul_le_mul (hK.trans x1) (by omega)
    have f2 : K * (60 * Lc + 130) ≤ X ^ 4 * (130 * m) := Nat.mul_le_mul (hK.trans x1) (by omega)
    have st : stepB Lc X + 30 ≤ X * (1000 * m) := by
      have e1 : 240 * Lc + 230 ≤ X * (470 * m) := by grw [← hX]; omega
      have e2 : 20 * X ≤ X * (20 * m) := by nlinarith
      have e3 : X * (4 * (60 * Lc + 80)) ≤ X * (320 * m) := Nat.mul_le_mul_left _ (by omega)
      have e6 : X * (1000 * m) = X * (470 * m) + X * (20 * m) + X * (320 * m) + X * (190 * m) := by
        ring
      unfold stepB
      omega
    have f3 : (4 * (X * X) + 10 * X) * (stepB Lc X + 30) ≤ X ^ 4 * (14000 * m) := by
      grw [st, ← x3, show 10 * X ≤ 10 * (X * X) by nlinarith]; ring_nf; rfl
    have f4 : X * (90 * Lc + 230) ≤ X ^ 4 * (230 * m) := Nat.mul_le_mul x1 (by omega)
    have tb : tmB' Lc X + 60 ≤ X ^ 3 * (20000 * m) := by
      have y1 : X ^ 2 ≤ X ^ 3 := h.Xpow (by norm_num)
      have y2 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
      have g1 : X * (3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000) ≤ X ^ 3 * (3000 * m) := by
        calc _ ≤ X * (3 * (X * (150 * m)) + X * (360 * m) + X * (62 * m) + X * (2000 * m)) := by
              refine Nat.mul_le_mul_left _ ?_
              have e1 : 3 * (X * (30 * Lc + 150)) ≤ 3 * (X * (150 * m)) := by gcongr; omega
              have e2 : 360 * Lc ≤ X * (360 * m) := by grw [← hX]; omega
              have e3 : 62 * X ≤ X * (62 * m) := by nlinarith
              have e4 : 2000 ≤ X * (2000 * m) := by grw [← hX]; omega
              omega
          _ = X ^ 2 * (2872 * m) := by ring
          _ ≤ _ := Nat.mul_le_mul y1 (by omega)
      have g2 : X * (X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500) ≤ X ^ 3 * (4000 * m) := by
        calc _ ≤ X * (X * (X * (700 * m) + X * (120 * m)) + X * (X * (150 * m)) +
            X * (X * (300 * m)) +
            X * (X * (1500 * m))) := by
              refine Nat.mul_le_mul_left _ ?_
              have e1 : X * (X * (270 * Lc + 700) + 120) ≤ X * (X * (700 * m) + X * (120 * m)) := by
                gcongr
                · omega
                · grw [← hX]; omega
              have e2 : X * (30 * Lc + 150) ≤ X * (X * (150 * m)) := by gcongr; grw [← hX]; omega
              have e3 : 300 * Lc ≤ X * (X * (300 * m)) := by grw [← hX]; omega
              have e4 : 1500 ≤ X * (X * (1500 * m)) := by grw [← hX]; omega
              linarith
          _ = X ^ 3 * (2770 * m) := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
      have g3 : X * (2000 * Lc + 5000) ≤ X ^ 3 * (5000 * m) := Nat.mul_le_mul y2 (by omega)
      have g4 : 1060 ≤ X ^ 3 * (1060 * m) := by grw [← hX]; omega
      unfold tmB'
      linarith
    have f5 : mm * (tmB' Lc X + 60) ≤ X ^ 4 * (20000 * m) := by
      grw [h.mmX, tb]; ring_nf; rfl
    have f6 : 300 ≤ X ^ 4 * (300 * m) := by grw [← hX]; omega
    have f8 : X ^ 4 * (34760 * m) ≤ X ^ 4 * m ^ 4 := by
      grw [show 34760 ≤ m ^ 3 by nlinarith [Nat.mul_le_mul hm1 hm1]]; ring_nf; rfl
    linarith
  have D3 : 60 * s + s * (60 * Lc + 100) ≤ s * m ^ 10 := by
    calc _ = s * (60 * Lc + 160) := by ring
      _ ≤ s * m ^ 2 := by gcongr; nlinarith
      _ ≤ _ := by grw [h.mpow (show 2 ≤ 10 by norm_num)]
  have e11 : τ * k * m ^ 3 + τ * k ≤ τ * k * m ^ 10 := by
    calc _ ≤ τ * k * m ^ 3 * m := by
          linarith [Nat.le_mul_of_pos_right (τ * k) (Nat.pow_pos hm (n := 3)),
            Nat.mul_le_mul_left (τ * k * m ^ 3) (show 2 ≤ m by omega)]
      _ ≤ _ := by grw [mul_assoc, ← pow_succ, h.mpow (show 3 + 1 ≤ 10 by norm_num)]
  generalize hW : K * (60 * Lc + 100) + K * (60 * Lc + 130) +
    (4 * (X * X) + 10 * X) * (stepB Lc X + 30) + X * (90 * Lc + 230) + mm * (tmB' Lc X + 60) + 300 = W at D2
  calc _ ≤ (s * m ^ 10 + (W + mm * bd * ((ub + 1) * (60 * Lc + 100)))) * v ^ 256 :=
        Nat.mul_le_mul_right _ (by unfold dealB; linarith)
    _ = s * v ^ 256 * m ^ 10 + W * v ^ 256 + mm * bd * ((ub + 1) * (60 * Lc + 100)) * v ^ 256 := by
        ring
    _ ≤ _ := by linarith

end CutNums

end Nc.Dl
