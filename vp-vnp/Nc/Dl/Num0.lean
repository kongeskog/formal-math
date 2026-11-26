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
  linarith [h.mc τ 8 10 4 (by norm_num) (by norm_num), Nat.le_mul_of_pos_right (τ * m) (Nat.pow_pos hm (n := 7))]

/-- **Size of the pieces.** -/
theorem size : (X + 1 + (200 * X ^ 3 * Lc + ιb * ℓ * (4 * c + 2) + bd * (4 * ub))) * k * v ^ 256 ≤
    (s * v ^ 256 + τ * k) * m ^ 10 := by
  have hm := h.m_pos
  have hk := h.k_pos
  have hX : 1 ≤ X := h.X_ge
  have hL := h.Lc_le
  have B1 : ιb * ℓ * k ≤ m * s + m * K := by
    grw [h.ℓeq, mul_right_comm, h.ιb_le, mul_add, mul_assoc, Nat.mul_div_le, mul_one]
  have S1 : (X + 1 + 200 * X ^ 3 * Lc) * k + m * K * m ≤ X ^ 6 * m ^ 20 := by
    have hXm : ∀ a b, a ≤ 4 → b ≤ 2 → X ^ a * m ^ b ≤ X ^ 4 * m ^ 2 := fun a b ha hb =>
      Nat.mul_le_mul (h.Xpow ha) (h.mpow hb)
    grw [h.kK, h.K_X, ← h.Xm_le (show 4 ≤ 6 by norm_num) (show 3 ≤ 20 by norm_num), ← h.mc (X ^ 4) 2 3 203
      (by norm_num) (by norm_num), show Lc ≤ m by omega]
    linarith [hXm 2 0 (by norm_num) (by norm_num), hXm 1 0 (by norm_num) (by norm_num),
      hXm 4 1 (by norm_num) (by norm_num), hXm 1 2 (by norm_num) (by norm_num)]
  have S2 : ιb * ℓ * (4 * c + 2) * k ≤ (m * s + m * K) * m := by
    grw [mul_right_comm, B1, show 4 * c + 2 ≤ m by have := h.c_le; omega]
  have S3 : bd * (4 * ub) * k * v ^ 256 ≤ 4 * (τ * k) := by
    grw [← h.bdub]; ring_nf; rfl
  linarith [h.X6, S3, Nat.mul_le_mul_right (v ^ 256) S1, Nat.mul_le_mul_right (v ^ 256) S2,
    h.mc (τ * k) 0 10 5 (by norm_num) (by norm_num), Nat.le_mul_of_pos_right τ (by omega : 0 < k),
    Nat.mul_le_mul_left (s * v ^ 256) (h.mpow (show 2 ≤ 10 by norm_num))]

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
    calc mm * bd * ((ub + 1) * (60 * Lc + 100)) * v ^ 256 ≤
          mm * bd * ((ub + ub) * (100 * m)) * v ^ 256 := by
          gcongr
          · exact h.ub_pos
          · omega
      _ = mm * (bd * ub * v ^ 256) * (200 * m) := by ring
      _ ≤ k * m * τ * (m * m) :=
          Nat.mul_le_mul (Nat.mul_le_mul h.mm_le h.bdub) (Nat.mul_le_mul_right _ (by omega))
      _ = τ * k * m ^ 3 := by ring
  -- small things
  have D2 : (K * (60 * Lc + 100) + K * (60 * Lc + 130) + (4 * (X * X) + 10 * X) * (stepB Lc X + 30) + X * (90 * Lc + 230) +
      mm * (tmB' Lc X + 60) + 300) * v ^ 256 ≤ τ * k := by
    have hsm : X ^ 4 * m ^ 4 * v ^ 256 ≤ τ * k :=
      (Nat.mul_le_mul_right _ (h.Xm_le (by norm_num) (by norm_num))).trans (h.X6.trans (Nat.le_mul_of_pos_right _ (by omega)))
    refine le_trans (Nat.mul_le_mul_right _ ?_) hsm
    have hK := h.K_X
    have x1 : X ≤ X ^ 4 := Nat.le_self_pow (by norm_num) X
    have x2 : X ^ 2 ≤ X ^ 4 := h.Xpow (by norm_num)
    have x3 : X ^ 3 ≤ X ^ 4 := h.Xpow (by norm_num)
    have L1 : 60 * Lc + 100 ≤ 100 * m := by omega
    have f1 : K * (60 * Lc + 100) ≤ X ^ 4 * (100 * m) := Nat.mul_le_mul (hK.trans x1) L1
    have f2 : K * (60 * Lc + 130) ≤ X ^ 4 * (130 * m) := Nat.mul_le_mul (hK.trans x1) (by omega)
    have st : stepB Lc X + 30 ≤ X * (1000 * m) := by
      have e1 : 60 * Lc ≤ X * (60 * m) := by
        calc 60 * Lc ≤ 1 * (60 * m) := by omega
          _ ≤ X * (60 * m) := Nat.mul_le_mul_right _ hX
      have e2 : 20 * X ≤ X * (20 * m) := by nlinarith
      have e3 : X * (4 * (60 * Lc + 80)) ≤ X * (320 * m) := Nat.mul_le_mul_left _ (by omega)
      have e4 : 180 * Lc ≤ X * (180 * m) := by
        calc 180 * Lc ≤ 1 * (180 * m) := by omega
          _ ≤ X * (180 * m) := Nat.mul_le_mul_right _ hX
      have e5 : 230 ≤ X * (230 * m) := by
        calc 230 ≤ 1 * (230 * m) := by omega
          _ ≤ X * (230 * m) := Nat.mul_le_mul_right _ hX
      have e6 : X * (1000 * m) = X * (60 * m) + X * (20 * m) + X * (320 * m) + X * (180 * m) + X * (230 * m) + X * (190 * m) := by
        ring
      unfold stepB
      omega
    have f3 : (4 * (X * X) + 10 * X) * (stepB Lc X + 30) ≤ X ^ 4 * (14000 * m) := by
      have e1 : 4 * (X * X) + 10 * X ≤ 14 * X ^ 2 := by nlinarith
      calc (4 * (X * X) + 10 * X) * (stepB Lc X + 30) ≤ 14 * X ^ 2 * (X * (1000 * m)) := Nat.mul_le_mul e1 st
        _ = X ^ 3 * (14000 * m) := by ring
        _ ≤ X ^ 4 * (14000 * m) := Nat.mul_le_mul_right _ x3
    have f4 : X * (90 * Lc + 230) ≤ X ^ 4 * (230 * m) := Nat.mul_le_mul x1 (by omega)
    have tb : tmB' Lc X + 60 ≤ X ^ 3 * (20000 * m) := by
      have y1 : X ^ 2 ≤ X ^ 3 := h.Xpow (by norm_num)
      have y2 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
      have y3 : 1 ≤ X ^ 3 := Nat.pow_pos hX
      have g1 : X * (3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000) ≤ X ^ 3 * (3000 * m) := by
        calc X * (3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000)
            ≤ X * (3 * (X * (150 * m)) + X * (360 * m) + X * (62 * m) + X * (2000 * m)) := by
              refine Nat.mul_le_mul_left _ ?_
              have e1 : 3 * (X * (30 * Lc + 150)) ≤ 3 * (X * (150 * m)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
              have e2 : 360 * Lc ≤ X * (360 * m) := by
                calc 360 * Lc ≤ 1 * (360 * m) := by omega
                  _ ≤ X * (360 * m) := Nat.mul_le_mul_right _ hX
              have e3 : 62 * X ≤ X * (62 * m) := by nlinarith
              have e4 : 2000 ≤ X * (2000 * m) := by
                calc 2000 ≤ 1 * (2000 * m) := by omega
                  _ ≤ X * (2000 * m) := Nat.mul_le_mul_right _ hX
              omega
          _ = X ^ 2 * (2872 * m) := by ring
          _ ≤ X ^ 3 * (3000 * m) := Nat.mul_le_mul y1 (by omega)
      have g2 : X * (X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500) ≤ X ^ 3 * (4000 * m) := by
        calc X * (X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500)
            ≤ X * (X * (X * (700 * m) + X * (120 * m)) + X * (X * (150 * m)) + X * (X * (300 * m)) + X * (X * (1500 * m))) := by
              refine Nat.mul_le_mul_left _ ?_
              have e0 : 1 ≤ X * X := Nat.mul_pos hX hX
              have e1 : X * (X * (270 * Lc + 700) + 120) ≤ X * (X * (700 * m) + X * (120 * m)) := by
                refine Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) ?_)
                calc 120 ≤ 1 * (120 * m) := by omega
                  _ ≤ X * (120 * m) := Nat.mul_le_mul_right _ hX
              have e2 : X * (30 * Lc + 150) ≤ X * (X * (150 * m)) := Nat.mul_le_mul_left _ (by
                calc 30 * Lc + 150 ≤ 1 * (150 * m) := by omega
                  _ ≤ X * (150 * m) := Nat.mul_le_mul_right _ hX)
              have e3 : 300 * Lc ≤ X * (X * (300 * m)) := by
                calc 300 * Lc ≤ 1 * (300 * m) := by omega
                  _ ≤ X * X * (300 * m) := Nat.mul_le_mul_right _ e0
                  _ = X * (X * (300 * m)) := by ring
              have e4 : 1500 ≤ X * (X * (1500 * m)) := by
                calc 1500 ≤ 1 * (1500 * m) := by omega
                  _ ≤ X * X * (1500 * m) := Nat.mul_le_mul_right _ e0
                  _ = X * (X * (1500 * m)) := by ring
              linarith
          _ = X ^ 3 * (2770 * m) := by ring
          _ ≤ X ^ 3 * (4000 * m) := Nat.mul_le_mul_left _ (by omega)
      have g3 : X * (2000 * Lc + 5000) ≤ X ^ 3 * (5000 * m) := Nat.mul_le_mul y2 (by omega)
      have g4 : 1060 ≤ X ^ 3 * (1060 * m) := by
        calc 1060 ≤ 1 * (1060 * m) := by omega
          _ ≤ X ^ 3 * (1060 * m) := Nat.mul_le_mul_right _ y3
      unfold tmB'
      linarith
    have f5 : mm * (tmB' Lc X + 60) ≤ X ^ 4 * (20000 * m) := by
      calc mm * (tmB' Lc X + 60) ≤ X * (X ^ 3 * (20000 * m)) := Nat.mul_le_mul h.mmX tb
        _ = X ^ 4 * (20000 * m) := by ring
    have f6 : 300 ≤ X ^ 4 * (300 * m) := by
      calc 300 ≤ 1 * (300 * m) := by omega
        _ ≤ X ^ 4 * (300 * m) := Nat.mul_le_mul_right _ (Nat.pow_pos hX)
    have f7 : X ^ 4 * (100 * m) + X ^ 4 * (130 * m) + X ^ 4 * (14000 * m) + X ^ 4 * (230 * m) + X ^ 4 * (20000 * m) +
        X ^ 4 * (300 * m) = X ^ 4 * (34760 * m) := by ring
    have f8 : X ^ 4 * (34760 * m) ≤ X ^ 4 * m ^ 4 := by
      refine Nat.mul_le_mul_left _ ?_
      calc 34760 * m ≤ m * m * m * m := by nlinarith [Nat.mul_le_mul hm1 hm1, Nat.mul_pos hm hm]
        _ = m ^ 4 := by ring
    omega
  have D3 : 60 * s + s * (60 * Lc + 100) ≤ s * (200 * m) := by
    calc 60 * s + s * (60 * Lc + 100) = s * (60 * Lc + 160) := by ring
      _ ≤ s * (200 * m) := Nat.mul_le_mul_left _ (by omega)
  have e10 : s * (200 * m) ≤ s * m ^ 10 := Nat.mul_le_mul_left _ (by
    calc 200 * m ≤ m * m := Nat.mul_le_mul_right _ (le_trans (by norm_num) hm1)
      _ = m ^ 2 := by ring
      _ ≤ m ^ 10 := h.mpow (by norm_num))
  have e11 : τ * k * m ^ 3 + τ * k ≤ τ * k * m ^ 10 := by
    calc τ * k * m ^ 3 + τ * k ≤ τ * k * m ^ 3 * 2 := by
          linarith [Nat.le_mul_of_pos_right (τ * k) (Nat.pow_pos hm (n := 3))]
      _ ≤ τ * k * m ^ 3 * m := Nat.mul_le_mul_left _ (by omega)
      _ = τ * k * m ^ 4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (h.mpow (by norm_num))
  have e12 : (s + K) * (60 * Lc + 100) = s * (60 * Lc + 100) + K * (60 * Lc + 100) := by ring
  generalize hW : K * (60 * Lc + 100) + K * (60 * Lc + 130) +
    (4 * (X * X) + 10 * X) * (stepB Lc X + 30) + X * (90 * Lc + 230) + mm * (tmB' Lc X + 60) + 300 = W at D2
  calc dealB Lc X K mm ub (mm * bd) (4 * (X * X) + 10 * X) s * v ^ 256 ≤
        (s * m ^ 10 + (W + mm * bd * ((ub + 1) * (60 * Lc + 100)))) * v ^ 256 :=
        Nat.mul_le_mul_right _ (by unfold dealB; omega)
    _ = s * v ^ 256 * m ^ 10 + W * v ^ 256 + mm * bd * ((ub + 1) * (60 * Lc + 100)) * v ^ 256 := by
        ring
    _ ≤ (s * v ^ 256 + τ * k) * m ^ 10 := by linarith

end CutNums

end Nc.Dl
