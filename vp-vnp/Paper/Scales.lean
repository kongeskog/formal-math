/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.NoAcc
import Paper.Circuit
import Paper.Cuts

/-!
# The paper, section "One scale is all scales"
-/

namespace Paper

open Finset NS1
open _root_.NS1.Tree

/-- If circuits with M^a gates are impossible whenever (lg M)^(Ca) ≤ M, then more than 2^((log M)^(4/3)/1600²) gates
are needed: take a = ⌈(log M)^(1/3)⌉. This is the rate of the main theorems in the contracting case. -/
theorem rate_of_exponents {P : ℕ → ℕ → Prop} (hmono : ∀ M s t, s ≤ t → P M s → P M t) {C M₁ : ℕ}
    (h : ∀ M ≥ M₁, ∀ a : ℕ, lg M ^ (C * a) ≤ M → ¬ P M (M ^ a)) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, P m s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  have ht : Filter.Tendsto (fun m : ℕ => Real.logb 2 m) Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have ho := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 2 / 3 by norm_num)).bound
    (show (0 : ℝ) < Real.log 2 / (4 * C + 4) by positivity)
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 ((ht.eventually ho).and (ht.eventually_ge_atTop 2))
  refine ⟨M₀ + M₁ + 2, fun m hm s hs => ?_⟩
  obtain ⟨h1, hL⟩ := hM₀ m (by omega)
  set L := Real.logb 2 m with hLd
  set l := Real.logb 2 L with hld
  have hL0 : 0 < L := by linarith
  have hl0 : 0 ≤ l := Real.logb_nonneg (by norm_num) (by linarith)
  have hlb : (4 * (C : ℝ) + 4) * l ≤ L ^ (2 / 3 : ℝ) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)),
      abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at h1
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : l ≤ L ^ (2 / 3 : ℝ) / (4 * C + 4) := by
      rw [hld, Real.logb, div_le_iff₀ hlog]
      calc Real.log L ≤ _ := h1
        _ = _ := by field_simp
    rwa [le_div_iff₀ (by positivity), mul_comm] at this
  have hc1 : (1 : ℝ) ≤ L ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  generalize ha : ⌈L ^ (1 / 3 : ℝ)⌉₊ = a
  have ha1 : (a : ℝ) ≤ 2 * L ^ (1 / 3 : ℝ) := by
    have := (Nat.ceil_lt_add_one (Real.rpow_nonneg hL0.le (1 / 3))).le
    rw [ha] at this
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlgR : (0 : ℝ) < lg m := by exact_mod_cast Nat.succ_pos _
  by_contra hb
  push Not at hb
  have hlg : Real.logb 2 (lg m) ≤ 2 * l := by
    have e : (lg m : ℝ) ≤ L ^ 2 := by
      have : ((Nat.log 2 m + 1 : ℕ) : ℝ) ≤ L + 1 := by
        push_cast
        exact add_le_add (Real.natLog_le_logb m 2) le_rfl
      calc (lg m : ℝ) ≤ L + 1 := this
        _ ≤ L ^ 2 := by nlinarith
    calc Real.logb 2 (lg m) ≤ Real.logb 2 (L ^ 2) := Real.logb_le_logb_of_le (by norm_num) hlgR e
      _ = 2 * l := by rw [Real.logb_pow]; push_cast; rfl
  have hkey : lg m ^ (C * a) ≤ m := by
    have key : ((C * a : ℕ) : ℝ) * Real.logb 2 (lg m) ≤ L := by
      push_cast
      calc (C : ℝ) * a * Real.logb 2 (lg m) ≤ C * (2 * L ^ (1 / 3 : ℝ)) * (2 * l) := by
            gcongr
            exact Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.succ_pos _)
        _ = L ^ (1 / 3 : ℝ) * (4 * C * l) := by ring
        _ ≤ L ^ (1 / 3 : ℝ) * L ^ (2 / 3 : ℝ) := by gcongr; linarith
        _ = L := by rw [← Real.rpow_add hL0]; norm_num
    have h3 := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) key
    rw [hLd, Real.rpow_logb (by norm_num) (by norm_num) hmR, mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hlgR, Real.rpow_natCast] at h3
    exact_mod_cast h3
  refine h m (by omega) a hkey (hmono m s _ ?_ hs)
  have h4 : (s : ℝ) ≤ (2 : ℝ) ^ (L * a) := by
    refine hb.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    calc L ^ (4 / 3 : ℝ) / 1600 ^ 2 ≤ L ^ (4 / 3 : ℝ) := div_le_self (Real.rpow_nonneg hL0.le _) (by norm_num)
      _ = L * L ^ (1 / 3 : ℝ) := by rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hL0, Real.rpow_one]
      _ ≤ L * a := by gcongr; exact ha ▸ Nat.le_ceil _
  rw [Real.rpow_mul (by norm_num), hLd, Real.rpow_logb (by norm_num) (by norm_num) hmR, Real.rpow_natCast] at h4
  exact_mod_cast h4

/-- "Otherwise let v = ⌊m^(1/B₀)⌋": at a large m = M it is large, v^B₀ ≤ M, and M^a ≤ v^(a′) for a′ = 2B₀a with
(lg v)^(E(a′+1)) ≤ v, if (lg M)^(Ca) ≤ M for a suitable C. -/
theorem exists_scale (B₀ E n : ℕ) (hB : 0 < B₀) : ∃ C M₁ : ℕ, ∀ M, M₁ ≤ M → ∀ a, lg M ^ (C * a) ≤ M →
    ∃ v, n ≤ v ∧ v ^ B₀ ≤ M ∧ M ^ a ≤ v ^ (2 * B₀ * a) ∧ lg v ^ (E * (2 * B₀ * a + 1)) ≤ v := by
  obtain ⟨n1, hn1⟩ := poly_lg 1 (2 * (E * (2 * B₀ + 1)))
  refine ⟨2 * (2 * B₀) * (E * (2 * B₀ + 1)), (n + n1 + 4) ^ B₀, fun M hM a ha => ?_⟩
  obtain ⟨v, hv, hvM, hMv⟩ := exists_root B₀ (n + n1 + 4) M hB hM
  have hM2 : M ≤ v ^ (2 * B₀) := by
    refine hMv.le.trans ((Nat.pow_le_pow_left (aux3 (show 2 ≤ v by omega)) B₀).trans (le_of_eq ?_))
    rw [← pow_mul]
  refine ⟨v, by omega, hvM, (Nat.pow_le_pow_left hM2 a).trans (le_of_eq (pow_mul _ _ _).symm), ?_⟩
  refine le_trans (Nat.pow_le_pow_right (Nat.succ_pos _) ?_) (lg_pow_transport (b := 2 * B₀) (by omega)
    ((Nat.le_self_pow (by omega) v).trans hvM) hM2 ha (by simpa using hn1 v (by omega)))
  rw [mul_assoc E (2 * B₀ + 1)]
  refine Nat.mul_le_mul_left E ?_
  calc 2 * B₀ * a + 1 ≤ (2 * B₀ + 1) * a + (2 * B₀ + 1) := by rw [add_mul]; omega
    _ = (2 * B₀ + 1) * (a + 1) := by ring

end Paper
