/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Main
import NS1.Compose

/-!
# Cuts one after the other

From one cut by any factor k ≤ v ^ 64 at the scale v, cuts down to v ^ H steps: the induction on the numbers of steps,
sizes and pieces.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem CutD.mono {τ s τ' s' P t τ'' s'' P' t' : ℕ} {G : Tree} (h : CutD θ τ s τ' s' P t G) (h1 : τ' ≤ τ'')
    (h2 : s' ≤ s'') (h3 : P ≤ P') (h4 : t ≤ t') : CutD θ τ s τ'' s'' P' t' G := by
  intro z hz
  obtain ⟨Q, hD, hQ, hv⟩ := h z hz
  exact ⟨Q, hD.mono h4, fun q hq => ⟨(hQ q hq).1.trans h3, fun y hy => ((hQ q hq).2 y hy).trans h2⟩, fun hp =>
    ⟨fun q hq y hy => ((hv hp).1 q hq y hy).of_le h1, (hv hp).2⟩⟩

section Iterate

variable {v a₀ H Λ : ℕ}

/-- The hypothesis at one `v`: a cut by `k` into pieces of `τ'` steps, for any `τ'` at least the
quotient of `τ * Λ` by `k`, of size `s'` and in time `t` with `s' * k` and `t` at most
`(s + τ * k / v ^ 256) * Λ`, stated without the quotients. -/
def OneCutAt (θ : List Bool → A) (v a₀ Λ : ℕ) : Prop := ∀ τ s k τ', v ^ a₀ ≤ τ → 4 * lg τ ≤ lg v ^ 2 →
  s ≤ τ → 2 ≤ k → k ≤ v ^ 64 → τ * Λ < k * (τ' + 1) → ∃ (G : Tree) (s' t : ℕ), G.size ≤ v ^ a₀ ∧
    CutD θ τ s τ' s' (k * Λ) t G ∧ s' * k * v ^ 256 ≤ (s * v ^ 256 + τ * k) * Λ ∧
    t * v ^ 256 ≤ (s * v ^ 256 + τ * k) * Λ

/-- **Paper: Theorem thm:cut, the induction on (τ_i, s_i, P_i).** Cut by v^63 as long as the steps are many, and at last
once to v^H; sizes, pieces and time. -/
theorem _root_.Paper.thm_cut_iterate (hc : OneCutAt θ v a₀ Λ) (hv : 1000 ≤ v) (hΛ2 : 2 ≤ Λ) (hΛv : Λ ≤ v) (hH : a₀ ≤ H) (hH' : 200 ≤ H) :
    ∀ r τ s c, v ^ H ≤ τ → 4 * lg τ ≤ lg v ^ 2 → τ * Λ < v ^ H * v ^ (64 + 62 * r) → s * v ^ 48 ≤ c * τ → 1 ≤ c →
      c * 4 ^ (r + 1) ≤ v → ∃ (G : Tree) (P t s' : ℕ), CutD θ τ s (v ^ H) s' P t G ∧
      P * v ^ H ≤ τ * (4 * Λ ^ 2) ^ (r + 1) ∧ t * v ^ 48 ≤ c * τ * (100 * Λ ^ 3) ^ (r + 1) ∧
      s' * v ^ 48 ≤ c * v ^ H * (8 * Λ) ^ (r + 1) ∧ G.size ≤ 4 ^ r * (v ^ a₀ + 3000) := by
  have hv1 : 1 ≤ v := by omega
  have hΛ1 : 1 ≤ Λ := by omega
  have ppos : ∀ a, 0 < v ^ a := fun a => Nat.pow_pos (by omega)
  have pmono : ∀ {a b}, a ≤ b → v ^ a ≤ v ^ b := fun h => Nat.pow_le_pow_right hv1 h
  have hsτ : ∀ {τ s c}, s * v ^ 48 ≤ c * τ → c ≤ v → s ≤ τ := fun hs hcv =>
    Nat.le_of_mul_le_mul_right (hs.trans (by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (hcv.trans (Nat.le_self_pow (by norm_num) v)))) (ppos 48)
  -- the first cut to the target
  have base : ∀ τ s c, v ^ H ≤ τ → 4 * lg τ ≤ lg v ^ 2 → τ * Λ < v ^ H * v ^ 64 → s * v ^ 48 ≤ c * τ → 1 ≤ c → c ≤ v →
      ∃ (G : Tree) (P t s' : ℕ), CutD θ τ s (v ^ H) s' P t G ∧ P * v ^ H ≤ τ * (4 * Λ ^ 2) ∧
      t * v ^ 48 ≤ c * τ * (100 * Λ ^ 3) ∧ s' * v ^ 48 ≤ c * v ^ H * (8 * Λ) ∧ G.size ≤ v ^ a₀ := by
    intro τ s c hτ hlτ hτΛ hs hc1 hcv
    obtain ⟨k, hk⟩ := exists_eq (a' := τ * Λ / v ^ H + 1)
    have hk1 : τ * Λ < k * v ^ H := hk ▸ (Nat.div_lt_iff_lt_mul (ppos H)).1 (Nat.lt_succ_self _)
    have hk2 : k ≤ v ^ 64 :=
      hk ▸ (Nat.div_lt_iff_lt_mul (ppos H)).2 (by rw [Nat.mul_comm (v ^ 64)]; exact hτΛ)
    have hk3 : k * v ^ H ≤ τ * Λ + v ^ H := by
      rw [hk, add_mul, one_mul]
      exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
    have hk0 : 2 ≤ k := Nat.lt_of_mul_lt_mul_left (a := v ^ H) <|
      calc v ^ H * 1 < v ^ H * Λ := Nat.mul_lt_mul_of_pos_left (by omega) (ppos H)
        _ ≤ τ * Λ := Nat.mul_le_mul_right _ hτ
        _ < v ^ H * k := Nat.mul_comm k _ ▸ hk1
    have h208 : v ^ 256 = v ^ 48 * v ^ 208 := by rw [← pow_add]
    have hk208 : k ≤ v ^ 208 := hk2.trans (pmono (by norm_num))
    obtain ⟨G, s', t, hG, hcut, hs', ht⟩ := hc τ s k (v ^ H) ((pmono hH).trans hτ) hlτ (hsτ hs hcv) hk0
      hk2 (hk1.trans_le (Nat.mul_le_mul_left _ (Nat.le_succ _)))
    refine ⟨G, _, t, s', hcut, ?_, ?_, ?_, hG⟩
    · grw [mul_right_comm, hk3, hτ]
      linarith only [Nat.mul_le_mul_left (τ * Λ) hΛ1, Nat.zero_le (τ * Λ ^ 2)]
    · refine Nat.le_of_mul_le_mul_right (c := v ^ 208) ?_ (ppos 208)
      calc t * v ^ 48 * v ^ 208 ≤ (s * v ^ 48 * v ^ 208 + τ * k) * Λ := by
            rw [Nat.mul_assoc, ← h208, Nat.mul_assoc s, ← h208]; exact ht
        _ ≤ (c * τ * v ^ 208 + c * τ * v ^ 208) * Λ := by
          gcongr; exact Nat.le_mul_of_pos_left _ hc1
        _ = c * τ * (2 * Λ) * v ^ 208 := by ring
        _ ≤ _ := by grw [← Nat.le_self_pow (show 3 ≠ 0 by norm_num) Λ]; gcongr; omega
    · refine Nat.le_of_mul_le_mul_right (c := k * v ^ 208) ?_ (by positivity)
      calc s' * v ^ 48 * (k * v ^ 208) = s' * k * v ^ 256 := by rw [h208]; ring
        _ ≤ (s * v ^ 48 * v ^ 208 + τ * k) * Λ := by rw [Nat.mul_assoc s, ← h208]; exact hs'
        _ ≤ c * (τ * Λ) * v ^ 208 + τ * Λ * k := by linarith [Nat.mul_le_mul_right (Λ * v ^ 208) hs]
        _ ≤ c * (k * v ^ H) * v ^ 208 + k * v ^ H * v ^ 208 := by gcongr
        _ = (c + 1) * (v ^ H * (k * v ^ 208)) := by ring
        _ ≤ 8 * c * Λ * (v ^ H * (k * v ^ 208)) := Nat.mul_le_mul_right _ (by nlinarith)
        _ = c * v ^ H * (8 * Λ) * (k * v ^ 208) := by ring
  intro r
  induction r with
  | zero =>
    intro τ s c hτ hlτ hτΛ hs hc1 hcv
    obtain ⟨G, P, t, s', h1, h2, h3, h4, h5⟩ := base τ s c hτ hlτ (by simpa using hτΛ) hs hc1 (by omega)
    refine ⟨G, P, t, s', h1, by simpa using h2, by simpa using h3, by simpa using h4, ?_⟩
    simp only [pow_zero, one_mul]
    omega
  | succ r ih =>
    intro τ s c hτ hlτ hτΛ hs hc1 hcv
    have hc4 : 4 * c * 4 ^ (r + 1) ≤ v := by
      convert hcv using 1
      ring
    have h41 : 1 ≤ 4 ^ (r + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hc4v : 4 * c ≤ v := (Nat.le_mul_of_pos_right _ h41).trans hc4
    have hX1 : 1 ≤ (4 * Λ ^ 2) ^ (r + 1) := Nat.one_le_pow _ _ (by positivity)
    have hX2 : 1 ≤ (100 * Λ ^ 3) ^ (r + 1) := Nat.one_le_pow _ _ (by positivity)
    have hX3 : 1 ≤ (8 * Λ) ^ (r + 1) := Nat.one_le_pow _ _ (by positivity)
    by_cases hbase : τ * Λ < v ^ H * v ^ 64
    · obtain ⟨G, P, t, s', h1, h2, h3, h4, h5⟩ := base τ s c hτ hlτ hbase hs hc1 (by omega)
      refine ⟨G, P, t, s', h1, ?_, ?_, ?_, ?_⟩
      · refine h2.trans (Nat.mul_le_mul_left _ ?_)
        rw [pow_succ (4 * Λ ^ 2) (r + 1)]
        exact Nat.le_mul_of_pos_left _ hX1
      · refine h3.trans (Nat.mul_le_mul_left _ ?_)
        rw [pow_succ (100 * Λ ^ 3) (r + 1)]
        exact Nat.le_mul_of_pos_left _ hX2
      · refine h4.trans (Nat.mul_le_mul_left _ ?_)
        rw [pow_succ (8 * Λ) (r + 1)]
        exact Nat.le_mul_of_pos_left _ hX3
      · grw [← h41]
        omega
    -- one cut by v ^ 63, then the rest
    push Not at hbase
    have hk63 : 2 ≤ v ^ 63 := (by omega : 2 ≤ v).trans (Nat.le_self_pow (by norm_num) v)
    have hτ₁lt := Nat.lt_mul_div_succ (τ * Λ) (ppos 63)
    obtain ⟨G₁, s₁, t₁, hG₁, hcut₁, hs₁, ht₁⟩ := hc τ s (v ^ 63) (τ * Λ / v ^ 63) ((pmono hH).trans hτ)
      hlτ (hsτ hs (by omega)) hk63 (pmono (by norm_num)) hτ₁lt
    generalize hτ₁ : τ * Λ / v ^ 63 = τ₁ at hcut₁ hτ₁lt
    have hτ₁le : τ₁ * v ^ 63 ≤ τ * Λ := by rw [← hτ₁]; exact Nat.div_mul_le_self _ _
    have hτ₁V : v ^ H ≤ τ₁ := by
      rw [← hτ₁, Nat.le_div_iff_mul_le (ppos 63)]
      exact (Nat.mul_le_mul_left _ (pmono (by norm_num))).trans hbase
    have hτ₁half : τ * Λ ≤ 2 * (τ₁ * v ^ 63) := by
      linarith [Nat.le_mul_of_pos_left (v ^ 63) (lt_of_lt_of_le (ppos H) hτ₁V)]
    have hτ₁τ : τ₁ ≤ τ := by
      have : τ₁ * v ^ 63 ≤ τ * v ^ 63 := hτ₁le.trans (Nat.mul_le_mul_left _ (hΛv.trans (Nat.le_self_pow (by norm_num) v)))
      exact Nat.le_of_mul_le_mul_right this (ppos 63)
    have hτ₁Λ : τ₁ * Λ < v ^ H * v ^ (64 + 62 * r) := by
      have h1 : τ₁ * v ^ 63 < v ^ H * v ^ (63 + 62 * r) * v ^ 63 := by
        calc τ₁ * v ^ 63 ≤ τ * Λ := hτ₁le
          _ < v ^ H * v ^ (64 + 62 * (r + 1)) := hτΛ
          _ = v ^ H * v ^ (63 + 62 * r) * v ^ 63 := by
            rw [Nat.mul_assoc, ← pow_add]
            ring
      have h2 : τ₁ < v ^ H * v ^ (63 + 62 * r) := lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
      calc τ₁ * Λ ≤ τ₁ * v := Nat.mul_le_mul_left _ hΛv
        _ < v ^ H * v ^ (63 + 62 * r) * v := Nat.mul_lt_mul_of_pos_right h2 (by omega)
        _ = v ^ H * v ^ (64 + 62 * r) := by
          rw [Nat.mul_assoc, ← pow_succ]
          congr 2
          ring
    have hs₁c : s₁ * v ^ 48 ≤ 4 * c * τ₁ := by
      refine Nat.le_of_mul_le_mul_right (c := v ^ 63 * v ^ 256) ?_ (by positivity)
      have a1 : τ * v ^ 63 * v ^ 48 ≤ c * τ * v ^ 256 := by
        calc τ * v ^ 63 * v ^ 48 = τ * v ^ 111 := by rw [Nat.mul_assoc, ← pow_add]
          _ ≤ c * τ * v ^ 256 := Nat.mul_le_mul (Nat.le_mul_of_pos_left _ hc1) (pmono (by norm_num))
      calc s₁ * v ^ 48 * (v ^ 63 * v ^ 256) = s₁ * v ^ 63 * v ^ 256 * v ^ 48 := by ring
        _ ≤ (s * v ^ 256 + τ * v ^ 63) * Λ * v ^ 48 := Nat.mul_le_mul_right _ hs₁
        _ = (s * v ^ 48 * v ^ 256 + τ * v ^ 63 * v ^ 48) * Λ := by ring
        _ ≤ (c * τ * v ^ 256 + c * τ * v ^ 256) * Λ := by gcongr
        _ = 2 * c * (τ * Λ) * v ^ 256 := by ring
        _ ≤ 2 * c * (2 * (τ₁ * v ^ 63)) * v ^ 256 := by gcongr
        _ = 4 * c * τ₁ * (v ^ 63 * v ^ 256) := by ring
    obtain ⟨G₂, P₂, t₂, s₂, hcut₂, hP₂, ht₂, hs₂, hG₂⟩ := ih τ₁ s₁ (4 * c) hτ₁V ((Nat.mul_le_mul_left 4 (lg_mono hτ₁τ)).trans hlτ) hτ₁Λ hs₁c (by omega) hc4
    have hP : v ^ 63 * Λ * P₂ * v ^ H ≤ τ * (4 * Λ ^ 2) ^ (r + 1 + 1) := by
      grw [mul_assoc, hP₂, mul_mul_mul_comm, mul_comm (v ^ 63), hτ₁le, pow_succ _ (r + 1)]
      ring_nf; omega
    refine ⟨_, _, _, _, Paper.thm_cut_compose hcut₁ hcut₂, hP, ?_, ?_, ?_⟩
    · -- time
      have b1 : t₁ * v ^ 48 ≤ c * τ * (2 * Λ) := by
        refine Nat.le_of_mul_le_mul_right (c := v ^ 208) ?_ (ppos 208)
        have a1 : τ * v ^ 63 ≤ c * τ * v ^ 208 :=
          Nat.mul_le_mul (Nat.le_mul_of_pos_left _ hc1) (pmono (by norm_num))
        calc t₁ * v ^ 48 * v ^ 208 = t₁ * v ^ 256 := by rw [Nat.mul_assoc, ← pow_add]
          _ ≤ (s * v ^ 48 * v ^ 208 + τ * v ^ 63) * Λ := by
            rw [Nat.mul_assoc s, ← pow_add]; exact ht₁
          _ ≤ (c * τ * v ^ 208 + c * τ * v ^ 208) * Λ := by gcongr
          _ = c * τ * (2 * Λ) * v ^ 208 := by ring
      have b2 : v ^ 63 * Λ * t₂ * v ^ 48 ≤ c * τ * (4 * Λ ^ 2 * (100 * Λ ^ 3) ^ (r + 1)) := by
        linarith only [Nat.mul_le_mul_left (v ^ 63 * Λ) ht₂,
          Nat.mul_le_mul_right (4 * c * Λ * (100 * Λ ^ 3) ^ (r + 1)) hτ₁le]
      have b3 : v ^ 63 * Λ * (62 * P₂) * v ^ 48 ≤ c * τ * (4 * Λ ^ 2) ^ (r + 1 + 1) := by
        have hv62 : 62 * v ^ 48 ≤ v ^ H := by
          grw [← pmono (show 49 ≤ H by omega), pow_succ' v 48]
          gcongr; omega
        grw [mul_assoc, mul_assoc 62, mul_left_comm 62, hv62, ← mul_assoc, hP, mul_assoc c, ← hc1,
          one_mul]
      have b4 : v ^ 63 * Λ * 110 * v ^ 48 + 100 * v ^ 48 ≤ c * τ * 2 := by
        have h1 : v ^ 63 * Λ * 110 * v ^ 48 ≤ τ := by
          calc v ^ 63 * Λ * 110 * v ^ 48 ≤ v ^ 63 * v * v * v ^ 48 :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hΛv) (by omega))
            _ = v ^ 113 := by ring
            _ ≤ v ^ H := pmono (by omega)
            _ ≤ τ := hτ
        have h2 : 100 * v ^ 48 ≤ τ := by
          calc 100 * v ^ 48 ≤ v * v ^ 48 := Nat.mul_le_mul_right _ (by omega)
            _ = v ^ 49 := by rw [← pow_succ']
            _ ≤ v ^ H := pmono (by omega)
            _ ≤ τ := hτ
        have h3 : τ ≤ c * τ := Nat.le_mul_of_pos_left _ hc1
        omega
      have hL3 : Λ ≤ Λ ^ 3 := Nat.le_self_pow (by norm_num) Λ
      have hL2 : Λ ^ 2 ≤ Λ ^ 3 := Nat.pow_le_pow_right hΛ1 (by norm_num)
      obtain ⟨X, hX⟩ := exists_eq (a' := (100 * Λ ^ 3) ^ (r + 1))
      have c1 : 2 * Λ ≤ 2 * Λ ^ 3 * X := by
        rw [hX]
        grw [← hX2]
        omega
      have c2 : 4 * Λ ^ 2 * X ≤ 4 * Λ ^ 3 * X := Nat.mul_le_mul_right _ (by omega)
      have c3 : (4 * Λ ^ 2) ^ (r + 1 + 1) ≤ 4 * Λ ^ 3 * X := by
        rw [pow_succ, hX, Nat.mul_comm]
        exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _)
      have c4 : 2 ≤ 2 * Λ ^ 3 * X := by
        have : 1 ≤ Λ ^ 3 := Nat.one_le_pow _ _ hΛ1
        grw [← this, hX, ← hX2]
      have c5 : (100 * Λ ^ 3) ^ (r + 1 + 1) = 100 * Λ ^ 3 * X := by rw [pow_succ, hX]; ring
      calc (t₁ + v ^ 63 * Λ * (t₂ + 62 * P₂ + 110) + 100) * v ^ 48 = t₁ * v ^ 48 + v ^ 63 * Λ * t₂ * v ^ 48 +
            v ^ 63 * Λ * (62 * P₂) * v ^ 48 + (v ^ 63 * Λ * 110 * v ^ 48 + 100 * v ^ 48) := by ring
        _ ≤ c * τ * (2 * Λ) + c * τ * (4 * Λ ^ 2 * X) + c * τ * (4 * Λ ^ 2) ^ (r + 1 + 1) + c * τ * 2 := by
            rw [hX]
            exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add b1 b2) b3) b4
        _ = c * τ * (2 * Λ + 4 * Λ ^ 2 * X + (4 * Λ ^ 2) ^ (r + 1 + 1) + 2) := by ring
        _ ≤ c * τ * (100 * Λ ^ 3 * X) := Nat.mul_le_mul_left _ (by
            have : 2 * Λ ^ 3 * X + 4 * Λ ^ 3 * X + 4 * Λ ^ 3 * X + 2 * Λ ^ 3 * X ≤ 100 * Λ ^ 3 * X := by
              have e : 2 * Λ ^ 3 * X + 4 * Λ ^ 3 * X + 4 * Λ ^ 3 * X + 2 * Λ ^ 3 * X = 12 * (Λ ^ 3 * X) := by ring
              have e' : 100 * Λ ^ 3 * X = 100 * (Λ ^ 3 * X) := by ring
              omega
            omega)
        _ = c * τ * (100 * Λ ^ 3) ^ (r + 1 + 1) := by rw [c5]
    · rw [pow_succ _ (r + 1)]
      linarith only [hs₂,
        Nat.mul_le_mul_left (c * v ^ H * (8 * Λ) ^ (r + 1)) (show 4 ≤ 8 * Λ by omega)]
    · have := size_compC G₁ G₂
      have e : 4 ^ (r + 1) * (v ^ a₀ + 3000) = 4 * (4 ^ r * (v ^ a₀ + 3000)) := by rw [pow_succ]; ring
      have h4r : 1 ≤ 4 ^ r := Nat.one_le_pow _ _ (by norm_num)
      have : v ^ a₀ + 3000 ≤ 4 ^ r * (v ^ a₀ + 3000) := Nat.le_mul_of_pos_left _ h4r
      omega

end Iterate

theorem OneCutAt.mono {v a₀ Λ Λ' : ℕ} (h : OneCutAt θ v a₀ Λ) (hΛ : Λ ≤ Λ') : OneCutAt θ v a₀ Λ' := by
  intro τ s k τ' h1 h2 h3 h4 h5 h6
  obtain ⟨G, s', t, hG, hcut, hs', ht⟩ :=
    h τ s k τ' h1 h2 h3 h4 h5 ((Nat.mul_le_mul_left _ hΛ).trans_lt h6)
  exact ⟨G, s', t, hG, hcut.mono le_rfl le_rfl (Nat.mul_le_mul_left _ hΛ) le_rfl,
    hs'.trans (Nat.mul_le_mul_left _ hΛ), ht.trans (Nat.mul_le_mul_left _ hΛ)⟩

/-- Powers of the logarithm that are at most `v` bound the exponent by the logarithm. -/
theorem le_lg_of_lg_pow_le {v k : ℕ} (hv : 4 ≤ v) (hk : lg v ^ k ≤ v) : k ≤ lg v := by
  have h1 : 2 ^ k < 2 ^ lg v :=
    lt_of_le_of_lt ((Nat.pow_le_pow_left (lg_ge_two hv) k).trans hk) (lt_two_pow_lg v)
  exact ((Nat.pow_lt_pow_iff_right (by norm_num)).1 h1).le

/-- The iterated cuts lose at most `v`, if `(lg v) ^ (C₀ * α) ≤ v` for the constant `C₀` below. -/
theorem polylog_loss_le {h C v α : ℕ} (hl : 100 ≤ lg v) (hα : 1 ≤ α)
    (hlog : lg v ^ ((3 * C + 4) * (32 * h + 2) * α) ≤ v) :
    (100 * (lg v ^ (C + 1)) ^ 3) ^ (16 * h * α + 1) ≤ v := by
  calc (100 * (lg v ^ (C + 1)) ^ 3) ^ (16 * h * α + 1) ≤ (lg v * (lg v ^ (C + 1)) ^ 3) ^ (16 * h * α + 1) :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hl) _
    _ = lg v ^ ((3 * C + 4) * (16 * h * α + 1)) := by
        rw [← pow_mul (lg v) (C + 1) 3, ← pow_succ', ← pow_mul]
        congr 1
        ring
    _ ≤ lg v ^ ((3 * C + 4) * (32 * h + 2) * α) := Nat.pow_le_pow_right (by omega) (by
        rw [Nat.mul_assoc (3 * C + 4) (32 * h + 2)]
        refine Nat.mul_le_mul_left _ ?_
        have : (32 * h + 2) * α = 16 * h * α + 16 * h * α + 2 * α := by ring
        omega)
    _ ≤ v := hlog

end NS1
