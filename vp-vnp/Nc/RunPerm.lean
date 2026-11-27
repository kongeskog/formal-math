/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.RunSum

/-!
# The sum over runs with finite domains: literals, counts
-/

set_option linter.unusedSectionVars false

namespace Nc

open Finset MvPolynomial

section Degree

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

end Degree

section Count

theorem card_ChN (S : Type) [Fintype S] (n : ℕ) : Fintype.card (Ch S (Fin n)) = 2 * Fintype.card S + n := by
  rw [← Fintype.card_congr (proxy_equiv% (Ch S (Fin n)))]
  simp [mul_comm]

variable {Γ S Q : Type} [Fintype Γ] [Fintype S] [Fintype Q] {n t M N B : ℕ}

theorem card_letter_le (hΓ : Fintype.card Γ ≤ B) (hS : Fintype.card S ≤ B) (hn : n ≤ B) (hB : 1 ≤ B) :
    Fintype.card (Letter S (Fin n) Γ) ≤ 4 * B ^ 2 := by
  rw [Fintype.card_option, Fintype.card_prod, card_ChN]
  grw [hΓ, hS, hn]
  have := Nat.one_le_pow 2 B hB
  ring_nf; omega

theorem card_RD_le (hS : Fintype.card S ≤ B) (hn : n ≤ B) (ht : t + 1 ≤ B) (hM : M ≤ B) :
    Fintype.card (RD S n t M) ≤ 6 * B ^ 2 := by
  have ht' : t ≤ B := by omega
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_ChN]
  grw [ht, ht', hS, hn, hM]
  have := Nat.le_self_pow (by decide : 2 ≠ 0) B
  ring_nf; omega

theorem card_RE_le [DecidableEq Γ] [DecidableEq S] [DecidableEq Q] (hΓ : Fintype.card Γ + 1 ≤ B)
    (hS : Fintype.card S ≤ B) (hQ : Fintype.card Q ≤ B) (hn : n ≤ B) (ht : t + 1 ≤ B) (hM : M ≤ B) (hB : 1 ≤ B) :
    Fintype.card (Σ d, RE Γ S Q n t M d) ≤ 9 * B ^ 3 := by
  have ht' : t ≤ B := by omega
  have hL := card_letter_le (Γ := Γ) (S := S) (n := n) (by omega) hS hn hB
  rw [Fintype.card_sigma, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  change (∑ _ : Fin t, Fintype.card (Letter S (Fin n) Γ)) + ((∑ _ : Fin (t + 1), Fintype.card Q) +
    ((∑ _ : Ch S (Fin n) × Fin (t + 1), Fintype.card (Fin M)) +
      ∑ _ : S × Fin M, Fintype.card (Option Γ))) ≤ _
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin,
    Fintype.card_prod, card_ChN]
  rw [Fintype.card_option (α := Γ)]
  grw [hL, ht, ht', hQ, hS, hn, hM, hΓ]
  have : B ^ 2 ≤ B ^ 3 := Nat.pow_le_pow_right hB (by decide)
  ring_nf; omega

theorem card_RS_le (hΓ : Fintype.card Γ + 1 ≤ B) (hS : Fintype.card S ≤ B) (hQ : Fintype.card Q ≤ B)
    (hn : n ≤ B) (ht : t ≤ B) (hB : 1 ≤ B) : Fintype.card (RS Γ S Q n t) ≤ 4 * B ^ 5 := by
  have hL := card_letter_le (Γ := Γ) (S := S) (n := n) (by omega) hS hn hB
  simp only [Fintype.card_prod, Fintype.card_fin]
  calc _ ≤ B * (4 * B ^ 2 * (B * B)) := by gcongr
    _ = 4 * B ^ 5 := by ring

theorem card_RH_le (hΓ : Fintype.card Γ + 1 ≤ B) (hS : Fintype.card S ≤ B)
    (hn : n ≤ B) (ht : t ≤ B) (hM : M ≤ B) (hB : 1 ≤ B) : Fintype.card (RH Γ S n t M) ≤ 25 * B ^ 5 := by
  have hL := card_letter_le (Γ := Γ) (S := S) (n := n) (by omega) hS hn hB
  have hΓ' : Fintype.card Γ ≤ B := by omega
  have h (k : ℕ) (hk : k ≤ 5) : B ^ k ≤ B ^ 5 := Nat.pow_le_pow_right hB hk
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  rw [card_ChN]
  grw [hL, hΓ', hS, hn, ht, hM]
  linarith only [h 0 (by decide), h 1 (by decide), h 2 (by decide),
    h 3 (by decide), h 4 (by decide)]

end Count

section Main

variable {F : Type*} [Field F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]

/-- The total length of the words with their separators. -/
theorem length_wordOf_ofFn {n : ℕ} (u : Fin n → List Γ) :
    (wordOf (List.ofFn u)).length = (∑ j, (u j).length) + n := by
  rw [length_wordOf, List.map_ofFn, List.sum_ofFn, List.length_ofFn]
  rfl

end Main

end Nc
