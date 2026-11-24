/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Tab

/-!
# Codes of finite types
-/

namespace Nc.Dl

open NS1 Finset

/-- The first `L` binary digits. -/
def bitsN (L n : ℕ) : List Bool := List.ofFn fun i : Fin L => n.testBit i

theorem length_bitsN (L n : ℕ) : (bitsN L n).length = L := by simp [bitsN]

theorem bitsN_inj {L n n' : ℕ} (hn : n < 2 ^ L) (hn' : n' < 2 ^ L) (h : bitsN L n = bitsN L n') : n = n' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < L
  · exact congrFun (List.ofFn_injective h) ⟨i, hi⟩
  · rw [Nat.testBit_lt_two_pow (hn.trans_le (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi))),
      Nat.testBit_lt_two_pow (hn'.trans_le (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi)))]

/-- A finite type has a code of fixed length. -/
theorem exists_code (α : Type) [Fintype α] {L : ℕ} (h : Fintype.card α ≤ 2 ^ L) :
    ∃ code : α → List Bool, Function.Injective code ∧ ∀ a, (code a).length = L := by
  refine ⟨fun a => bitsN L (Fintype.equivFin α a), fun a b hab => ?_, fun a => length_bitsN _ _⟩
  have h1 := ((Fintype.equivFin α a).2).trans_le h
  have h2 := ((Fintype.equivFin α b).2).trans_le h
  have := bitsN_inj h1 h2 hab
  exact (Fintype.equivFin α).injective (Fin.ext this)

/-- The value of the binary digits (lowest first). -/
theorem val_bitsN (L n : ℕ) (hn : n < 2 ^ L) : KT.val (bitsN L n) = n := by
  induction L generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    subst this
    rfl
  | succ L ih =>
    have e : bitsN (L + 1) n = (n.testBit 0) :: bitsN L (n / 2) := by
      rw [bitsN, List.ofFn_succ]
      congr 1
      unfold bitsN
      congr 1
      funext i
      simp [Nat.testBit_succ]
    rw [e, KT.val, ih (n / 2) (by rw [pow_succ] at hn; omega), Nat.testBit_zero]
    have := Nat.div_add_mod n 2
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · simp [h]; omega
    · simp [h]; omega

end Nc.Dl
