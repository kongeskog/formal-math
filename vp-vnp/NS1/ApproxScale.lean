/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.ApproxRound

/-!
# From one scale to the next, approximately
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree LaurentPolynomial

variable {A : Type} [CommRing A] {θ : List Bool → A} {E : Type} [CommRing E] [Algebra A E]

theorem size_roundA {R : Type} (K : KT R) (B J : ℕ) (D G p : Tree) :
    (roundA K B J D G p).code.size ≤ D.size + G.size + p.size + (gt id J B K [false]).code.size +
      2 * WN.code.size + 2000 := by
  have := size_LP D
  have hw : 2 * flatB.code.size ≤ WN.code.size := by
    simp only [WN, CK, lett, foldF, app, Fm.code, Tree.size, size_num]
    omega
  simp only [roundA, stepA, renF, preF, guessF, lett, node, leaf, app, foldF, foldB, ZE, Fm.code,
    Tree.size, size_num, one]
  omega

/-- **The exponents of the outer weights**: products of powers of constants of span `M`. -/
theorem span_expand_budg {K : KT E[T;T⁻¹]} {M B J : ℕ} (hM : K.All (Span M)) {q : Bt × E[T;T⁻¹]}
    (hq : q ∈ (K.expand B).budg J) : Span ((K.expand B).nds * 2 ^ J * (2 ^ B * M)) q.2 :=
  span_budg (hM.expand (Q := Span (2 ^ B * M)) fun _ hc _ hb =>
    (hc.pow _).mono (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hb.le))) hq

end NS1
