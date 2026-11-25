/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Relay
import Nc.Price.Norm

/-!
# Pairs of chambers

Two facts about unordered pairs, used to build the laws at the vertices of a tower (`VLaws`) from prices.
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Nc.Price

theorem out_mk {Fl : Type} (q : Sym2 Fl) : s(q.out.1, q.out.2) = q := Quot.out_eq q

/-- Sums over ordered and over unordered pairs. -/
theorem sum_off {Fl : Type} [Fintype Fl] [DecidableEq Fl] (f : Sym2 Fl → ℝ) :
    ∑ p, ∑ q, (if p = q then 0 else f s(p, q)) = 2 * ∑ q : Sym2 Fl, if q.IsDiag then 0 else f q := by
  rw [← Fintype.sum_prod_type' (f := fun p q => if p = q then (0 : ℝ) else f s(p, q)),
    ← Finset.sum_fiberwise (s := Finset.univ) (g := fun x : Fl × Fl => s(x.1, x.2)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  induction q with
  | h a b =>
    by_cases hab : a = b
    · subst hab
      rw [if_pos (Sym2.mk_isDiag_iff.2 rfl), mul_zero]
      refine Finset.sum_eq_zero fun x hx => ?_
      -- by `Sym2.eq_iff`, `x = (a, a)`, so the `if` is true and the term is 0
      grind
    · rw [if_neg (fun h => hab (Sym2.mk_isDiag_iff.1 h))]
      have hf : (Finset.univ.filter fun x : Fl × Fl => s(x.1, x.2) = s(a, b)) = {(a, b), (b, a)} := by
        ext ⟨x, y⟩
        simp
      -- rewrite by `hf`, sum over the pair `(a, b)`, `(b, a)`, both `if`s false, `s(a, b) = s(b, a)`
      grind

end Nc.Tow
