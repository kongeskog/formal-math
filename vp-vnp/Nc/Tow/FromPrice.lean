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
      have := (Finset.mem_filter.1 hx).2
      rw [Sym2.eq_iff] at this
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [if_pos (h1.trans h2.symm)]
    · rw [if_neg (fun h => hab (Sym2.mk_isDiag_iff.1 h))]
      have hf : (Finset.univ.filter fun x : Fl × Fl => s(x.1, x.2) = s(a, b)) = {(a, b), (b, a)} := by
        ext ⟨x, y⟩
        simp
      rw [hf, Finset.sum_pair (fun h => hab (Prod.ext_iff.1 h).1), if_neg hab, if_neg (Ne.symm hab),
        Sym2.eq_swap (a := b)]
      ring

end Nc.Tow
