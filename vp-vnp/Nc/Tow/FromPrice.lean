/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Relay
import Nc.Price.Norm

/-!
# The laws at the vertices of a tower, from prices

`VLaws`: the laws for one local structure (chambers Fl, near pairs Nr), the same for all towers. They exist by
Paper.thm_laws, see Paper.exists_laws.
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Nc.Price

/-- The norm of loads on pairs of chambers at a vertex. -/
noncomputable def vN2 {Fl : Type} [Fintype Fl] [DecidableEq Fl] (b : ℕ) (n : Sym2 Fl → ℕ) : ℝ :=
  ((b : ℝ) * (b - 1) / 2) * ∑ q : Sym2 Fl, if q.IsDiag then 0 else (n q : ℝ) ^ 2

/-- The laws for one local structure: chambers `Fl`, near pairs `Nr`. -/
structure VLaws (F : Type) [CommRing F] {Fl Nr : Type} [Fintype Fl] [DecidableEq Fl] [Fintype Nr]
    [DecidableEq Nr] (cN dN : Nr → Fl) (r b : ℕ) where
  /-- kinds of laws -/
  Di : Type
  [fD : Fintype Di]
  [dD : DecidableEq Di]
  /-- the laws -/
  L : Di → Law F
  /-- roles are the chambers -/
  ro : ∀ d, (L d).Ro ≃ Fl
  /-- channels are the near pairs -/
  cn : ∀ d, (L d).Cn ≃ Nr
  ends : ∀ d ν, s(ro d ((L d).c ν), ro d ((L d).d ν)) = s(cN (cn d ν), dN (cn d ν))
  lam_pos : ∀ d, 1 ≤ (L d).lam
  nonempty : ∀ d, Nonempty (L d).I
  /-- the scale -/
  a₁ : ℕ
  a₁_pos : 0 < a₁
  /-- the constant of the contraction -/
  C₁ : ℝ
  C₁_nonneg : 0 ≤ C₁
  /-- its integer form -/
  G₁ : ℕ
  G₁_le : (G₁ : ℝ) ≤ 2 * C₁ * (a₁ : ℝ) ^ 2
  /-- every load is below one of finitely many -/
  L1 : ∀ (n : Sym2 Fl → ℕ) (t : ℕ), √(vN2 b n) ≤ (a₁ : ℝ) * t → ∃ d, ∀ q : Sym2 Fl, ¬ q.IsDiag →
    n q ≤ (univ.filter fun e : (L d).Sl => s(ro d ((L d).a e), ro d ((L d).b e)) = q).card * t
  /-- the strings are short -/
  L2 : ∀ d i, r * b * ∑ ν, ((L d).lam + (L d).len i ν) ^ 2 ≤ G₁

attribute [instance] VLaws.fD VLaws.dD

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
