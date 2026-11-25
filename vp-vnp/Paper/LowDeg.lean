/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Acc.Main
import Nc.Final.CClasses

/-!
# The paper, section "One scale is all scales": low degree is fast
-/

namespace Paper

open Finset NS1
open _root_.NS1.Tree

open Nc.Acc in
/-- The part of degree i is what the point scales by the ith power. -/
theorem line_coeff_eq {R σ : Type} [CommRing R] (u : σ → R) (p : MvPolynomial σ R) (i : ℕ) :
    (line u p).coeff i = MvPolynomial.eval u (MvPolynomial.homogeneousComponent i p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).2
      (MvPolynomial.isHomogeneous_monomial a rfl : (MvPolynomial.monomial d a).IsHomogeneous d.degree))]
    have e : line u (MvPolynomial.monomial d a) =
        Polynomial.C (MvPolynomial.eval u (MvPolynomial.monomial d a)) * Polynomial.X ^ d.degree := by
      simp only [line, MvPolynomial.aeval_monomial, MvPolynomial.eval_monomial, Finsupp.prod, mul_pow,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_eq]
      simp [Finsupp.degree, mul_assoc]
      rfl
    rw [e, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp
  | add p q hp hq => simp [map_add, hp, hq]

end Paper
