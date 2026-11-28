/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Fields
import Paper.ApproxScales

/-!
# The paper, appendix "Approximate computation"

Theorem thm:approx; the exact end theorems follow from it in `Solution.lean`, exact computation being
approximation without error.
-/

namespace Paper

open Finset MvPolynomial Nc Nc.Price Nc.CaseI Ov

universe u

/- VP closure, like VP with approximating circuits: the definition of the frozen statement
(`Statement.lean`), shared by the development. Its `Approximates` unfolds to `Nc.Approximates`. -/
export Statement (VPBar)

theorem coeff_mul_T {R : Type} [CommRing R] (f : LaurentPolynomial R) (N i : ℤ) :
    (f * LaurentPolynomial.T N).coeff i = f.coeff (i - N) := by
  classical
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
  | C_mul_T n a =>
    rw [LaurentPolynomial.mul_T_assoc, ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    congr 1
    exact propext ⟨fun h => by omega, fun h => by omega⟩

theorem coeff_toLaurent_natCast {R : Type} [CommRing R] (f : Polynomial R) (i : ℕ) :
    (Polynomial.toLaurent f).coeff (i : ℤ) = f.coeff i := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ i

open Ten in
/-- **Paper: Lemma lem:few-approx.** "The lemma on sums with few terms remains true if f_j has coefficients in
k[ε,ε⁻¹] and t is the part of ε⁰ of the sum, no negative powers occurring." -/
theorem lem_few_approx {K : Type} [Field K] {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (φ : Spec K V)
    (P : Finset V) (t : Ten K V) (ht : ∀ q, q ∉ P → Subsingleton (t.ι q)) {J : ℕ} [NeZero J] (T : Fin J → Ten K V)
    (f : ∀ j p, t.ι p → (T j).ι p → LaurentPolynomial K)
    (h : ∀ x (i : ℤ), i ≤ 0 →
      (∑ j, ∑ y : ∀ p, (T j).ι p, (∏ p, f j p (x p) (y p)) * LaurentPolynomial.C ((T j).val y)).coeff i =
        if i = 0 then t.val x else 0) :
    φ.F t ≤ (J : ℝ) ^ hexp φ (Subtype.val : P → V) * univ.sup' univ_nonempty fun j => φ.F (T j) := by
  classical
  choose e g hg using fun (z : Σ (j : Fin J) (p : V), t.ι p × (T j).ι p) =>
    LaurentPolynomial.exists_T_pow (f z.1 z.2.1 z.2.2.1 z.2.2.2)
  let Δ : ℕ := univ.sup e
  let L : ∀ j p, t.ι p → (T j).ι p → Polynomial K := fun j p a b =>
    g ⟨j, p, a, b⟩ * Polynomial.X ^ (Δ - e ⟨j, p, a, b⟩)
  have hL : ∀ j p a b, Polynomial.toLaurent (L j p a b) = f j p a b * LaurentPolynomial.T (Δ : ℤ) := by
    intro j p a b
    have hle : e ⟨j, p, a, b⟩ ≤ Δ := Finset.le_sup (mem_univ _)
    simp only [L, map_mul, Polynomial.toLaurent_X_pow, hg, LaurentPolynomial.mul_T_assoc]
    congr 2
    omega
  have hB : BSum (Fintype.card V * Δ) t T := by
    refine ⟨L, fun x i hi => ?_⟩
    have e1 : Polynomial.toLaurent (∑ j, ∑ y : ∀ p, (T j).ι p, (∏ p, L j p (x p) (y p)) * Polynomial.C ((T j).val y)) =
        (∑ j, ∑ y : ∀ p, (T j).ι p, (∏ p, f j p (x p) (y p)) * LaurentPolynomial.C ((T j).val y)) *
          LaurentPolynomial.T ((Fintype.card V * Δ : ℕ) : ℤ) := by
      simp only [map_sum, map_mul, map_prod, Polynomial.toLaurent_C, hL, Finset.prod_mul_distrib, Finset.prod_const,
        card_univ, LaurentPolynomial.T_pow, Finset.sum_mul, Nat.cast_mul]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [← coeff_toLaurent_natCast, e1, coeff_mul_T, h x _ (by omega)]
    by_cases hid : i = Fintype.card V * Δ
    · rw [if_pos hid, if_pos (by omega)]
    · rw [if_neg hid, if_neg (by omega)]
  have := few φ (Subtype.val : P → V) t (fun q hq => ht q fun hmem => hq ⟨⟨q, hmem⟩, rfl⟩) hB
    (M := univ.sup' univ_nonempty fun j => φ.F (T j)) (fun j => Finset.le_sup' (fun j => φ.F (T j)) (mem_univ j))
  rwa [Fintype.card_fin] at this

/-- A wire over the Laurent polynomials is the one over k. -/
theorem wire_laurent {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (n : ℕ) (p q : I)
    (y : ∀ r, (Ten.wire K n p q).ι r) :
    (Ten.wire (LaurentPolynomial K) n p q).val y =
      LaurentPolynomial.C ((Ten.wire K n p q).val y) := by
  unfold Ten.wire Ten.push Ten.unit
  dsimp only
  split_ifs <;> simp

/-- The hub tensors over the Laurent polynomials are those over k. -/
theorem hubTen_laurent {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] {k ℓ L : ℕ}
    (π : End k → I) (hub : Finset (Fin k) → Bool → I) (S : Finset (Fin k))
    (y : ∀ p, (hubTen K ℓ L π hub S).ι p) :
    (hubTen (LaurentPolynomial K) ℓ L π hub S).val y =
      LaurentPolynomial.C ((hubTen K ℓ L π hub S).val y) := by
  show (∏ a, (Ten.wire (LaurentPolynomial K) (2 ^ ℓ) (π a) (hubOf hub S a)).val
        fun p => (y p).1 a) *
      (Ten.wire (LaurentPolynomial K) L (hub S true) (hub S false)).val (fun p => (y p).2) =
    LaurentPolynomial.C ((∏ a, (Ten.wire K (2 ^ ℓ) (π a) (hubOf hub S a)).val fun p => (y p).1 a) *
      (Ten.wire K L (hub S true) (hub S false)).val fun p => (y p).2)
  rw [map_mul, map_prod]
  exact congrArg₂ (· * ·)
    (Finset.prod_congr rfl fun a _ => wire_laurent (2 ^ ℓ) (π a) (hubOf hub S a) fun p => (y p).1 a)
    (wire_laurent L (hub S true) (hub S false) fun p => (y p).2)

/-- "So Proposition prop:flat-rate holds for approximating circuits: cut the constants off, and note
that Lemma lem:balanced holds over every commutative ring." Here the constants are cut off already:
the circuit is over KK[ε,ε⁻¹], and the hub decomposition is made over that ring. -/
theorem flat_rate_approximating {K : Type} [Field K] (hK : Flat K) {k : ℕ} (hk : 2 ≤ k) {ℓ s : ℕ}
    (hℓ : 100 * √k ≤ (ℓ : ℝ)) {Q : MvPolynomial (Fin k × Ix k ℓ) (LaurentPolynomial K)}
    (hQ : Computes Q s) (hQf : ∀ (d : Fin k × Ix k ℓ →₀ ℕ) (i : ℤ), i ≤ 0 →
      (coeff d Q).coeff i = if i = 0 then coeff d (fkl K k ℓ) else 0) :
    (ℓ : ℝ) * (k * √k) / 14 ≤ Real.logb 2 s := by
  classical
  have hs : 1 ≤ s := by
    obtain ⟨l, -, a, ha, -⟩ := hQ
    omega
  refine rate_of_someSetPays hK hk hℓ hs fun φ => ?_
  have := bal_nonempty hk
  have : NeZero (Fintype.card (bal (univ : Finset (Fin k)))) := ⟨Fintype.card_ne_zero⟩
  have : Nonempty (RPt k) := ⟨hubPt ∅ true⟩
  let π : End k → RPt k := Sum.inl
  let T : Fin (Fintype.card (bal (univ : Finset (Fin k)))) → Ten K (RPt k) := fun j =>
    hubTen K ℓ s π hubPt (balEnum k j).1
  -- the hub decomposition over the Laurent polynomials: the coefficient of an entry is a sum over
  -- the balanced sets of the hub tensors over k, with functionals in k[ε,ε⁻¹]
  obtain ⟨M, hM⟩ := (prop_flat_lower_sum hk hQ π hubPt).reindex (balEnum k)
  refine someSetPays_of_few φ hs (lem_few_approx φ _ _ (fklTen_onEnds K k ℓ) T
    (fun j p a b => M j p a b) fun x i hi => ?_)
  have e : (Ten.push π (fklTen K k ℓ)).val x = cf univ (fkl K k ℓ) (tables fun a => x (π a) ⟨a, rfl⟩) :=
    fklTen_val K fun a => x (π a) ⟨a, rfl⟩
  have hx : cf univ Q (tables fun a => x (π a) ⟨a, rfl⟩) =
      ∑ j, ∑ y : ∀ p, (T j).ι p, (∏ p, M j p (x p) (y p)) * LaurentPolynomial.C ((T j).val y) :=
    (hM x).trans (Finset.sum_congr rfl fun j _ => Fintype.sum_equiv (Equiv.refl _) _ _ fun y =>
      congrArg₂ (· * ·) rfl (hubTen_laurent (K := K) π hubPt _ _))
  rw [e, ← hx]
  exact hQf (mono univ (tables fun a => x (π a) ⟨a, rfl⟩)) i hi

/-- Both cases over KK, for circuits with constants in KK[ε,ε⁻¹]. -/
theorem approx_rate_closed {K : Type} [Field K] {G : ∀ S, MvPolynomial (Fin S × Fin S) K} {κ : ℕ}
    (hG : GridComplete K G κ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, ∀ P : MvPolynomial (Fin m × Fin m) (LaurentPolynomial K), Computes P s →
      (∀ (d) (i : ℤ), i ≤ 0 → (coeff d P).coeff i = if i = 0 then coeff d (G m) else 0) →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨m₀, h⟩ : ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, Approximates (G m) s →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
    -- Theorem thm:alt: "One of the two cases occurs."
    by_cases hK : Contracting K
    · obtain ⟨C, M₁, h⟩ := contracting_approx_complete hK hG
      exact rate_of_exponents (P := fun m s => Approximates (G m) s)
        (fun _ _ _ hst ⟨Q, hQ, hQf⟩ => ⟨Q, Computes.mono hQ hst, hQf⟩) h
    -- The flat case, "… and with it Theorem thm:flat-rate".
    have hF : Flat K := fun k V _ E => thm_alt_euclidean hK (μ := k + 3) (by omega) (by omega) V E
    obtain ⟨m₀, h⟩ := rate_of_projection κ
    refine ⟨m₀, h _ fun k ℓ m s hk hℓ hℓk hm hs => ?_⟩
    -- Lemma lem:fkl-perm for a family complete for grid sums: f_{k,ℓ} is a projection of G_m with
    -- affine entries
    obtain ⟨E, hE, he⟩ := clauses_of_complete hG fklLits (fklLits_ne hk hℓ) fklLits_occ (fklWt K)
      (fun κ => Or.inl ⟨κ.1, rfl⟩) (S := m)
      (le_trans (le_trans (Nat.mul_le_mul_left _ (fklLits_count hk)) (le_of_eq (by ring))) hm)
    obtain ⟨Q, hQ, hQf⟩ := (show Approximates (fkl K k ℓ) (5 * s) from
      he.trans (lem_fkl_perm_clauseSum K k ℓ) ▸ hs.substitute_affine E hE).exists_laurentPolynomial
    refine rate_pow hk ?_ (flat_rate_approximating hF hk hℓk hQ hQf)
    obtain ⟨l, -, a, ha, -⟩ := hQ
    omega
  exact ⟨m₀, fun m hm s P hP hc => h m hm s (Approximates.of_laurentPolynomial hP hc)⟩

/-- **Paper: Theorem thm:approx.** "The theorem on all fields holds for circuits that approximate HC_m, respectively
PERM_m. In particular VNP is not contained in the closure of VP over every field." -/
theorem thm_approx :
    (∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, p = 0 ∨ p.Prime → ∃ m₀ : ℕ, ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
      (Approximates (genHC F m) s → (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) ∧
      (p ≠ 2 → Approximates (genPerm F m) s → (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s)) ∧
    ∀ (F : Type u) [Field F], ¬ VNP F ⊆ VPBar F := by
  have main : ∀ p : ℕ, p = 0 ∨ p.Prime → ∃ m₀ : ℕ, ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
      (Approximates (genHC F m) s → (m : ℝ) ^ (1 / 1600 ^ 2 * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) ∧
      (p ≠ 2 → Approximates (genPerm F m) s → (m : ℝ) ^ (1 / 1600 ^ 2 * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) := by
    intro p hp
    obtain ⟨K, _, _, _⟩ := exists_closed p hp
    obtain ⟨M₁, h1⟩ := approx_rate_closed (gridComplete_hc K)
    obtain ⟨M₂, h2⟩ : ∃ M₂ : ℕ, p ≠ 2 → ∀ m ≥ M₂, ∀ s, ∀ P : MvPolynomial (Fin m × Fin m) (LaurentPolynomial K),
        Computes P s → (∀ (d) (i : ℤ), i ≤ 0 →
          (coeff d P).coeff i = if i = 0 then coeff d (genPerm K m) else 0) →
        (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
      by_cases hne : p = 2
      · exact ⟨0, fun h => absurd hne h⟩
      · obtain ⟨M₂, h⟩ := approx_rate_closed (gridComplete_perm (two_ne_zero_of_char K p hp hne))
        exact ⟨M₂, fun _ => h⟩
    refine ⟨M₁ + M₂ + 2, fun F _ _ m hm s => ⟨fun hs => ?_, fun hne hs => ?_⟩⟩
    · rw [← map_genHC (Int.castRingHom F)] at hs
      obtain ⟨P, hP, hc⟩ := lem_transfer_approx (KK := K) p (genHC ℤ m) hs
      rw [map_genHC] at hc
      exact beyond_of_rate (by omega) (h1 m (by omega) s P hP hc)
    · rw [← map_permInt] at hs
      obtain ⟨P, hP, hc⟩ := lem_transfer_approx (KK := K) p (permInt m) hs
      rw [map_permInt] at hc
      exact beyond_of_rate (by omega) (h2 hne m (by omega) s P hP hc)
  refine ⟨⟨1 / 1600 ^ 2, by norm_num, main⟩, fun F _ h => ?_⟩
  obtain ⟨C, hC⟩ := h (hc_mem_VNP F)
  obtain ⟨p, _⟩ := CharP.exists F
  obtain ⟨m₀, hlow⟩ := main p (CharP.char_is_prime_or_zero F p).symm
  obtain ⟨m, hm1, hm2⟩ := exists_beyond_poly (show (0 : ℝ) < 1 / 1600 ^ 2 by norm_num) m₀ C
  exact hm2 ((hlow F m hm1 _).1 (hC m).2.2)

end Paper
