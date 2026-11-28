/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Defs

/-!
# Loads in a tower: one stage

The sum of the squares of the loads, times the number of chambers, falls by the factor 4 in every stage, up to a
small error. Everything is a natural number: the squares of the norms are carried, not the norms.
-/

namespace Nc.Tow

open Finset

variable {h b J : ℕ} (T : Tower h b J)

namespace Tower

/-- The units of type `i` at a chamber. -/
def be {j : ℕ} (i : Fin h) (n : T.Ed j → ℕ) (c : T.X j) : ℕ :=
  ∑ e, if T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c) then n e else 0

/-- The number of end segments on the pair `q` of the vertex `ω`. -/
def nEnd {j : ℕ} (i : Fin h) (n : T.Ed j → ℕ) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) : ℕ :=
  ∑ c : T.X j, if T.πV (T.vx i c) = ω ∧ s(T.co i (T.host i (T.vx i c)), T.co i c) = q then T.be i n c else 0

variable {T}

theorem card_V {j : ℕ} (i : Fin h) : Fintype.card (T.V j i) * b = Fintype.card (T.X j) := by
  rw [Fintype.card_of_bijective (T.vx_co i), Fintype.card_prod, T.card_fl]

theorem two_card_ed {j : ℕ} : 2 * Fintype.card (T.Ed j) = h * Fintype.card (T.X j) := by
  have h1 : Fintype.card (T.Ed j) = ∑ i : Fin h, (univ.filter fun e : T.Ed j => T.ty e = i).card := by
    rw [← card_univ]
    exact card_eq_sum_card_fiberwise (fun _ _ => mem_coe.2 (mem_univ _))
  rw [h1, Finset.mul_sum, Finset.sum_congr rfl fun i _ => T.card_ed j i]
  simp

/-- The chambers of level 0 by those of level `j`. -/
theorem card_X_pow : ∀ j ≤ J, Fintype.card (T.X 0) = b ^ j * Fintype.card (T.X j) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [ih (by omega), T.card_X j (by omega), pow_succ, mul_assoc]

/-- Cauchy–Schwarz for a sum over few elements. -/
theorem sq_sum_le {κ : Type*} (s : Finset κ) (f : κ → ℕ) {k : ℕ} (hk : s.card ≤ k) :
    (∑ x ∈ s, f x) ^ 2 ≤ k * ∑ x ∈ s, f x ^ 2 :=
  sq_sum_le_card_mul_sum_sq.trans (Nat.mul_le_mul_right _ hk)

section Stage

variable {j : ℕ} {i : Fin h} {n : T.Ed j → ℕ}

/-- Loads on middle segments. -/
theorem mid_le (hj : j < J) {n' : T.Ed (j + 1) → ℕ}
    (hmid : ∀ e', T.ty e' = i → n' e' ≤ ∑ e ∈ univ.filter (fun e => T.πE e = e'), n e) :
    ∑ e' ∈ univ.filter (fun e' => T.ty e' = i), n' e' ^ 2 ≤
      b * ∑ e ∈ univ.filter (fun e => T.ty e = i), n e ^ 2 := by
  have h1 : ∀ e' ∈ univ.filter (fun e' : T.Ed (j + 1) => T.ty e' = i), n' e' ^ 2 ≤
      b * ∑ e ∈ univ.filter (fun e => T.πE e = e'), n e ^ 2 := fun e' he' =>
    (Nat.pow_le_pow_left (hmid e' (mem_filter.1 he').2) 2).trans (sq_sum_le _ _ (T.fibre hj e'))
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  refine Nat.mul_le_mul_left _ (le_of_eq ?_)
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter fun e : T.Ed j => T.ty e = i)
    (t := univ.filter fun e' : T.Ed (j + 1) => T.ty e' = i) (g := T.πE) (f := fun e => n e ^ 2)]
  · refine Finset.sum_congr rfl fun e' he' => Finset.sum_congr ?_ fun _ _ => rfl
    ext e
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hh
      refine ⟨?_, hh⟩
      rw [← T.π_ty e, hh]
      exact (mem_filter.1 he').2
    · exact fun hh => hh.2
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he ⊢
    rw [T.π_ty e, he]

/-- Units at chambers. -/
theorem sum_be_sq : ∑ c, T.be i n c ^ 2 ≤ 2 * ∑ e ∈ univ.filter (fun e => T.ty e = i), n e ^ 2 := by
  have h1 : ∀ c, T.be i n c ^ 2 ≤
      ∑ e, if T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c) then n e ^ 2 else 0 := by
    intro c
    unfold be
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    simpa only [one_mul] using sq_sum_le _ n (T.deg j c i)
  refine (Finset.sum_le_sum fun c _ => h1 c).trans ?_
  rw [Finset.sum_comm]
  have h2 : ∀ e : T.Ed j, (∑ c, if T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c) then n e ^ 2 else 0) =
      if T.ty e = i then 2 * n e ^ 2 else 0 := by
    intro e
    by_cases ht : T.ty e = i
    · rw [if_pos ht]
      have h3 : ∀ c, (if T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c) then n e ^ 2 else 0) =
          (if T.e0 e = c then n e ^ 2 else 0) + if T.e1 e = c then n e ^ 2 else 0 := by
        intro c
        have hne := T.e_ne e
        by_cases h0 : T.e0 e = c
        · have h1 : ¬ T.e1 e = c := fun hh => hne (h0.trans hh.symm)
          simp [ht, h0, h1]
        · by_cases h1 : T.e1 e = c <;> simp [ht, h0, h1]
      rw [Finset.sum_congr rfl fun c _ => h3 c, Finset.sum_add_distrib]
      simp
      ring
    · rw [if_neg ht]
      exact Finset.sum_eq_zero fun c _ => if_neg fun hh => ht hh.1
  rw [Finset.sum_congr rfl fun e _ => h2 e, Finset.sum_filter, Finset.mul_sum]
  refine le_of_eq (Finset.sum_congr rfl fun e _ => ?_)
  split_ifs <;> ring

/-- A pair of a vertex carries the end segments of at most two chambers. -/
theorem card_two (hj : j < J) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) :
    (univ.filter fun c : T.X j => T.πV (T.vx i c) = ω ∧
      s(T.co i (T.host i (T.vx i c)), T.co i c) = q).card ≤ 2 := by
  induction q using Sym2.inductionOn with
  | _ f f' =>
    have h1 : (univ.filter fun c : T.X j => T.πV (T.vx i c) = ω ∧
        s(T.co i (T.host i (T.vx i c)), T.co i c) = s(f, f')).card ≤ ({(f, f'), (f', f)} : Finset (T.Fl × T.Fl)).card := by
      refine card_le_card_of_injOn (fun c => (T.co i (T.host i (T.vx i c)), T.co i c)) ?_ ?_
      · intro c hc
        have := (mem_filter.1 (mem_coe.1 hc)).2.2
        rw [Sym2.eq_iff] at this
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        exact this
      · intro c hc c' hc' heq
        simp only [Prod.mk.injEq] at heq
        have hv := (mem_filter.1 (mem_coe.1 hc)).2.1
        have hv' := (mem_filter.1 (mem_coe.1 hc')).2.1
        have hh : T.host i (T.vx i c) = T.host i (T.vx i c') := by
          apply (T.vx_co i).1
          simp only [Prod.mk.injEq]
          refine ⟨?_, heq.1⟩
          rw [T.host_vx hj, T.host_vx hj, hv, hv']
        have hvx := T.host_inj hj i hh
        apply (T.vx_co i).1
        simp only [Prod.mk.injEq]
        exact ⟨hvx, heq.2⟩
    exact h1.trans card_le_two

/-- Loads of end segments. -/
theorem sum_end_sq (hj : j < J) :
    ∑ ω, ∑ q : Sym2 T.Fl, T.nEnd i n ω q ^ 2 ≤ 2 * ∑ c, T.be i n c ^ 2 := by
  have h1 : ∀ ω q, T.nEnd i n ω q ^ 2 ≤ 2 * ∑ c : T.X j, if T.πV (T.vx i c) = ω ∧
      s(T.co i (T.host i (T.vx i c)), T.co i c) = q then T.be i n c ^ 2 else 0 := by
    intro ω q
    unfold nEnd
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    exact sq_sum_le _ _ (card_two hj ω q)
  refine (Finset.sum_le_sum fun ω _ => Finset.sum_le_sum fun q _ => h1 ω q).trans ?_
  simp only [← Finset.mul_sum]
  refine Nat.mul_le_mul_left _ (le_of_eq ?_)
  have e2 : ∀ ω, (∑ q : Sym2 T.Fl, ∑ c : T.X j, if T.πV (T.vx i c) = ω ∧
      s(T.co i (T.host i (T.vx i c)), T.co i c) = q then T.be i n c ^ 2 else 0) =
      ∑ c : T.X j, if T.πV (T.vx i c) = ω then T.be i n c ^ 2 else 0 := by
    intro ω
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hω : T.πV (T.vx i c) = ω
    · simp [hω]
    · simp [hω]
  rw [Finset.sum_congr rfl fun ω _ => e2 ω, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp

end Stage

/-- **One stage.** The loads `n'` of the next stage: on the edges of the chosen type `i` what the edges above
them carried (`hmid`), on the others what the laws at the vertices give for the end segments there (`hal`). -/
theorem load_step {j : ℕ} (hj : j < J) {i : Fin h}
    {n : T.Ed j → ℕ} {n' : T.Ed (j + 1) → ℕ} {C₁ E : ℕ} (hg : 4 * (1 + 8 * C₁) ≤ h)
    (hi : h * ∑ e ∈ univ.filter (fun e => T.ty e = i), n e ^ 2 ≤ ∑ e, n e ^ 2)
    (hmid : ∀ e', T.ty e' = i → n' e' ≤ ∑ e ∈ univ.filter (fun e => T.πE e = e'), n e)
    (hal : ∀ ω, b * ∑ ν, n' ((T.nr i).symm (ω, ν)).1 ^ 2 ≤
      2 * C₁ * (b ^ 2 * ∑ q, T.nEnd i n ω q ^ 2 + E)) :
    4 * (Fintype.card (T.X (j + 1)) * ∑ e', n' e' ^ 2) ≤
      Fintype.card (T.X j) * ∑ e, n e ^ 2 + 8 * C₁ * E * Fintype.card (T.X (j + 1)) ^ 2 := by
  have e1 : ∑ e' ∈ univ.filter (fun e' : T.Ed (j + 1) => ¬ T.ty e' = i), n' e' ^ 2 =
      ∑ ω, ∑ ν, n' ((T.nr i).symm (ω, ν)).1 ^ 2 := by
    rw [← Fintype.sum_prod_type' (f := fun ω ν => n' ((T.nr i).symm (ω, ν)).1 ^ 2)]
    rw [← Equiv.sum_comp (T.nr i) (fun p => n' ((T.nr i).symm p).1 ^ 2)]
    simp only [Equiv.symm_apply_apply]
    exact (Finset.sum_subtype (univ.filter fun e' : T.Ed (j + 1) => ¬ T.ty e' = i) (p := fun e' => T.ty e' ≠ i)
      (by simp) fun e' => n' e' ^ 2)
  have hm := mid_le hj hmid
  -- the end segments of all vertices are at most four times the loads of the type
  have h1 : b * ∑ ω, ∑ ν, n' ((T.nr i).symm (ω, ν)).1 ^ 2 ≤
      2 * C₁ * (b ^ 2 * (2 * (2 * ∑ e ∈ univ.filter (fun e => T.ty e = i), n e ^ 2)) +
        Fintype.card (T.V (j + 1) i) * E) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun ω _ => hal ω).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_univ, smul_eq_mul]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _
      ((sum_end_sq hj).trans (Nat.mul_le_mul_left 2 sum_be_sq))) _)
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun e' : T.Ed (j + 1) => T.ty e' = i), e1,
    T.card_X j hj, ← card_V (T := T) (j := j + 1) i]
  generalize ∑ e ∈ univ.filter (fun e => T.ty e = i), n e ^ 2 = P at hi hm h1
  generalize Fintype.card (T.V (j + 1) i) = v at h1 ⊢
  generalize ∑ e' ∈ univ.filter (fun e' => T.ty e' = i), n' e' ^ 2 = Si at hm ⊢
  generalize ∑ ω, ∑ ν, n' ((T.nr i).symm (ω, ν)).1 ^ 2 = So at h1 ⊢
  have hv : v ≤ v * b := Nat.le_mul_of_pos_right _ T.b_pos
  calc 4 * (v * b * (Si + So)) = 4 * (v * b * Si) + 4 * (v * (b * So)) := by ring
    _ ≤ 4 * (v * b * (b * P)) + 4 * (v * (2 * C₁ * (b ^ 2 * (2 * (2 * P)) + v * E))) := by gcongr
    _ = b * (v * b) * (4 * (1 + 8 * C₁) * P) + 8 * C₁ * E * v ^ 2 := by ring
    _ ≤ b * (v * b) * ∑ e, n e ^ 2 + 8 * C₁ * E * (v * b) ^ 2 := by
        gcongr
        exact (Nat.mul_le_mul_right _ hg).trans hi

end Tower

end Nc.Tow
