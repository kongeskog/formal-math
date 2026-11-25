/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Rate.Defs

/-!
# The paper, section "Tensors, prices and duality": tensors

The subsection "Tensors". One theorem for every numbered statement, in the order of the paper and named by its label, and
one for every step of the running text that is used later. Tensors are arrays over a field K with one finite index set for
each party (Ov.Ten); tensors that are restrictions of one another (Ov.Ten.Equi) are not identified, instead a spectral point
has the same value on them (def_spectral_congr). The other subsections are in Paper/Gauges.lean, Paper/Extension.lean and
Paper/Prices.lean.
-/

namespace Paper

open Ov Ov.Ten Nc.Price Finset

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-! ## Tensors -/

section Tensors

variable {J L : Type} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- "Every nonzero t has 1 as a restriction". -/
theorem tensor_one_restr [Nonempty I] {t : Ten K I} (ht : ∃ x, t.val x ≠ 0) : Restr 1 t :=
  Restr.one_le ht.choose_spec

/-- "Every t is covered by finitely many copies of 1." -/
theorem tensor_covered_by_ones [Nonempty I] (t : Ten K I) : ∃ r : ℕ, SumRestr t fun _ : Fin r => (1 : Ten K I) :=
  ⟨_, (rankLE_card t).sumRestr⟩

/-- "Push-forward commutes with products". -/
theorem tensor_push_mul (π : J → I) (s t : Ten K J) : Equi (Ten.push π (s * t)) (Ten.push π s * Ten.push π t) :=
  Equi.push_mul π s t

/-- "Push-forward commutes with … compositions". -/
theorem tensor_push_comp (π : J → I) (ρ : L → J) (t : Ten K L) :
    Equi (Ten.push π (Ten.push ρ t)) (Ten.push (π ∘ ρ) t) :=
  Equi.push_push π ρ t

/-- "Push-forward … sends 1 to 1". -/
theorem tensor_push_one (π : J → I) : Equi (Ten.push π (1 : Ten K J)) 1 := Equi.push_one π

end Tensors

/-- The text after the definition: "So φ(t) ≥ 1 if t ≠ 0". -/
theorem def_spectral_values [Nonempty I] (φ : Spec K I) (t : Ten K I) : (∃ x, t.val x ≠ 0) → 1 ≤ φ.F t :=
  fun ⟨_, hx⟩ => φ.one_le hx

/-- Tensors that are restrictions of each other are identified: a spectral point is monotone under restriction, so it has
the same value on them. -/
theorem def_spectral_congr (φ : Spec K I) {s t : Ten K I} :
    (Restr s t → φ.F s ≤ φ.F t) ∧ (Equi s t → φ.F s = φ.F t) :=
  ⟨φ.mono, φ.congr⟩

open Classical in
/-- The first example after Definition def:spectral: "An example is φ(t) = 1 for all t ≠ 0". -/
noncomputable def trivialPoint (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] : Spec K I where
  F t := if ∃ x, t.val x ≠ 0 then 1 else 0
  nonneg t := by split_ifs <;> norm_num
  one := if_pos ⟨fun _ => (), one_ne_zero⟩
  mul s t := by
    by_cases hs : ∃ x, s.val x ≠ 0
    · by_cases ht : ∃ x, t.val x ≠ 0
      · rw [if_pos hs, if_pos ht, if_pos, mul_one]
        obtain ⟨x, hx⟩ := hs
        obtain ⟨y, hy⟩ := ht
        exact ⟨fun p => (x p, y p), mul_ne_zero hx hy⟩
      · rw [if_neg ht, mul_zero, if_neg]
        rintro ⟨x, hx⟩
        exact ht ⟨fun p => (x p).2, right_ne_zero_of_mul hx⟩
    · rw [if_neg hs, zero_mul, if_neg]
      rintro ⟨x, hx⟩
      exact hs ⟨fun p => (x p).1, left_ne_zero_of_mul hx⟩
  le_sum {κ} _ s b h := by
    by_cases hs : ∃ x, s.val x ≠ 0
    · rw [if_pos hs]
      obtain ⟨x, hx⟩ := hs
      obtain ⟨L, hL⟩ := h
      rw [hL] at hx
      obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
      have h1 : ∃ x, (b k).val x ≠ 0 := ⟨y, right_ne_zero_of_mul hy⟩
      calc (1 : ℝ) = if ∃ x, (b k).val x ≠ 0 then 1 else 0 := (if_pos h1).symm
        _ ≤ _ := Finset.single_le_sum
          (f := fun k => if ∃ x, (b k).val x ≠ 0 then (1 : ℝ) else 0)
          (fun k _ => by split_ifs <;> norm_num) (Finset.mem_univ k)
    · rw [if_neg hs]
      exact Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num

/-- Proof of Lemma lem:exponents: "The function q ↦ φ(⟨q⟩_P) is at least 1, multiplicative and monotone, hence a power of q."
The unit tensor has a leg at π a for every a; the exponent is Nc.Price.hexp. -/
theorem lem_exponents_power [Nonempty I] (φ : Spec K I) {A : Type} [Fintype A] [DecidableEq A] (π : A → I) :
    0 ≤ hexp φ π ∧ ∀ q : ℕ, 1 ≤ q → φ.F (Ten.push π (Ten.unit K A q)) = (q : ℝ) ^ hexp φ π :=
  ⟨Real.logb_nonneg (by norm_num) (φ.one_le_unit π (by norm_num)), fun _ hq =>
    eq_rpow_of_mul_mono (fun n => φ.F (Ten.push π (Ten.unit K A n))) (fun _ h => φ.one_le_unit π h)
      (fun m n _ _ => by
        rw [(def_spectral_congr φ).2 ((Equi.unit_mul m n).push π), (def_spectral_congr φ).2 (tensor_push_mul _ _ _), φ.mul])
      (fun _ _ _ h => (def_spectral_congr φ).1 ((Restr.unit_mono h).push π)) _ hq⟩

/-- The case of a wire: φ(⟨n⟩_uv) = n ^ d_φ(u,v). Stated in the namespace Ov.Spec, so that the development cites it as
`φ.wire_eq`; so are the facts about wires below. -/
theorem _root_.Ov.Spec.wire_eq (φ : Spec K I) (u v : I) {n : ℕ} (hn : 1 ≤ n) :
    φ.F (Ten.wire K n u v) = (n : ℝ) ^ φ.e u v :=
  have : Nonempty I := ⟨u⟩
  (lem_exponents_power φ ![u, v]).2 n hn

/-- φ(⟨2⟩_uv) = 2 ^ d_φ(u,v). -/
theorem _root_.Ov.Spec.wire_two (φ : Spec K I) (u v : I) : φ.F (Ten.wire K 2 u v) = 2 ^ φ.e u v := by
  have := φ.wire_eq u v (n := 2) (by norm_num)
  exact_mod_cast this

/-- Proof of Lemma lem:exponents: "A wire of dimension q is covered by q copies of 1, so d_φ ≤ 1." (The cover and its
consequence φ(⟨q⟩_uv) ≤ q are Ov.Spec.unit_le.) Also d_φ ≥ 0, as for every exponent. -/
theorem lem_exponents_unit_interval (φ : Spec K I) (u v : I) : 0 ≤ φ.e u v ∧ φ.e u v ≤ 1 := by
  have : Nonempty I := ⟨u⟩
  refine ⟨(lem_exponents_power φ ![u, v]).1, ?_⟩
  have h : φ.F (Ten.wire K 2 u v) ≤ (2 : ℕ) := φ.unit_le ![u, v] 2
  rw [Spec.wire_two] at h
  have h2 : (2 : ℝ) ^ φ.e u v ≤ 2 ^ (1 : ℝ) := by simpa using h
  exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h2

/-- "We put ⟨q⟩_uu = 1": a wire from u to u is a restriction of 1, so d_φ(u,u) = 0. -/
theorem _root_.Ov.Spec.e_self (φ : Spec K I) (u : I) : φ.e u u = 0 := by
  have : Nonempty I := ⟨u⟩
  have h : φ.F (Ten.wire K 2 u u) = 1 := by
    refine le_antisymm ?_ (φ.one_le_unit ![u, u] (by norm_num))
    rw [← φ.one]
    exact (def_spectral_congr φ).1 (Restr.wire_self 2 u)
  rw [Spec.e, h, Real.logb_one]

/-- A wire has no direction. -/
theorem _root_.Ov.Spec.e_comm (φ : Spec K I) (u v : I) : φ.e u v = φ.e v u := by
  rw [Spec.e, Spec.e, (def_spectral_congr φ).2 (Equi.wire_comm 2 u v)]

/-- Proof of Lemma lem:exponents: "Contracting the two indices at v shows that ⟨q⟩_uw is a restriction of ⟨q⟩_uv ⟨q⟩_vw". -/
theorem lem_exponents_contract (q : ℕ) (u v w : I) :
    Restr (Ten.wire K q u w) (Ten.wire K q u v * Ten.wire K q v w) :=
  Restr.wire_trans q u w v

/-- Proof of Lemma lem:exponents: "… this is the triangle inequality." -/
theorem lem_exponents_triangle (φ : Spec K I) (u v w : I) : φ.e u w ≤ φ.e u v + φ.e v w := by
  have h := φ.le_mul (lem_exponents_contract (K := K) 2 u v w)
  rw [Spec.wire_two, Spec.wire_two, Spec.wire_two, ← Real.rpow_add (by norm_num)] at h
  exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h

end Paper
