/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tape.Rep

/-!
# Rational series
-/


namespace Nc

open Finset Matrix

variable {F : Type*} [CommRing F] {Ω : Type*}

/-- The series is rational: it has a linear representation. -/
def Rational (f : Series F Ω) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (r : Rep F Ω Q), r.series = f

namespace Rational

theorem zero : Rational (0 : Series F Ω) :=
  ⟨Empty, inferInstance, ⟨0, 0, 0⟩, by ext o; simp [Rep.series]⟩

theorem add {f g : Series F Ω} (hf : Rational f) (hg : Rational g) : Rational (f + g) := by
  obtain ⟨Q₁, _, r₁, rfl⟩ := hf
  obtain ⟨Q₂, _, r₂, rfl⟩ := hg
  refine ⟨Q₁ ⊕ Q₂, inferInstance, r₁.add r₂, ?_⟩
  ext o
  exact Rep.add_series r₁ r₂ o

theorem mul {f g : Series F Ω} (hf : Rational f) (hg : Rational g) :
    Rational (Series.mul f g) := by
  obtain ⟨Q₁, _, r₁, rfl⟩ := hf
  obtain ⟨Q₂, _, r₂, rfl⟩ := hg
  refine ⟨Q₁ ⊕ Q₂, inferInstance, r₁.mul r₂, ?_⟩
  ext o
  exact Rep.mul_series r₁ r₂ o

theorem kstar {f : Series F Ω} (hf : Rational f) : Rational (Series.kstar f) := by
  obtain ⟨Q₁, _, r₁, rfl⟩ := hf
  refine ⟨Unit ⊕ Q₁, inferInstance, r₁.star, ?_⟩
  ext o
  exact Rep.star_series r₁ o

theorem smul {f : Series F Ω} (c : F) (hf : Rational f) : Rational (c • f) := by
  obtain ⟨Q, _, r, rfl⟩ := hf
  refine ⟨Q, inferInstance, ⟨c • r.lam, r.mu, r.gam⟩, ?_⟩
  ext o
  have : ∀ o, (⟨c • r.lam, r.mu, r.gam⟩ : Rep F Ω Q).tail o = r.tail o := by
    intro o
    induction o with
    | nil => rfl
    | cons a o ih => simp [Rep.tail, ih]
  simp [Rep.series, this]

theorem one : Rational (Series.one : Series F Ω) := by
  refine ⟨Unit, inferInstance, ⟨1, 0, 1⟩, ?_⟩
  ext o
  cases o with
  | nil => simp [Rep.series, Rep.tail, Series.one, dotProduct]
  | cons a o => simp [Rep.series, Rep.tail, Series.one]

theorem sum {ι : Type*} (s : Finset ι) (f : ι → Series F Ω) (h : ∀ i ∈ s, Rational (f i)) :
    Rational (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Rational

/-- The series of one letter. -/
def Series.letter [DecidableEq Ω] (a : Ω) : Series F Ω := fun o => if o = [a] then 1 else 0

theorem Rational.letter [DecidableEq Ω] (a : Ω) : Rational (Series.letter a : Series F Ω) := by
  refine ⟨Bool, inferInstance, ⟨fun q => if q then 0 else 1,
    fun b => Matrix.of fun q q' => if b = a ∧ q = false ∧ q' = true then 1 else 0,
    fun q => if q then 1 else 0⟩, ?_⟩
  ext o
  match o with
  | [] => simp [Rep.series, Rep.tail, Series.letter, dotProduct]
  | [b] =>
    by_cases h : b = a <;> simp [Rep.series, Rep.tail, Series.letter, dotProduct, Matrix.mulVec, h]
  | b :: c :: o =>
    simp [Rep.series, Rep.tail, Series.letter, dotProduct, Matrix.mulVec]

/-- Normal form: one initial and one final state; the same values at non-empty words. -/
theorem Rational.normal {f : Series F Ω} (hf : Rational f) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (mu : Ω → Matrix Q Q F) (i e : Q),
      ∀ o : List Ω, o ≠ [] → (o.map mu).prod i e = f o := by
  classical
  obtain ⟨Q, _, r, rfl⟩ := hf
  let mu : Ω → Matrix (Option (Option Q)) (Option (Option Q)) F := fun a => Matrix.of fun q q' =>
    match q, q' with
    | none, none => 0
    | none, some none => r.lam ⬝ᵥ (r.mu a *ᵥ r.gam)
    | none, some (some q') => (r.lam ᵥ* r.mu a) q'
    | some none, _ => 0
    | some (some _), none => 0
    | some (some q), some none => (r.mu a *ᵥ r.gam) q
    | some (some q), some (some q') => r.mu a q q'
  refine ⟨Option (Option Q), inferInstance, inferInstance, mu, none, some none, ?_⟩
  have key : ∀ o : List Ω, ∀ q, o ≠ [] → (o.map mu).prod (some (some q)) (some none) = r.tail o q := by
    intro o
    induction o with
    | nil => simp
    | cons a o ih =>
      intro q _
      rw [List.map_cons, List.prod_cons, Matrix.mul_apply, Fintype.sum_option, Fintype.sum_option]
      by_cases ho : o = []
      · subst ho
        simp [mu, Rep.tail]
      · have h0 : (o.map mu).prod (some none) (some none) = 0 := by
          obtain ⟨b, o', rfl⟩ := List.exists_cons_of_ne_nil ho
          rw [List.map_cons, List.prod_cons, Matrix.mul_apply]
          simp [mu]
        simp only [mu, Matrix.of_apply, zero_mul, zero_add] at *
        rw [h0, mul_zero, zero_add, Rep.tail, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun q' _ => by rw [ih q' ho]
  intro o ho
  obtain ⟨a, o, rfl⟩ := List.exists_cons_of_ne_nil ho
  rw [List.map_cons, List.prod_cons, Matrix.mul_apply, Fintype.sum_option, Fintype.sum_option]
  by_cases ho : o = []
  · subst ho
    simp [mu, Rep.series, Rep.tail]
  · have h0 : (o.map mu).prod (some none) (some none) = 0 := by
      obtain ⟨b, o', rfl⟩ := List.exists_cons_of_ne_nil ho
      rw [List.map_cons, List.prod_cons, Matrix.mul_apply]
      simp [mu]
    rw [Finset.sum_congr rfl fun q' _ => by rw [key o q' ho]]
    simp only [mu, Matrix.of_apply, zero_mul, zero_add] at *
    rw [h0, mul_zero, zero_add, Rep.series, Rep.tail, Matrix.dotProduct_mulVec]
    rfl

end Nc
