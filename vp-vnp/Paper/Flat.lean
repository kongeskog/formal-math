/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Alternative
import Paper.Grids
import Nc.CaseI.Lower

/-!
# The paper, section "The flat case"
-/

namespace Paper

open Finset MvPolynomial Nc Nc.Price Nc.CaseI Ov

/-! ### The polynomial of the complete network -/

/-- The other end of a pair. -/
def pairOf {k : ℕ} (a b : Fin k) (h : b ≠ a) : Pr k :=
  if hab : a < b then ⟨(a, b), hab⟩ else ⟨(b, a), lt_of_le_of_ne (not_lt.1 hab) h⟩

theorem asm_pairOf {k ℓ : ℕ} (σ : Pr k → Fin ℓ → Bool) (a b : Fin k) (h : b ≠ a) :
    asm (fun e _ => σ e) a b = σ (pairOf a b h) := by
  unfold asm pairOf
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact absurd (le_antisymm (not_lt.1 h1) (not_lt.1 h2)) h

theorem asm_self {k ℓ : ℕ} (σ : Pr k → Fin ℓ → Bool) (a : Fin k) :
    asm (fun e _ => σ e) a a = fun _ => false := by
  simp [asm]

/-- A value of σ_a: a table with no string for a itself. -/
abbrev Val (k ℓ : ℕ) := {κ : Fin k × Ix k ℓ // κ.2 κ.1 = fun _ => false}

/-- The literals of the clause σ_a = ρ. -/
noncomputable def fklLits {k ℓ : ℕ} (κ : Val k ℓ) : List ((Pr k × Fin ℓ) × Bool) :=
  (univ : Finset ({b : Fin k // b ≠ κ.1.1} × Fin ℓ)).toList.map fun p =>
    ((pairOf κ.1.1 p.1.1 p.1.2, p.2), κ.1.2 p.1.1 p.2)

/-- The weight x_{a,ρ} of the clause σ_a = ρ. -/
noncomputable def fklWt (F : Type) [Field F] {k ℓ : ℕ} (κ : Val k ℓ) : MvPolynomial (Fin k × Ix k ℓ) F := X κ.1

theorem forall_fklLits {k ℓ : ℕ} (κ : Val k ℓ) (x : Pr k × Fin ℓ → Bool) :
    (∀ l ∈ fklLits κ, x l.1 = l.2) ↔ asm (fun e _ i => x (e, i)) κ.1.1 = κ.1.2 := by
  obtain ⟨⟨a, t⟩, ht⟩ := κ
  constructor
  · intro h
    funext b
    by_cases hb : b = a
    · subst hb
      exact (asm_self (fun e i => x (e, i)) b).trans ht.symm
    · refine (asm_pairOf (fun e i => x (e, i)) a b hb).trans (funext fun i => ?_)
      exact h ((pairOf a b hb, i), t b i) (List.mem_map.2 ⟨(⟨b, hb⟩, i), by simp, rfl⟩)
  · intro h l hl
    obtain ⟨⟨⟨b, hb⟩, i⟩, -, rfl⟩ := List.mem_map.1 hl
    show x (pairOf a b hb, i) = t b i
    exact (congrFun (asm_pairOf (fun e i => x (e, i)) a b hb) i).symm.trans
      (congrFun (congrFun (h : asm (fun e _ i => x (e, i)) a = t) b) i)

/-- "It is the clause sum over the bits of σ in which, for every a and every value ρ of σ_a, the clause saying σ_a = ρ
has the weight x_{a,ρ}." -/
theorem lem_fkl_perm_clauseSum (F : Type) [Field F] (k ℓ : ℕ) :
    clauseSum (fklLits (k := k) (ℓ := ℓ)) (fklWt F) = fkl F k ℓ := by
  classical
  unfold clauseSum fkl
  refine Fintype.sum_equiv (Equiv.curry (Pr k) (Fin ℓ) Bool) _ _ fun x => ?_
  simp only [forall_fklLits, fklWt]
  rw [← Finset.prod_filter]
  refine Finset.prod_bij' (fun κ _ => κ.1.1)
    (fun a _ => ⟨(a, asm (fun e _ i => x (e, i)) a), asm_self (fun e i => x (e, i)) a⟩) ?_ ?_ ?_ ?_ ?_
  · intros
    exact mem_univ _
  · intro a _
    exact mem_filter.2 ⟨mem_univ _, rfl⟩
  · intro κ hκ
    exact Subtype.ext (Prod.ext rfl (mem_filter.1 hκ).2)
  · intros
    rfl
  · intro κ hκ
    exact congrArg X (Prod.ext rfl (mem_filter.1 hκ).2.symm)

theorem fklLits_ne {k ℓ : ℕ} (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) (κ : Val k ℓ) : fklLits κ ≠ [] := by
  have h1 : Fintype.card {b : Fin k // b ≠ κ.1.1} = k - 1 := by simp
  have h2 : 0 < (fklLits κ).length := by
    simp only [fklLits, List.length_map, Finset.length_toList, card_univ, Fintype.card_prod, h1, Fintype.card_fin]
    exact Nat.mul_pos (by omega) (by omega)
  exact List.length_pos_iff.1 h2

theorem fklLits_occ {k ℓ : ℕ} (b : Pr k × Fin ℓ) : ∃ κ : Val k ℓ, ∃ l ∈ fklLits κ, l.1 = b := by
  obtain ⟨⟨⟨a, c⟩, hac⟩, i⟩ := b
  refine ⟨⟨(a, fun _ _ => false), rfl⟩, ((pairOf a c (ne_of_gt hac), i), false),
    List.mem_map.2 ⟨(⟨c, ne_of_gt hac⟩, i), by simp, rfl⟩, ?_⟩
  simp only [pairOf, dif_pos (show a < c from hac)]

theorem fklLits_count {k ℓ : ℕ} (hk : 2 ≤ k) : ∑ κ : Val k ℓ, (fklLits κ).length ≤ k ^ 3 * ℓ * 2 ^ (k * ℓ) := by
  have h1 : ∀ κ : Val k ℓ, (fklLits κ).length ≤ k * ℓ := fun κ => by
    simp only [fklLits, List.length_map, Finset.length_toList, card_univ, Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ ((Fintype.card_subtype_le _).trans_eq (Fintype.card_fin k))
  have h2 : Fintype.card (Val k ℓ) ≤ k * 2 ^ (k * ℓ) := by
    refine (Fintype.card_subtype_le _).trans (le_of_eq ?_)
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [← pow_mul, mul_comm ℓ k]
  calc ∑ κ : Val k ℓ, (fklLits κ).length ≤ ∑ _κ : Val k ℓ, k * ℓ := Finset.sum_le_sum fun κ _ => h1 κ
    _ = Fintype.card (Val k ℓ) * (k * ℓ) := by rw [sum_const, card_univ, smul_eq_mul]
    _ ≤ k * 2 ^ (k * ℓ) * (k * ℓ) := Nat.mul_le_mul_right _ h2
    _ = k ^ 2 * ℓ * 2 ^ (k * ℓ) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega)))

/-- The form of Lemma lem:fkl-perm for every family that is complete for grid sums: if M ≥ κk³ℓ2^(kℓ), then f_{k,ℓ} is a
projection of G_M with affine entries. -/
theorem fkl_complete {F : Type} [Field F] {G : ∀ M, MvPolynomial (Fin M × Fin M) F} {κ : ℕ}
    (hG : GridComplete F G κ) {k ℓ : ℕ} (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) {M : ℕ}
    (hM : κ * k ^ 3 * ℓ * 2 ^ (k * ℓ) ≤ M) :
    ∃ E : Fin M × Fin M → MvPolynomial (Fin k × Ix k ℓ) F, (∀ q, IsAffine (E q)) ∧ aeval E (G M) = fkl F k ℓ := by
  obtain ⟨E, hE, he⟩ := clauses_of_complete hG fklLits (fklLits_ne hk hℓ) fklLits_occ (fklWt F)
    (fun κ => Or.inl ⟨κ.1, rfl⟩) (S := M) (le_trans (le_trans (Nat.mul_le_mul_left _ (fklLits_count hk))
      (le_of_eq (by ring))) hM)
  exact ⟨E, hE, he.trans (lem_fkl_perm_clauseSum F k ℓ)⟩

/-! ### Balanced products -/

/-- A polynomial that is linear in each block of S and contains no other variables, by its coefficients. -/
noncomputable def linearIn {R T : Type} [CommSemiring R] [Fintype T] {k : ℕ} (S : Finset (Fin k))
    (c : (S → T) → R) : MvPolynomial (Fin k × T) R :=
  ∑ y : S → T, C (c y) * ∏ a : S, X ((a : Fin k), y a)

/-- The part of a polynomial that is linear in each block. -/
noncomputable def linearPart {R T : Type} [CommSemiring R] [Fintype T] [DecidableEq T] {k : ℕ}
    (P : MvPolynomial (Fin k × T) R) : MvPolynomial (Fin k × T) R :=
  ∑ x : Fin k → T, C (cf univ P x) * ∏ a, X (a, x a)

theorem linearPart_cf {R T : Type} [CommSemiring R] [Fintype T] [DecidableEq T] {k : ℕ}
    (c : (Fin k → T) → R) (y : Fin k → T) :
    cf univ (∑ x : Fin k → T, C (c x) * ∏ a, X (a, x a)) y = c y := by
  classical
  have e : ∀ x : Fin k → T, (∏ a, X (a, x a) : MvPolynomial (Fin k × T) R) = monomial (mono univ x) 1 := fun x => by
    rw [mono, monomial_sum_one]
    rfl
  rw [cf, coeff_sum, Finset.sum_eq_single y]
  · rw [e, coeff_C_mul, coeff_monomial, if_pos rfl, mul_one]
  · intro x _ hx
    rw [e, coeff_C_mul, coeff_monomial, if_neg, mul_zero]
    intro h
    refine hx (funext fun a => ?_)
    have h1 := DFunLike.congr_fun h (a, x a)
    rw [mono_apply, mono_apply, if_pos ⟨mem_univ _, rfl⟩] at h1
    by_contra hne
    rw [if_neg fun h2 => hne h2.2.symm] at h1
    exact one_ne_zero' _ h1
  · exact fun h => absurd (mem_univ _) h

/-- A product gh, g linear in each block of S and h in each other block, by its coefficients. -/
theorem linearIn_mul {R T : Type} [CommSemiring R] [Fintype T] [DecidableEq T] {k : ℕ} (S : Finset (Fin k))
    (g : (S → T) → R) (h : ((Sᶜ : Finset (Fin k)) → T) → R) :
    linearIn S g * linearIn Sᶜ h =
      ∑ x : Fin k → T, C (g (fun a => x a) * h fun a => x a) * ∏ a, X (a, x a) := by
  classical
  rw [linearIn, linearIn, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine (Finset.sum_bij' (fun x _ => ((fun a : S => x a), fun a : (Sᶜ : Finset (Fin k)) => x a))
    (fun p _ a => if ha : a ∈ S then p.1 ⟨a, ha⟩ else p.2 ⟨a, mem_compl.2 ha⟩) (fun _ _ => mem_univ _)
    (fun _ _ => mem_univ _) (fun x _ => ?_) (fun p _ => ?_) (fun x _ => ?_)).symm
  · funext a
    by_cases ha : a ∈ S <;> simp [ha]
  · refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
    · simp [a.2]
    · simp [mem_compl.1 a.2]
  · simp only [map_mul]
    rw [← Finset.prod_mul_prod_compl S fun a => (X (a, x a) : MvPolynomial (Fin k × T) R),
      ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort Sᶜ]
    ring

/-- **Paper: Lemma lem:balanced.** "If a polynomial has a circuit with L gates, its part f that is linear in each of
k ≥ 2 blocks of variables of equal size is a sum of products gh: for every set S with k ≤ 3|S| ≤ 2k at most L products
in which g is linear in each block of S, h in each other block, and neither contains other variables." The blocks are
{a} × T, and R is any commutative semiring, so it holds for approximating circuits too. -/
theorem lem_balanced {R T : Type} [CommSemiring R] [Fintype T] [DecidableEq T] {k : ℕ}
    {P : MvPolynomial (Fin k × T) R} {L : ℕ} (h : Computes P L) (hk : 2 ≤ k) :
    ∃ (g : ∀ S : Finset (Fin k), Fin L → (S → T) → R) (q : ∀ S : Finset (Fin k), Fin L → ((Sᶜ : Finset (Fin k)) → T) → R),
      linearPart P = ∑ S ∈ (univ : Finset (Finset (Fin k))).filter (fun S => k ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * k),
        ∑ δ, linearIn S (g S δ) * linearIn Sᶜ (q S δ) := by
  classical
  obtain ⟨l, hl, γ, hγ, rfl⟩ := h
  -- the induction on the circuit, for the output and all blocks
  obtain ⟨q, hq, he⟩ := dec_gate hl hk γ hγ univ (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  rcases isEmpty_or_nonempty T with hT | hT
  · have : IsEmpty (Fin k → T) := ⟨fun x => hT.false (x ⟨0, by omega⟩)⟩
    refine ⟨fun _ _ _ => 0, fun _ _ _ => 0, ?_⟩
    simp [linearPart, linearIn]
  let t₀ : T := Classical.arbitrary T
  let ext : ∀ S : Finset (Fin k), (S → T) → Fin k → T := fun S y a => if ha : a ∈ S then y ⟨a, ha⟩ else t₀
  refine ⟨fun S δ y => cf S (l δ) (ext S y), fun S δ z => q δ S (ext Sᶜ z), ?_⟩
  have hbal : bal (univ : Finset (Fin k)) = univ.filter fun S => k ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * k := by
    ext S
    simp [mem_bal]
  rw [← hbal]
  simp only [linearIn_mul]
  have e1 : ∀ S δ (x : Fin k → T), cf S (l δ) (ext S fun a : S => x a) = cf S (l δ) x := fun S δ x =>
    cf_congr _ fun a ha => by simp [ext, ha]
  have e2 : ∀ S δ (x : Fin k → T), q δ S (ext Sᶜ fun a : (Sᶜ : Finset (Fin k)) => x a) = q δ S x := fun S δ x =>
    hq δ S _ _ fun a ha => by simp [ext, (Finset.mem_sdiff.1 ha).2]
  simp only [e1, e2]
  simp only [linearPart, he, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_comm (s := bal _)]
  exact Finset.sum_congr rfl fun δ _ => Finset.sum_comm

/-- Lemma lem:balanced for the coefficients: the coefficient of ∏ x_{a,y_a} is a sum of products. -/
theorem lem_balanced_cf {R T : Type} [CommSemiring R] [Fintype T] [DecidableEq T] {k : ℕ}
    {P : MvPolynomial (Fin k × T) R} {L : ℕ} (h : Computes P L) (hk : 2 ≤ k) :
    ∃ (g : ∀ S : Finset (Fin k), Fin L → (S → T) → R)
      (q : ∀ S : Finset (Fin k), Fin L → ((Sᶜ : Finset (Fin k)) → T) → R),
      ∀ y, cf univ P y = ∑ S ∈ bal univ, ∑ δ, g S δ (fun a => y a) * q S δ fun a => y a := by
  obtain ⟨g, q, he⟩ := lem_balanced h hk
  refine ⟨g, q, fun y => ?_⟩
  have hbal : bal (univ : Finset (Fin k)) = univ.filter fun S => k ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * k := by
    ext S
    simp [mem_bal]
  rw [← linearPart_cf (fun x => cf univ P x) y, show (∑ x : Fin k → T, C (cf univ P x) * ∏ a, X (a, x a)) =
    linearPart P from rfl, he, ← hbal, cf, coeff_sum]
  simp only [linearIn_mul, coeff_sum]
  exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun δ _ => by
    rw [← coeff_sum]; exact linearPart_cf _ y

/-! ### The tensor of f_{k,ℓ} -/

/-- The numbers below 2^ℓ are the strings of ℓ bits. -/
noncomputable def strEquiv (ℓ : ℕ) : Fin (2 ^ ℓ) ≃ (Fin ℓ → Bool) :=
  (Fintype.equivFinOfCardEq (by simp)).symm

/-- The tensor of f_{k,ℓ} on the ends: the product of the wires of dimension 2^ℓ on the pairs. -/
noncomputable def fklTen (K : Type) [Field K] (k ℓ : ℕ) : Ten K (End k) :=
  Ten.outer fun _ : Pr k => Ten.unit K (Fin 2) (2 ^ ℓ)

/-- The strings at the tables for an entry of the tensor. -/
noncomputable def tables {k ℓ : ℕ} (z : End k → Fin (2 ^ ℓ)) : Fin k → Ix k ℓ :=
  asm fun e i => strEquiv ℓ (z ⟨e, i⟩)

/-- "As a tensor on the ends it is the product of the wires on the pairs." -/
theorem fklTen_val (K : Type) [Field K] {k ℓ : ℕ} (z : End k → Fin (2 ^ ℓ)) :
    (fklTen K k ℓ).val z = cf univ (fkl K k ℓ) (tables z) := by
  rw [tables, cf_fkl]
  refine (Ten.outer_val (fun _ : Pr k => Ten.unit K (Fin 2) (2 ^ ℓ)) z).trans ?_
  rw [
    Finset.prod_congr rfl fun e _ => unit_two_val' (strEquiv ℓ) fun i => z ⟨e, i⟩, Finset.prod_ite_zero]
  simp

theorem fklTen_price {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (φ : Spec K I) {k : ℕ} (ℓ : ℕ)
    (π : End k → I) :
    φ.F (Ten.push π (fklTen K k ℓ)) = (2 : ℝ) ^ ((ℓ : ℝ) * ∑ e : Pr k, φ.e (π ⟨e, 0⟩) (π ⟨e, 1⟩)) := by
  rw [fklTen, φ.congr (Ten.Equi.push_outer π _), φ.prod, Finset.mul_sum, Real.rpow_sum_of_pos (by norm_num)]
  refine Finset.prod_congr rfl fun e _ => ?_
  have : (fun i => π ⟨e, i⟩) = ![π ⟨e, 0⟩, π ⟨e, 1⟩] := by
    funext i
    fin_cases i <;> rfl
  rw [this, show Ten.push ![π ⟨e, 0⟩, π ⟨e, 1⟩] (Ten.unit K (Fin 2) (2 ^ ℓ)) =
    Ten.wire K (2 ^ ℓ) (π ⟨e, 0⟩) (π ⟨e, 1⟩) from rfl, φ.wire_eq _ _ Nat.one_le_two_pow,
    Real.rpow_mul (by norm_num)]
  simp

/-- The hub of an end for the set S. -/
def hubOf {I : Type} {k : ℕ} (hub : Finset (Fin k) → Bool → I) (S : Finset (Fin k)) (a : End k) : I :=
  hub S (decide (endNode a.1 a.2 ∈ S))

/-- The product of the wires from the ends to their hubs for S and a wire of dimension L between the hubs. -/
noncomputable def hubTen (K : Type) [Field K] {I : Type} [Fintype I] [DecidableEq I] {k : ℕ} (ℓ L : ℕ)
    (π : End k → I) (hub : Finset (Fin k) → Bool → I) (S : Finset (Fin k)) : Ten K I :=
  Ten.prod (fun a => Ten.wire K (2 ^ ℓ) (π a) (hubOf hub S a)) * Ten.wire K L (hub S true) (hub S false)

/-- What the set S costs: ℓ times the wires from the ends to their hubs, and the wire between the hubs. -/
noncomputable def hubCost {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (φ : Spec K I) {k : ℕ} (ℓ L : ℕ)
    (π : End k → I) (hub : Finset (Fin k) → Bool → I) (S : Finset (Fin k)) : ℝ :=
  ℓ * ∑ e : Pr k, ∑ i, φ.e (π ⟨e, i⟩) (hubOf hub S ⟨e, i⟩) + φ.e (hub S true) (hub S false) * Real.logb 2 L

theorem hubTen_price {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (φ : Spec K I) {k : ℕ} (ℓ : ℕ) {L : ℕ}
    (hL : 1 ≤ L) (π : End k → I) (hub : Finset (Fin k) → Bool → I) (S : Finset (Fin k)) :
    φ.F (hubTen K ℓ L π hub S) = (2 : ℝ) ^ hubCost φ ℓ L π hub S := by
  rw [hubTen, φ.mul, φ.prod, hubCost, Real.rpow_add (by norm_num), φ.wire_eq _ _ hL, Finset.mul_sum,
    Real.rpow_sum_of_pos (by norm_num), mul_comm (φ.e _ _), Real.rpow_mul (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hL), Fintype.prod_sigma]
  refine congrArg₂ _ (Finset.prod_congr rfl fun e _ => ?_) rfl
  rw [Finset.mul_sum, Real.rpow_sum_of_pos (by norm_num)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [φ.wire_eq _ _ Nat.one_le_two_pow, Real.rpow_mul (by norm_num)]
  simp

/-- "By Lemma lem:balanced the tensor of f_{k,ℓ} is a sum of at most 2^k tensors, one for each S, each of which Lemma
lem:hubs leads through ±o_S with a wire of dimension L between them." (At most 2^k: card_bal_le.) The tensor here is that of the part linear in
each block of any polynomial with L gates. -/
theorem prop_flat_lower_sum {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] {k : ℕ} (hk : 2 ≤ k)
    {ℓ L : ℕ} {P : MvPolynomial (Fin k × Ix k ℓ) K} (hP : Computes P L) (π : End k → I)
    (hub : Finset (Fin k) → Bool → I) :
    Ten.SumRestr (Ten.push π ((fklTen K k ℓ).withVal fun z => cf univ P (tables z)))
      fun S : bal (univ : Finset (Fin k)) => hubTen K ℓ L π hub S := by
  classical
  obtain ⟨g, q, he⟩ := lem_balanced_cf hP hk
  let part : bal (univ : Finset (Fin k)) → (End k → Fin (2 ^ ℓ)) → K := fun S z =>
    ∑ δ, g S.1 δ (fun a => tables z a) * q S.1 δ fun a => tables z a
  have hsum : Ten.SumRestr ((fklTen K k ℓ).withVal fun z => cf univ P (tables z))
      fun S => ((fklTen K k ℓ).withVal fun z => cf univ P (tables z)).withVal (part S) :=
    Ten.SumRestr.of_withVal _ _ fun z => (he (tables z)).trans (Finset.sum_coe_sort _ _).symm
  refine (hsum.push π).mono fun S => ?_
  have hcongr : ∀ (z z' : End k → Fin (2 ^ ℓ)) (a : Fin k),
      (∀ x : End k, endNode x.1 x.2 = a → z x = z' x) → tables z a = tables z' a := fun z z' a h =>
    asm_congr fun e i hei => by rw [h ⟨e, i⟩ hei]
  have h := lem_hubs π ((fklTen K k ℓ).withVal (part S)) (fun x => endNode x.1 x.2 ∈ S.1)
    (fun δ z => g S.1 δ fun a => tables z a) (fun δ z => q S.1 δ fun a => tables z a)
    (fun δ z z' hz => congrArg (g S.1 δ) (funext fun a => hcongr z z' a fun x hx => hz x (hx ▸ a.2)))
    (fun δ z z' hz => congrArg (q S.1 δ)
      (funext fun a => hcongr z z' a fun x hx => hz x (hx ▸ mem_compl.1 a.2)))
    (fun z => rfl) (hub S.1 true) (hub S.1 false)
  refine h.trans ?_
  refine Eq.subst (motive := fun t => Ten.Restr t _) ?_ (Ten.Restr.refl _)
  unfold hubTen
  congr 2
  funext a
  rw [show Fintype.card (((fklTen K k ℓ).withVal (part S)).ι a) = 2 ^ ℓ from Fintype.card_fin _]
  congr 1
  unfold hubOf
  split_ifs with ha <;> simp [ha]

theorem card_bal_le (k : ℕ) : Fintype.card (bal (univ : Finset (Fin k))) ≤ 2 ^ k := by
  have h1 := Fintype.card_subtype_le (fun S => S ∈ bal (univ : Finset (Fin k)))
  simpa using h1

theorem bal_nonempty {k : ℕ} (hk : 2 ≤ k) : Nonempty (bal (univ : Finset (Fin k))) := by
  have hc : #(univ.filter fun a : Fin k => a.1 < k / 2) = k / 2 := by
    rw [Fin.card_filter_val_lt]
    omega
  exact ⟨⟨_, mem_bal.2 ⟨Finset.subset_univ (univ.filter fun a : Fin k => a.1 < k / 2), by rw [hc]; omega,
    by rw [hc]; omega⟩⟩⟩

end Paper
