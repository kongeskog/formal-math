/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.ApproxOrd
import Paper.Postpone
import Nc.Acc.CompK

/-!
# One round for approximate accelerators

The budgets of the outer program are guessed and their constants named exactly. The constants of
the inner program are rescaled by ε ↦ ε^r, with r above every exponent in the outer weights. To give
the rescaled constants names of their own the round goes through the names of the value of the list
program and writes `true` in front of each (`renF`).
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree LaurentPolynomial

variable {A : Type} [CommRing A] {θ : List Bool → A}

section Programs

variable {R : Type} [CommRing R] [Algebra A R] {κ : List Bool → R} {S : Set (List Bool)}

/-- Put a name, with `true` in front, before the names so far; the argument is (name, names). -/
def preF : Fm := node (leaf (.cons (.quote one) (.hd .id))) (.tl .id)

/-- The names of a list, each with `true` in front, before the names `acc`. -/
def preT (xs : List Tree) (acc : Tree) : Tree :=
  xs.foldl (fun acc x => .cons (.cons (.cons (.cons one x) (.cons .nil .nil)) acc) .nil) acc

theorem names_preT (xs : List Tree) (acc : Tree) :
    names (preT xs acc) = (xs.reverse.map fun x => true :: x.path) ++ names acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    rw [preT, List.foldl_cons, ← preT, ih, names, names]
    simp [path, one]

theorem size_preT (xs : List Tree) (acc : Tree) :
    (preT xs acc).size = acc.size + (xs.map fun x => x.size + 11).sum := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    rw [preT, List.foldl_cons, ← preT, ih]
    simp only [Tree.size, one, List.map_cons, List.sum_cons]
    omega

/-- The names of a value, each with `true` in front. -/
def renF : Fm := foldF preF (.quote .nil)
  (app flatB.code (.cons (.quote flatB.code) (.cons .id (.quote .nil))))

theorem renF_gives (o : Tree) : Gives θ renF o (preT (nmT o) .nil)
    (40 * o.size + ((nmT o).map fun _ => 11 + 30).sum + 29) := by
  have hl := Gives.lett (Gives.cons (Gives.quote (θ := θ) flatB.code o)
    (Gives.cons (Gives.id o) (Gives.quote (listT []) o))) (flatB_gives o [])
  rw [List.append_nil] at hl
  exact (foldF_gives (Inv := fun _ _ => True) (d := fun _ => 11) (Gives.quote .nil o) hl
    (fun x _ σ _ _ => ⟨Gives.cons (Gives.cons (Gives.cons (Gives.cons (Gives.quote one _)
      (Gives.id _).hd) (Gives.quote _ _)) (Gives.id _).tl) (Gives.quote .nil _), trivial⟩)
    trivial).mono (by omega)

/-- **A program with renamed constants**: its names with `true` in front name the images under
`f` of its constants. A pass over the value writes the new names. -/
theorem renamed_kv (f : R →ₐ[A] R) {κ₀ : List Bool → R} {S₀ : Set (List Bool)} {F : Fm} {x : Tree}
    {w : R} {c : ℕ} (h : KV θ κ₀ S₀ F x w c)
    (hS : ∀ p ∈ S₀, κ (true :: p) = f (κ₀ p) ∧ true :: p ∈ S) :
    KV θ κ S (lett F renF) x (f w) (54 * c + 40) := by
  obtain ⟨l, e1, e2, e3⟩ := h
  refine ((KV.app_ev (p := renF.code) (c := c) (d := 53 * c + 32)
    (ω := fun s => f ((names s.out).map κ₀).prod) e1
    (fun s hs => (Nat.le_add_right _ _).trans (e2 s hs).1) fun s hs => ?_).mono (by omega)).congr ?_
  · have hn : names (preT (nmT s.out) .nil) = (nmT s.out).reverse.map fun x => true :: x.path := by
      rw [names_preT, names, List.append_nil]
    have hm : ∀ x ∈ nmT s.out, x.path ∈ S₀ := fun x hx =>
      (e2 s hs).2 _ (by rw [names_eq]; exact List.mem_map_of_mem hx)
    rw [Fm.ofTree_code]
    refine ((KV.gives (renF_gives s.out) fun p hp => ?_).mono ?_).congr ?_
    · rw [hn] at hp
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hp
      exact (hS _ (hm y (List.mem_reverse.1 hy))).2
    · have key : ((nmT s.out).map fun _ => 11 + 30).sum +
          ((nmT s.out).map fun x => x.size + 11).sum ≤ 13 * s.out.size := by
        rw [← List.sum_map_add]
        calc _ ≤ ((nmT s.out).map fun x => 13 * (x.size + 4)).sum :=
              List.sum_le_sum fun x _ => by omega
          _ = 13 * ((nmT s.out).map fun x => x.size + 4).sum := by rw [List.sum_map_mul_left]
          _ ≤ _ := Nat.mul_le_mul_left _ (sum_nmT_le _)
      have := (e2 s hs).1
      rw [size_preT]
      simp only [Tree.size]
      omega
    · rw [hn, names_eq, List.map_map, List.map_map, map_list_prod, List.map_map,
        List.map_reverse, List.prod_reverse]
      exact congrArg List.prod (List.map_congr_left fun y hy => (hS _ (hm y hy)).1)
  · rw [← e3, val, map_list_sum, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun s _ => by simp [wt])

end Programs

section Round

variable {E : Type} [CommRing E] [Algebra A E]

/-- **Paper: the definition of an approximate accelerator.** The program `D`, with constants in E[ε,ε⁻¹], has values in pv z + ε E[ε], in `t`
steps, on the instances of size `v ^ (H - 32)` of the universal plain sums of `v ^ H` steps. -/
structure IsAccA (θ : List Bool → A) (H v t : ℕ) (K : KT E[T;T⁻¹]) (B : ℕ) (D : Tree) : Prop where
  run : ∀ z, z.size ≤ v ^ (H - 32) → Hl θ (Fm.ofTree D) z ∧ ∀ r ∈ evl θ (Fm.ofTree D) z,
      r.cost + r.out.size ≤ t ∧
    ∀ p ∈ names r.out, K.InB B p
  val : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
    OrdGE 1 (val K.lk (evl θ (Fm.ofTree D) z) - algebraMap A E[T;T⁻¹] (pv θ z))

/-- The same, where runs have to stop only if the sum is plain. -/
structure IsPreA (θ : List Bool → A) (H v t : ℕ) (K : KT E[T;T⁻¹]) (B : ℕ) (D : Tree) : Prop where
  run : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z → Hl θ (Fm.ofTree D) z ∧
    ∀ r ∈ evl θ (Fm.ofTree D) z, r.cost + r.out.size ≤ t ∧ ∀ p ∈ names r.out, K.InB B p
  val : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
    OrdGE 1 (val K.lk (evl θ (Fm.ofTree D) z) - algebraMap A E[T;T⁻¹] (pv θ z))

theorem IsAccA.pre {H v t : ℕ} {K : KT E[T;T⁻¹]} {B : ℕ} {D : Tree} (h : IsAccA θ H v t K B D) :
    IsPreA θ H v t K B D :=
  ⟨fun z hz _ => h.run z hz, h.val⟩

theorem IsAccA.mono {H v t t' : ℕ} {K : KT E[T;T⁻¹]} {B B' : ℕ} {D : Tree} (h : IsAccA θ H v t K B D) (ht : t ≤ t')
    (hB : B ≤ B') : IsAccA θ H v t' K B' D :=
  ⟨fun z hz => ⟨(h.run z hz).1, fun r hr => ⟨((h.run z hz).2 r hr).1.trans ht, fun p hp =>
    (((h.run z hz).2 r hr).2 p hp).mono hB⟩⟩, h.val⟩

/-- The universal program is a program for the universal plain sums; it needs no constants. -/
theorem UF_preA (θ : List Bool → A) (H v : ℕ) (B : ℕ) :
    IsPreA (E := E) θ H v (v ^ H + 9) KT.none B UF.code := by
  constructor
  · intro z _ hp
    have e := UF_ev hp.1.ev
    rw [Fm.ofTree_code]
    refine ⟨e.hl, fun r hr => ?_⟩
    rw [e.evl, List.mem_map] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    have := hp.2 s hs
    simp only [Tree.size, names]
    exact ⟨by omega, by simp⟩
  · intro z _ hp
    rw [Fm.ofTree_code, (UF_ev hp.1.ev).evl,
      show val KT.none.lk _ = algebraMap A E[T;T⁻¹] (pv θ z) by
        simp [val, wt, names, pv, pval, map_list_sum, Function.comp_def], sub_self]
    exact OrdGE.zero 1

/-- The constants of `E` as constant Laurent polynomials. -/
noncomputable def cstL : E →ₐ[A] E[T;T⁻¹] := IsScalarTower.toAlgHom A E E[T;T⁻¹]

/-- An exact accelerator is an approximate one with constants in `E`. -/
theorem IsAccT.toA {H v t : ℕ} {K : KT E} {B : ℕ} {D : Tree} (h : IsAccT θ H v t K B D) :
    IsAccA θ H v t (K.map (cstL (A := A))) B D := by
  have h' := h.map (cstL (A := A) (E := E))
  refine ⟨h'.run, fun z hz hp => ?_⟩
  rw [h'.val z hz hp, sub_self]
  exact OrdGE.zero 1

/-- If the constants of an approximate accelerator are constant Laurent polynomials, the images of a trie `K`
over `E`, then the same program with `K` is an exact accelerator: the value minus pv(z) then lies in `E`, and
having no term in ε⁰ it is zero. -/
theorem IsAccA.toT {H v t : ℕ} {K : KT E} {B : ℕ} {D : Tree}
    (h : IsAccA θ H v t (K.map (cstL (A := A))) B D) : IsAccT θ H v t K B D := by
  refine ⟨fun z hz => ⟨(h.run z hz).1, fun r hr => ⟨((h.run z hz).2 r hr).1, fun p hp =>
    (KT.inB_map _ B K p).1 (((h.run z hz).2 r hr).2 p hp)⟩⟩, fun z hz hp => ?_⟩
  have h0 := h.val z hz hp 0 (by norm_num)
  rw [NS1.val_map, ← AlgHom.commutes (cstL (A := A) (E := E)), ← map_sub] at h0
  have : (cstL (A := A) (E := E)) (NS1.val K.lk (evl θ (Fm.ofTree D) z) - algebraMap A E (pv θ z)) =
      algebraMap E E[T;T⁻¹] (NS1.val K.lk (evl θ (Fm.ofTree D) z) - algebraMap A E (pv θ z)) := rfl
  rw [this, coeff_algebraMap (A := E) (E := E), if_pos rfl] at h0
  exact sub_eq_zero.1 (by simpa using h0)

/-- Rescaling `ε ↦ ε ^ r` fixes the constants of `E`. -/
theorem rescale_cstL (r : ℕ) (e : E) : rescale A r (cstL (A := A) e) = cstL (A := A) e := by
  show rescale A r (algebraMap E E[T;T⁻¹] e) = algebraMap E E[T;T⁻¹] e
  rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply]
  simp only [rescale, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidHom.coe_mulLeft]
  rw [AddMonoidAlgebra.mapDomain_single, mul_zero]

/-- The program of a round: the names of the outer budgets begin with 0, those of the inner
program are renamed to begin with 1. -/
def roundA {R : Type} (K : KT R) (B J : ℕ) (D G p : Tree) : Fm :=
  stepA (lett (.run (.hd .id) .id) renF) (LP D).code G p (gt id J B K [false])

end Round

end NS1
