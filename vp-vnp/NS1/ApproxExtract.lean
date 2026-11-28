/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.ApproxScale
import NS1.ApproxAdd
import Nc.Acc.Loop

/-!
# Back to equality

A program runs an approximate accelerator and goes through the names of its value. For every name
it guesses one term of the constant, names the coefficient of the term, an element of the ring E,
and adds the exponent of ε on a counter. It accepts only if the counter is 0. So its value is the
coefficient of ε^0 of an approximate value: the exact one.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree LaurentPolynomial Nc.Grp

variable {A : Type} [CommRing A] {θ : List Bool → A} {E : Type} [CommRing E] [Algebra A E]

section Terms

/-- The exponent of the term with the number `k`. -/
noncomputable def termExp (P : E[T;T⁻¹]) (k : ℕ) : ℤ := P.coeff.support.toList.getD k 0

/-- Its coefficient; 0 if there is no such term. -/
noncomputable def termCoef (P : E[T;T⁻¹]) (k : ℕ) : E :=
  if k < P.coeff.support.toList.length then P.coeff (termExp P k) else 0

/-- An exponent as `W` digits modulo 2 ^ W. -/
noncomputable def expBits (W : ℕ) (e : ℤ) : List Bool := (exists_word (ZMod.val_lt (e : ZMod (2 ^ W)))).choose

theorem length_expBits (W : ℕ) (e : ℤ) : (expBits W e).length = W :=
  (exists_word (ZMod.val_lt (e : ZMod (2 ^ W)))).choose_spec.1

theorem cast_val_expBits (W : ℕ) (e : ℤ) : ((KT.val (expBits W e) : ℕ) : ZMod (2 ^ W)) = e := by
  rw [expBits, (exists_word (ZMod.val_lt (e : ZMod (2 ^ W)))).choose_spec.2, ZMod.natCast_zmod_val]

/-- Exponents modulo 2 ^ W. -/
noncomputable def wrap (A : Type) [CommRing A] {E : Type} [CommRing E] [Algebra A E] (W : ℕ) :
    E[T;T⁻¹] →ₐ[A] AddMonoidAlgebra E (ZMod (2 ^ W)) :=
  AddMonoidAlgebra.mapDomainAlgHom A E (Int.castAddHom (ZMod (2 ^ W)))

/-- A coefficient with the exponent on the counter. -/
noncomputable def mark (W : ℕ) (o : List Bool) (a : E) : AddMonoidAlgebra E (ZMod (2 ^ W)) :=
  AddMonoidAlgebra.single ((KT.val o : ℕ) : ZMod (2 ^ W)) a

theorem mark_addc {W : ℕ} {o o' : List Bool} (h : o.length = W) (h' : o'.length = W) (a a' : E) :
    mark W (addc false o o') (a * a') = mark W o a * mark W o' a' := by
  simp [mark, AddMonoidAlgebra.single_mul_single, val_addc false (h.trans h'.symm), h]

theorem wrap_apply (W : ℕ) (P : E[T;T⁻¹]) : wrap A W P =
    ∑ i ∈ P.coeff.support, AddMonoidAlgebra.single ((i : ℤ) : ZMod (2 ^ W)) (P.coeff i) := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single P]
  rw [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [wrap, -LaurentPolynomial.single_eq_C_mul_T]

/-- **Paper: proof of Proposition prop:approx-acc, the counter at 0.** The coefficient at 0 modulo 2 ^ W is the one of ε^0. -/
theorem coeff_wrap_zero {W n : ℕ} {P : E[T;T⁻¹]} (h : Span n P) (hn : n < 2 ^ W) :
    (wrap A W P).coeff 0 = P.coeff 0 := by
  classical
  rw [wrap_apply, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    refine if_neg fun h0 => hi0 ?_
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h0 ?_
    rw [Int.natAbs_natCast]
    exact lt_of_le_of_lt (h i (Finsupp.mem_support_iff.1 hi)) hn
  · intro h0
    simp [Finsupp.notMem_support_iff.1 h0]

/-- **All terms of a Laurent polynomial.** -/
theorem sum_terms {W m : ℕ} (P : E[T;T⁻¹]) (h : P.coeff.support.card ≤ 2 ^ m) :
    ((wd m).map fun w => mark W (expBits W (termExp P (KT.val w))) (termCoef P (KT.val w))).sum =
      wrap A W P := by
  rw [sum_wd m fun k => mark W (expBits W (termExp P k)) (termCoef P k), wrap_apply]
  simp only [mark, cast_val_expBits]
  rw [← Finset.sum_subset (Finset.range_mono (show P.coeff.support.toList.length ≤ 2 ^ m by simpa using h))]
  · conv_rhs => rw [← Finset.sum_map_toList, ← Fin.sum_univ_fun_getElem]
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [termCoef, if_pos i.2, termExp, List.getD_eq_getElem _ _ i.2]
  · intro k _ hk
    rw [Finset.mem_range] at hk
    rw [termCoef, if_neg hk]
    simp

end Terms

section Leaves

variable {R : Type} [CommRing R]

theorem KT.leaf_comb (c : R) {B b : ℕ} (h : b < B) : (KT.comb c B).Leaf (KT.pw b) := by
  induction b generalizing c B with
  | zero =>
    cases B with
    | zero => omega
    | succ B => rfl
  | succ b ih =>
    cases B with
    | zero => omega
    | succ B => exact ih _ (by omega)

/-- The name of a power of a constant is a leaf of the trie of the powers. -/
theorem KT.leaf_expand {B : ℕ} {K : KT R} {p : List Bool} (h : K.InB B p) :
    (K.expand B).Leaf p := by
  induction K generalizing p with
  | none => exact h.elim
  | leaf c =>
    obtain ⟨b, hb, rfl⟩ := h
    exact KT.leaf_comb c hb
  | node l r ihl ihr =>
    cases p with
    | nil => exact h.elim
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem KT.All.lookup {P : R → Prop} {K : KT R} (h : K.All P) {p : List Bool} (hp : K.Leaf p) :
    P (K.lookup p) := by
  induction K generalizing p with
  | none => exact hp.elim
  | leaf c =>
    obtain rfl : p = [] := hp
    exact h
  | node l r ihl ihr =>
    cases p with
    | nil => exact hp.elim
    | cons a p =>
      cases a with
      | true => exact ihr h.2 hp
      | false => exact ihl h.1 hp

end Leaves

section Gadget

/-- The coefficients of the terms of the constants, with a name for every term: the name of the
constant, the number of the term in `m` digits, and 0. -/
noncomputable def coefK (m : ℕ) : KT E[T;T⁻¹] → KT E
  | .none => .none
  | .leaf c => KT.full m fun w => termCoef c (KT.val w)
  | .node l r => .node (coefK m l) (coefK m r)

theorem lk_coefK {m : ℕ} {K : KT E[T;T⁻¹]} {p w : List Bool} (hp : K.Leaf p) (hw : w.length = m) :
    (coefK m K).lk (p ++ (w ++ [false])) = termCoef (K.lookup p) (KT.val w) ∧
      (coefK m K).InB 1 (p ++ (w ++ [false])) := by
  induction K generalizing p with
  | none => exact hp.elim
  | leaf c =>
    obtain rfl : p = [] := hp
    exact KT.lk_full _ hw
  | node l r ihl ihr =>
    cases p with
    | nil => exact hp.elim
    | cons a p =>
      cases a with
      | true => exact ihr hp
      | false => exact ihl hp

/-- A trie, as `tget` reads it, with the value `f w` at every name `w` of length `n`. -/
def fullT : ℕ → (List Bool → Tree) → Tree
  | 0, f => .cons (f []) .nil
  | n + 1, f =>
    .cons .nil (.cons (fullT n fun w => f (false :: w)) (fullT n fun w => f (true :: w)))

theorem tget_fullT {n : ℕ} (f : List Bool → Tree) {w : List Bool} (h : w.length = n) :
    tget w (fullT n f) = f w := by
  induction n generalizing f w with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 h
    rfl
  | succ n ih =>
    cases w with
    | nil => simp at h
    | cons b w => cases b <;> exact ih _ (by simpa using h)

theorem size_fullT {n C : ℕ} (f : List Bool → Tree) (h : ∀ w, (f w).size ≤ C) :
    (fullT n f).size + 3 ≤ 2 ^ n * (C + 5) := by
  induction n generalizing f with
  | zero =>
    have := h []
    simp only [fullT, Tree.size]
    omega
  | succ n ih =>
    have h1 := ih (fun w => f (false :: w)) fun w => h _
    have h2 := ih (fun w => f (true :: w)) fun w => h _
    have e : 2 ^ (n + 1) * (C + 5) = 2 ^ n * (C + 5) + 2 ^ n * (C + 5) := by ring
    simp only [fullT, Tree.size]
    omega

/-- The exponents of the terms of the constants, as a trie: at the name of a constant and the
number of a term, the exponent in `W` digits. -/
noncomputable def expT (W m : ℕ) : KT E[T;T⁻¹] → Tree
  | .none => .nil
  | .leaf c => fullT m fun w => ofBits (expBits W (termExp c (KT.val w)))
  | .node l r => .cons .nil (.cons (expT W m l) (expT W m r))

theorem tget_expT {W m : ℕ} {K : KT E[T;T⁻¹]} {p w : List Bool} (hp : K.Leaf p)
    (hw : w.length = m) :
    tget (p ++ w) (expT W m K) = ofBits (expBits W (termExp (K.lookup p) (KT.val w))) := by
  induction K generalizing p with
  | none => exact hp.elim
  | leaf c =>
    obtain rfl : p = [] := hp
    exact tget_fullT _ hw
  | node l r ihl ihr =>
    cases p with
    | nil => exact hp.elim
    | cons a p =>
      cases a with
      | true => exact ihr hp
      | false => exact ihl hp

theorem size_expT (W m : ℕ) (K : KT E[T;T⁻¹]) :
    (expT W m K).size + 3 ≤ K.nds * (2 ^ m * (4 * W + 6)) := by
  induction K with
  | none =>
    have := Nat.mul_le_mul (Nat.one_le_two_pow (n := m)) (Nat.le_add_left 6 (4 * W))
    simp only [expT, Tree.size, KT.nds, one_mul]
    omega
  | leaf c =>
    have := size_fullT (n := m) (C := 4 * W + 1)
      (fun w => ofBits (expBits W (termExp c (KT.val w)))) fun w => by
        have := size_ofBits (expBits W (termExp c (KT.val w)))
        rwa [length_expBits] at this
    simpa [expT, KT.nds] using this
  | node l r ihl ihr =>
    simp only [expT, Tree.size, KT.nds, add_mul, one_mul]
    omega

end Gadget

section Walk

/-- The names of a list of trees and bits put after one another. -/
theorem path_listT_append (x : Tree) (w : List Bool) :
    (listT (x.toList ++ w.map bit)).path = x.path ++ w := by
  induction x with
  | nil => rw [toList, List.nil_append, listT_ofBits, path_ofBits]; rfl
  | cons a b _ ih => simp only [toList, List.cons_append, listT, path, ih]

theorem length_toList (x : Tree) : x.toList.length = x.len := by
  induction x with
  | nil => rfl
  | cons a b _ ih => simp only [toList, List.length_cons, len, ih]

theorem len_listT (l : List Tree) : (listT l).len = l.length := by
  rw [← length_toList, toList_listT]

theorem size_listT_append (x : Tree) (ys : List Tree) :
    (listT (x.toList ++ ys)).size + 1 = x.size + (listT ys).size := by
  induction x with
  | nil => simp only [toList, List.nil_append, Tree.size]; omega
  | cons a b _ ih => simp only [toList, List.cons_append, listT, Tree.size]; omega

/-- One name: guess a term of its constant, add the exponent of the term to the counter, and put the
name of its coefficient in front of the names. The argument is (name, (counter, names)); `T` is the
trie of the exponents. -/
def termF (m : ℕ) (T : Tree) : Fm :=
  lett (.cons .id (gwd m)) (lett (.cons .id (appF (.hd (.hd .id)) (.tl .id)))
    (.cons (.run (.quote AD.code) (.cons (.quote AD.code) (.cons (.quote .nil)
        (.cons (.hd (.tl (.hd (.hd .id)))) (getF (.tl .id) (.quote T))))))
      (node (leaf (appF (.tl .id) (.quote (ofBits [false])))) (.tl (.tl (.hd (.hd .id)))))))

/-- The state after a name `x` with the term `w`: `e` is the exponent of the term. -/
def termS (x : Tree) (w e : List Bool) (s : List Bool × Tree) : List Bool × Tree :=
  (addc false s.1 e, .cons (.cons (.cons (listT (x.toList ++ (w ++ [false]).map bit))
    (.cons .nil .nil)) s.2) .nil)

theorem termF_does {m : ℕ} {T x : Tree} {s : List Bool × Tree} {e : List Bool → List Bool}
    (hT : ∀ w, w.length = m → tget (x.path ++ w) T = ofBits (e w))
    (he : ∀ w, (e w).length = s.1.length) :
    Does θ (termF m T) (.cons x (.cons (ofBits s.1) s.2))
      (((wd m).map fun w => ((1 : A), termS x w (e w) s)).map
        (Prod.map id fun s => .cons (ofBits s.1) s.2))
      (160 * x.size + 200 * m + 60 * s.1.length + 400) := by
  refine ((Does.letk (gwd_does (θ := θ) m (.cons x (.cons (ofBits s.1) s.2)))
    (R := fun v => [(1, .cons (ofBits (addc false s.1 (e v.path)))
      (.cons (.cons (.cons (listT (x.toList ++ (v.path ++ [false]).map bit)) (.cons .nil .nil)) s.2)
        .nil))])
    (d := 212 * x.len + 160 * m + 60 * s.1.length + 300) fun q hq => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hq
      have hwm := length_of_mem_wd hw
      obtain ⟨k, hk', hd⟩ := AD_dt (θ := θ) false (he w).symm
      obtain ⟨y, hy⟩ : ∃ y, y = Tree.cons (.cons (.cons x (.cons (ofBits s.1) s.2)) (ofBits w))
        (listT (x.toList ++ w.map bit)) := ⟨_, rfl⟩
      have hg := getF_gives (θ := θ) (Gives.id y).tl (Gives.quote T y)
      have hn := appF_gives (θ := θ) (xs := x.toList ++ w.map bit) (ys := [bit false])
        (by rw [hy]; exact (Gives.id _).tl) (Gives.quote _ y)
      have hc : Gives θ (.hd (.tl (.hd (.hd .id)))) y (ofBits s.1) 5 := by
        rw [hy]; exact (Gives.id _).hd.hd.tl.hd
      have ha : Gives θ (.tl (.tl (.hd (.hd .id)))) y s.2 5 := by
        rw [hy]; exact (Gives.id _).hd.hd.tl.tl
      rw [hy, tl_cons, path_listT_append, hT w hwm, ← hy] at hg
      have h2 := Gives.cons (Gives.run (Gives.quote AD.code y) (Gives.cons (Gives.quote AD.code y)
        (Gives.cons (Gives.quote .nil y) (Gives.cons hc hg)))
          (by rw [Fm.ofTree_code]; exact (Does.of_dt hd).mono hk'))
        (Gives.cons (Gives.cons (Gives.cons hn (Gives.quote (.cons .nil .nil) y)) ha)
          (Gives.quote .nil y))
      have hk := appF_gives (θ := θ) (xs := x.toList) (ys := w.map bit)
        (x := .cons (.cons x (.cons (ofBits s.1) s.2)) (ofBits w))
        (by rw [listT_toList]; exact (Gives.id _).hd.hd)
        (by rw [listT_ofBits]; exact (Gives.id _).tl)
      rw [hy] at h2
      have h3 := Gives.lett (Gives.cons (Gives.id _) hk) h2
      rw [List.append_assoc] at h3
      simp only [path_ofBits, List.map_append, List.map_cons, List.map_nil]
      refine Does.mono h3 ?_
      simp only [len_listT, List.length_append, List.length_map, length_toList, hwm]
      omega).replace ?_).mono (by have := two_len_lt x; omega)
  simp [bindW, flatMap_single, termS, Function.comp_def]

/-- What `termF` gives at the name `x`: for every term of the constant `κ x.path`, the counter with
the exponent of the term added and the names with the name of its coefficient. -/
noncomputable def termL (W m : ℕ) (κ : List Bool → E[T;T⁻¹]) (x : Tree) (s : List Bool × Tree) :
    List (A × List Bool × Tree) :=
  (wd m).map fun w => (1, termS x w (expBits W (termExp (κ x.path) (KT.val w))) s)

/-- **Paper: proof of Proposition prop:approx-acc, the guessed terms together give the constants.**
Summed over the runs of the walk, the coefficients named, with the counter as exponent modulo
2 ^ W, are the product of the constants of the names. -/
theorem sum_foldL_term {W m : ℕ} {κ : List Bool → E[T;T⁻¹]} {κ' : List Bool → E} (xs : List Tree)
    (hx : ∀ x ∈ xs, (κ x.path).coeff.support.card ≤ 2 ^ m ∧ ∀ w, w.length = m →
      κ' (x.path ++ (w ++ [false])) = termCoef (κ x.path) (KT.val w))
    (s : List Bool × Tree) (hs : s.1.length = W) :
    ((foldL (A := A) (termL W m κ) xs s).map fun q =>
      mark W q.2.1 (algebraMap A E q.1 * ((names q.2.2).map κ').prod)).sum =
      mark W s.1 ((names s.2).map κ').prod * wrap A W (xs.map fun x => κ x.path).prod := by
  induction xs generalizing s with
  | nil => simp [foldL]
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := hx x List.mem_cons_self
    rw [foldL, termL, bindW_pure, sum_flatMap_map, List.map_cons, List.prod_cons, map_mul,
      ← sum_terms (A := A) (W := W) _ h1, ← mul_assoc, ← List.sum_map_mul_left,
      ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun w hw => ?_)
    rw [ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) _
      (by rw [termS, length_addc _ (hs.trans (length_expBits _ _).symm), hs])]
    have e : names (termS x w (expBits W (termExp (κ x.path) (KT.val w))) s).2 =
        (x.path ++ (w ++ [false])) :: names s.2 := by
      rw [termS, names, names, path_listT_append]
      rfl
    rw [e, List.map_cons, List.prod_cons, h2 w (length_of_mem_wd hw), mul_comm (termCoef _ _),
      termS, mark_addc hs (length_expBits _ _)]

/-- The states of the walk: the counter keeps its length, the names are names of coefficients, and
the tree of names grows by the name and twelve nodes more for every name. -/
theorem mem_foldL_term {W m : ℕ} {κ : List Bool → E[T;T⁻¹]} {S : Set (List Bool)} (xs : List Tree)
    (hx : ∀ x ∈ xs, ∀ w : List Bool, w.length = m → x.path ++ (w ++ [false]) ∈ S)
    (s : List Bool × Tree) (hs : s.1.length = W) (hS : ∀ n ∈ names s.2, n ∈ S)
    {q : A × List Bool × Tree} (hq : q ∈ foldL (termL W m κ) xs s) :
    q.2.1.length = W ∧ (∀ n ∈ names q.2.2, n ∈ S) ∧
      q.2.2.size ≤ s.2.size + (xs.map fun x => x.size + 4 * m + 12).sum := by
  induction xs generalizing s with
  | nil =>
    obtain rfl := List.mem_singleton.1 hq
    exact ⟨hs, hS, Nat.le_add_right _ _⟩
  | cons x xs ih =>
    rw [foldL, termL, bindW_pure, List.mem_flatMap] at hq
    obtain ⟨w, hw, hq⟩ := hq
    have hwm := length_of_mem_wd hw
    obtain ⟨a1, a2, a3⟩ := ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) _
      (by rw [termS, length_addc _ (hs.trans (length_expBits _ _).symm), hs]) (by
        intro n hn
        simp only [termS, names, path_listT_append, List.cons_append, List.nil_append,
          List.mem_cons] at hn
        rcases hn with rfl | hn
        · exact hx x List.mem_cons_self w hwm
        · exact hS n hn) hq
    refine ⟨a1, a2, a3.trans ?_⟩
    have h1 := size_listT_append x ((w ++ [false]).map bit)
    have h2 := size_ofBits (w ++ [false])
    rw [listT_ofBits] at h1
    simp only [List.length_append, List.length_singleton, hwm] at h2
    simp only [termS, Tree.size, List.map_cons, List.sum_cons]
    omega

end Walk

end NS1
