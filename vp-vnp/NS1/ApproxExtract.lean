/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.ApproxScale
import NS1.ApproxAdd
import Nc.Acc.Trie

/-!
# Back to equality

A program guesses, for every constant, the digits of its power and one term of that power, names the
coefficient of the term, an element of the ring E, and adds the exponent of ε on a counter. It accepts only if the
counter is 0. So its value is the coefficient of ε^0 of an approximate value: the exact one.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree LaurentPolynomial

variable {A : Type} [CommRing A] {θ : List Bool → A} {E : Type} [CommRing E] [Algebra A E]

section Choice

/-- Guess a word of length `n`; go on with the formula of this word. -/
def chT : ℕ → (List Bool → Fm) → Fm
  | 0, f => f []
  | n + 1, f => .ite .guess (chT n fun w => f (true :: w)) (chT n fun w => f (false :: w))

/-- A run that gives budgets and the digits of a counter, and names constants whose product is a coefficient. -/
def RelX (κ : List Bool → E) (S : Set (List Bool)) (c : ℕ) (r : Run A) (q : Bt × E × List Bool) : Prop :=
  RelT κ (· ∈ S) c r (.cons q.1.enc (ofBits q.2.2)) q.2.1

theorem RelX.mono {κ : List Bool → E} {S : Set (List Bool)} {c d : ℕ} {r : Run A} {q : Bt × E × List Bool}
    (h : RelX κ S c r q) (hd : c ≤ d) : RelX κ S d r q :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.trans hd⟩

theorem chT_ev {κ : List Bool → E} {S : Set (List Bool)} {c : ℕ} {x : Tree} {n : ℕ} {f : List Bool → Fm}
    {o : List Bool → Bt × E × List Bool}
    (h : ∀ w : List Bool, w.length = n → ∃ l, Ev θ (f w) x l ∧ List.Forall₂ (RelX κ S c) l [o w]) :
    ∃ l, Ev θ (chT n f) x l ∧ List.Forall₂ (RelX κ S (c + 3 * n)) l ((KT.words n).map o) := by
  induction n generalizing f o with
  | zero =>
    obtain ⟨l, e, r⟩ := h [] rfl
    exact ⟨l, e, r⟩
  | succ n ih =>
    obtain ⟨l1, e1, r1⟩ := ih (f := fun w => f (true :: w)) (o := fun w => o (true :: w)) fun w hw => h _ (by simp [hw])
    obtain ⟨l0, e0, r0⟩ := ih (f := fun w => f (false :: w)) (o := fun w => o (false :: w)) fun w hw => h _ (by simp [hw])
    refine ⟨_, Ev.ite (L := fun r => if r.out = .nil then l0 else l1) (Ev.guess x)
      (fun r _ h => by rw [if_neg h]; exact e1) (fun r _ h => by rw [if_pos h]; exact e0), ?_⟩
    simp only [KT.words, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.map_map,
      Run.det, Tree.one, if_true, reduceCtorEq, if_false, Function.comp_def]
    refine List.rel_append ?_ ?_ <;> rw [List.forall₂_map_left_iff]
    · refine r0.imp fun r q hr => ⟨by simp [Run.seq, Run.tick, hr.1], hr.2.1, hr.2.2.1, hr.2.2.2.1, ?_⟩
      have := hr.2.2.2.2
      simp only [Run.seq, Run.tick]
      omega
    · refine r1.imp fun r q hr => ⟨by simp [Run.seq, Run.tick, hr.1], hr.2.1, hr.2.2.1, hr.2.2.2.1, ?_⟩
      have := hr.2.2.2.2
      simp only [Run.seq, Run.tick]
      omega

end Choice

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

theorem sum_words_range (n : ℕ) {G : Type*} [AddCommMonoid G] (f : ℕ → G) :
    ((KT.words n).map fun w => f (KT.val w)).sum = ∑ k ∈ Finset.range (2 ^ n), f k := by
  induction n generalizing f with
  | zero => simp [KT.words, KT.val]
  | succ n ih =>
    have e : ((KT.words (n + 1)).map fun w => f (KT.val w)).sum =
        ((KT.words n).map fun w => f (2 * KT.val w)).sum + ((KT.words n).map fun w => f (1 + 2 * KT.val w)).sum := by
      simp [KT.words, KT.val, Function.comp_def]
    rw [e, ih fun k => f (2 * k), ih fun k => f (1 + 2 * k), pow_succ, mul_comm]
    clear e ih
    induction 2 ^ n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_one, Finset.sum_range_succ, Finset.sum_range_succ,
        ← ih, show 1 + 2 * k = 2 * k + 1 by ring]
      abel

theorem sum_words_split (J m : ℕ) {G : Type*} [AddCommMonoid G] (F : List Bool → List Bool → G) :
    ((KT.words (J + m)).map fun w => F (w.take J) (w.drop J)).sum =
      ((KT.words J).map fun v => ((KT.words m).map fun w => F v w).sum).sum := by
  induction J generalizing F with
  | zero => simp [KT.words]
  | succ J ih =>
    rw [Nat.succ_add]
    simp [KT.words, Function.comp_def, ih fun v w => F (false :: v) w, ih fun v w => F (true :: v) w]

/-- **All terms of a Laurent polynomial.** -/
theorem sum_terms {W m : ℕ} (P : E[T;T⁻¹]) (h : P.coeff.support.card ≤ 2 ^ m) :
    ((KT.words m).map fun w => mark W (expBits W (termExp P (KT.val w))) (termCoef P (KT.val w))).sum =
      wrap A W P := by
  rw [sum_words_range m fun k => mark W (expBits W (termExp P k)) (termCoef P k), wrap_apply]
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

section Gadget

/-- The coefficients of the terms of the powers, with names for every choice of digits and term. -/
noncomputable def coefK (J m : ℕ) : KT E[T;T⁻¹] → KT E
  | .none => .none
  | .leaf c => KT.full (J + m) fun w => termCoef (c ^ KT.val (w.take J)) (KT.val (w.drop J))
  | .node l r => .node (coefK J m l) (coefK J m r)

/-- What the gadget guesses: budgets, a coefficient, the digits of the counter. -/
noncomputable def xL (J m W : ℕ) : KT E[T;T⁻¹] → List (Bt × E × List Bool)
  | .none => [(.none, 1, List.replicate W false)]
  | .leaf c => (KT.words (J + m)).map fun w => (.leaf (w.take J), termCoef (c ^ KT.val (w.take J)) (KT.val (w.drop J)),
      expBits W (termExp (c ^ KT.val (w.take J)) (KT.val (w.drop J))))
  | .node l r => (xL J m W l).flatMap fun p => (xL J m W r).map fun q =>
      (.node p.1 q.1, p.2.1 * q.2.1, addc false p.2.2 q.2.2)

/-- Pair the budgets and add the counters. The argument is ((data, names), (data, names)) where the data are
(budgets, counter). -/
def combF : Fm := .cons (.cons (.cons (.hd (.hd (.hd .id))) (.hd (.hd (.tl .id)))) (.quote .nil))
  (.run (.quote AD.code) (.cons (.quote AD.code) (.cons (.quote .nil)
    (.cons (.tl (.hd (.hd .id))) (.tl (.hd (.tl .id)))))))

/-- The gadget. Its value is ((budgets, counter), names). -/
noncomputable def xF (J m W : ℕ) : KT E[T;T⁻¹] → List Bool → Fm
  | .none, _ => .quote (.cons (.cons Bt.none.enc (ofBits (List.replicate W false))) .nil)
  | .leaf c, pre => chT (J + m) fun w => .cons
      (.quote (.cons (Bt.leaf (w.take J)).enc (ofBits (expBits W (termExp (c ^ KT.val (w.take J)) (KT.val (w.drop J)))))))
      (leaf (.quote (ofBits (pre ++ (w ++ [false])))))
  | .node l r, pre => zipF combF (xF J m W l (pre ++ [false])) (xF J m W r (pre ++ [true]))

section

-- The gadget for the tree of constants `K`, with `J` digits of budget, `m` of term, `W` of counter.
variable {J m W : ℕ} {K : KT E[T;T⁻¹]}

theorem length_xL : ∀ q ∈ xL J m W K, q.2.2.length = W := by
  induction K with
  | none =>
    intro q hq
    simp only [xL, List.mem_singleton] at hq
    subst hq
    simp
  | leaf c =>
    intro q hq
    simp only [xL, List.mem_map] at hq
    obtain ⟨w, -, rfl⟩ := hq
    exact length_expBits _ _
  | node l r ihl ihr =>
    intro q hq
    simp only [xL, List.mem_flatMap, List.mem_map] at hq
    obtain ⟨a, ha, b, hb, rfl⟩ := hq
    rw [length_addc _ ((ihl a ha).trans (ihr b hb).symm)]
    exact ihl a ha

/-- The budgets of the gadget have few digits. -/
theorem bt_xL :
    ∀ q ∈ xL J m W K, q.1.ht ≤ K.ht + J + 1 ∧ q.1.nds ≤ K.nds * (J + 1) := by
  induction K with
  | none =>
    intro q hq
    simp only [xL, List.mem_singleton] at hq
    subst hq
    simp [Bt.ht, Bt.nds, KT.nds]
  | leaf c =>
    intro q hq
    simp only [xL, List.mem_map] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    simp [Bt.ht, Bt.nds, KT.ht, KT.nds, KT.length_words hw]
  | node l r ihl ihr =>
    intro q hq
    simp only [xL, List.mem_flatMap, List.mem_map] at hq
    obtain ⟨a, ha, b, hb, rfl⟩ := hq
    obtain ⟨h1, h2⟩ := ihl a ha
    obtain ⟨h3, h4⟩ := ihr b hb
    simp only [Bt.ht, Bt.nds, KT.ht, KT.nds]
    refine ⟨by omega, ?_⟩
    have : (l.nds + r.nds + 1) * (J + 1) = l.nds * (J + 1) + r.nds * (J + 1) + (J + 1) := by ring
    omega

/-- **Paper: proof of Proposition prop:approx-acc, the guessed terms together give all budgets.** Counted modulo 2 ^ W. -/
theorem sum_xL (hK : K.All fun c => ∀ n < 2 ^ J, (c ^ n).coeff.support.card ≤ 2 ^ m)
    (φ : Bt → AddMonoidAlgebra E (ZMod (2 ^ W))) :
    ((xL J m W K).map fun q => φ q.1 * mark W q.2.2 q.2.1).sum = ((K.budg J).map fun q => φ q.1 * wrap A W q.2).sum := by
  induction K generalizing φ with
  | none =>
    have : KT.val (List.replicate W false) = 0 := (all_not_iff _).1 (by simp)
    simp only [xL, KT.budg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mark, this, Nat.cast_zero,
      map_one]
    rfl
  | leaf c =>
    simp only [xL, KT.budg, List.map_map, Function.comp_def]
    rw [sum_words_split J m fun v w => φ (.leaf v) *
      mark W (expBits W (termExp (c ^ KT.val v) (KT.val w))) (termCoef (c ^ KT.val v) (KT.val w))]
    congr 1
    refine List.map_congr_left fun v hv => ?_
    rw [List.sum_map_mul_left, sum_terms (A := A) _ (hK _ (val_lt_of_length (KT.length_words hv)))]
  | node l r ihl ihr =>
    simp only [xL, KT.budg, sum_flatMap_map, List.map_map, Function.comp_def]
    calc ((xL J m W l).map fun p => ((xL J m W r).map fun q =>
          φ (.node p.1 q.1) * mark W (addc false p.2.2 q.2.2) (p.2.1 * q.2.1)).sum).sum
        = ((xL J m W l).map fun p => ((r.budg J).map fun q => φ (.node p.1 q.1) * wrap A W q.2).sum *
            mark W p.2.2 p.2.1).sum := by
          congr 1
          refine List.map_congr_left fun p hp => ?_
          rw [← ihr hK.2 fun t => φ (.node p.1 t), ← List.sum_map_mul_right]
          congr 1
          refine List.map_congr_left fun q hq => ?_
          rw [mark_addc (length_xL p hp) (length_xL q hq)]
          ring
      _ = _ := by
          rw [ihl hK.1 fun t => ((r.budg J).map fun q => φ (.node t q.1) * wrap A W q.2).sum]
          congr 1
          refine List.map_congr_left fun p _ => ?_
          rw [← List.sum_map_mul_right]
          congr 1
          refine List.map_congr_left fun q _ => ?_
          rw [map_mul]
          ring

end

theorem le_size_ofBits (w : List Bool) : 2 * w.length + 1 ≤ (ofBits w).size := by
  induction w with
  | nil => simp [ofBits, Tree.size]
  | cons b w ih => cases b <;> simp [ofBits, bit, one, Tree.size] <;> omega

theorem combF_dt {W : ℕ} {t t' : Bt} {o o' : List Bool} (h : o.length = W) (h' : o'.length = W) {u w : Tree}
    (hu : u.hd = .cons t.enc (ofBits o)) (hw : w.hd = .cons t'.enc (ofBits o')) :
    ∃ k ≤ 60 * W + 90, Dt θ combF (.cons u w) (.cons (Bt.node t t').enc (ofBits (addc false o o'))) k := by
  obtain ⟨k, hk, hd⟩ := AD_dt (θ := θ) false (h.trans h'.symm)
  have hd' : Dt θ (Fm.ofTree AD.code) (.cons AD.code (.cons .nil (.cons (ofBits o) (ofBits o'))))
      (ofBits (addc false o o')) k := by
    rw [Fm.ofTree_code]
    exact hd
  have := Dt.cons (Dt.cons (Dt.cons (Dt.hd (Dt.hd (Dt.hd (Dt.id (θ := θ) (.cons u w)))))
    (Dt.hd (Dt.hd (Dt.tl (Dt.id _))))) (Dt.quote .nil _))
    (Dt.run (Dt.quote AD.code _) (Dt.cons (Dt.quote AD.code _) (Dt.cons (Dt.quote .nil _)
      (Dt.cons (Dt.tl (Dt.hd (Dt.hd (Dt.id _)))) (Dt.tl (Dt.hd (Dt.tl (Dt.id _))))))) (by simpa [hu, hw] using hd'))
  simp only [hd_cons, tl_cons, hu, hw, Bt.enc] at this ⊢
  exact ⟨_, by omega, this⟩

/-- **The runs of the gadget.** -/
theorem xF_ev {J m W L : ℕ} {κ : List Bool → E} {S : Set (List Bool)} (x : Tree) (K : KT E[T;T⁻¹]) (pre : List Bool)
    (h : ∀ p, (coefK J m K).InB 1 p → κ (pre ++ p) = (coefK J m K).lk p ∧ pre ++ p ∈ S ∧ (pre ++ p).length ≤ L) :
    ∃ l, Ev θ (xF J m W K pre) x l ∧
      List.Forall₂ (RelX κ S (K.nds * (70 * W + 4 * L + 7 * (J + m) + 200))) l (xL J m W K) := by
  induction K generalizing pre with
  | none =>
    have := size_ofBits (List.replicate W false)
    refine ⟨_, .quote _ x, .cons ⟨rfl, rfl, by simp [Run.det, names], by simp [Run.det, names], ?_⟩ .nil⟩
    simp only [Run.det, Tree.size, Bt.enc, KT.nds, List.length_replicate] at this ⊢
    omega
  | leaf c =>
    have hl := chT_ev (θ := θ) (κ := κ) (S := S) (c := 4 * W + 4 * L + 4 * (J + m) + 30) (x := x) (n := J + m)
      (f := fun w => .cons (.quote (.cons (Bt.leaf (w.take J)).enc
        (ofBits (expBits W (termExp (c ^ KT.val (w.take J)) (KT.val (w.drop J)))))))
        (leaf (.quote (ofBits (pre ++ (w ++ [false]))))))
      (o := fun w => (.leaf (w.take J), termCoef (c ^ KT.val (w.take J)) (KT.val (w.drop J)),
        expBits W (termExp (c ^ KT.val (w.take J)) (KT.val (w.drop J))))) fun w hw => by
        have e := Dt.cons (Dt.quote (θ := θ) (.cons (Bt.leaf (w.take J)).enc
          (ofBits (expBits W (termExp (c ^ KT.val (w.take J)) (KT.val (w.drop J)))))) x)
          (Dt.cons (Dt.quote (ofBits (pre ++ (w ++ [false]))) x) (Dt.quote (.cons .nil .nil) x))
        refine ⟨_, e, .cons ⟨rfl, rfl, ?_, ?_, ?_⟩ .nil⟩
        · obtain ⟨h1, -, -⟩ := h (w ++ [false]) (KT.inB_full _ hw)
          simp only [Run.det, tl_cons, names, path_ofBits, List.map_cons, List.map_nil, List.prod_cons,
            List.prod_nil, mul_one]
          rw [h1]
          exact KT.lk_full _ hw
        · simpa [Run.det, names, path_ofBits] using (h (w ++ [false]) (KT.inB_full _ hw)).2.1
        · have h3 := (h (w ++ [false]) (KT.inB_full _ hw)).2.2
          have s1 := size_ofBits (pre ++ (w ++ [false]))
          have s2 := size_ofBits (w.take J)
          have s3 := size_ofBits (expBits W (termExp (c ^ KT.val (w.take J)) (KT.val (w.drop J))))
          simp only [length_expBits, List.length_take] at s2 s3
          simp only [Run.det, Tree.size, Bt.enc]
          omega
    obtain ⟨l, e, r⟩ := hl
    refine ⟨l, e, r.imp fun s q hs => hs.mono ?_⟩
    simp only [KT.nds]
    omega
  | node l r ihl ihr =>
    obtain ⟨ll, el, rl⟩ := ihl (pre ++ [false]) fun p hp => by
      simpa [coefK, KT.lk] using h (false :: p) hp
    obtain ⟨lr, er, rr⟩ := ihr (pre ++ [true]) fun p hp => by
      simpa [coefK, KT.lk] using h (true :: p) hp
    obtain ⟨L', eL, rL⟩ := zip_rel (e := fun a b => .cons (.cons (.cons a.hd b.hd) .nil) (ofBits (addc false a.tl.path
      b.tl.path))) el er rl rr (fun a ha b hb u w hu hw => by
        simpa [path_ofBits, Bt.enc] using combF_dt (θ := θ) (length_xL a ha) (length_xL b hb) hu hw)
      fun a ha b hb => by
        have := size_ofBits (addc false a.2.2 b.2.2)
        rw [length_addc _ ((length_xL a ha).trans (length_xL b hb).symm), length_xL a ha] at this
        have h1 := le_size_ofBits a.2.2
        have h2 := le_size_ofBits b.2.2
        rw [length_xL a ha] at h1
        rw [length_xL b hb] at h2
        simp only [hd_cons, tl_cons, path_ofBits, Tree.size]
        omega
    refine ⟨L', eL, ?_⟩
    have e : xL J m W (l.node r) = (((xL J m W l).flatMap fun a => (xL J m W r).map fun b => (a, b)).map
        fun p => (Bt.node p.1.1 p.2.1, p.1.2.1 * p.2.2.1, addc false p.1.2.2 p.2.2.2)) := by
      simp [xL, List.map_flatMap, Function.comp_def]
    rw [e, List.forall₂_map_right_iff]
    refine rL.imp fun s p hs => ⟨hs.1, by simpa [Bt.enc, path_ofBits] using hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
    have := hs.2.2.2.2
    simp only [KT.nds]
    nlinarith

end Gadget

end NS1
