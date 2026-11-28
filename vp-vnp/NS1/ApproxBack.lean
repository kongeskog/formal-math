/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.ApproxExtract
import Nc.Acc.Main

/-!
# An approximate accelerator gives an exact one

The program that reads the coefficient of ε^0 out of an approximate accelerator, its constants and its size.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree LaurentPolynomial Nc.Grp

variable {A : Type} [CommRing A] {θ : List Bool → A} {E : Type} [CommRing E] [Algebra A E]

/-- Accept only with the counter at 0; the value is then the tree of names. The argument is
(counter, names). -/
def finF : Fm := .ite (app nzB.code (.cons (.quote nzB.code) (.hd .id))) .fail (.tl .id)

theorem finF_kv {κ : List Bool → E} {S : Set (List Bool)} {o : List Bool} {acc : Tree}
    (hS : ∀ n ∈ names acc, n ∈ S) : KV θ κ S finF (.cons (ofBits o) acc)
      ((if KT.val o = 0 then 1 else 0) * ((names acc).map κ).prod)
      (20 * o.length + acc.size + 20) := by
  have hn := Gives.lett (Gives.cons (Gives.quote (θ := θ) nzB.code (.cons (ofBits o) acc))
    (Gives.id _).hd) (nzB_gives o)
  by_cases hz : KT.val o = 0
  · rw [show bit (decide (KT.val o ≠ 0)) = .nil by simp [hz, bit]] at hn
    rw [if_pos hz, one_mul]
    exact (KV.ite_false hn (KV.gives (Gives.id _).tl hS)).mono (by simp only [tl_cons]; omega)
  · rw [if_neg hz, zero_mul]
    exact (KV.ite_true hn (by simp [hz, bit, one]) (KV.fail _)).mono (by omega)

theorem coeff_list_sum {G : Type*} [AddCommMonoid G] (l : List (AddMonoidAlgebra E G)) (i : G) :
    l.sum.coeff i = (l.map fun P => P.coeff i).sum := by
  induction l with
  | nil => rfl
  | cons P l ih => simp [AddMonoidAlgebra.coeff_add, ih]

/-- The coefficient at 0 of a coefficient with a counter: the counter has to be 0. -/
theorem coeff_mark_zero {W : ℕ} {o : List Bool} (h : o.length = W) (a : E) :
    (mark W o a).coeff 0 = if KT.val o = 0 then a else 0 := by
  have h0 : (((KT.val o : ℕ) : ZMod (2 ^ W)) = 0) ↔ KT.val o = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact ⟨fun h' => Nat.eq_zero_of_dvd_of_lt h' (val_lt_of_length h), fun h' => h' ▸ dvd_zero _⟩
  rw [mark, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  exact if_congr h0 rfl rfl

theorem coeff_algebraMap_mul (a : A) (P : E[T;T⁻¹]) (i : ℤ) :
    (algebraMap A E[T;T⁻¹] a * P).coeff i = algebraMap A E a * P.coeff i := by
  rw [← Algebra.smul_def, ← Algebra.smul_def]
  rfl

theorem Span.list_prod {N : ℕ} (l : List E[T;T⁻¹]) (h : ∀ P ∈ l, Span N P) :
    Span (l.length * N) l.prod := by
  induction l with
  | nil => simpa using Span.one (E := E) 0
  | cons P l ih =>
    rw [List.prod_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact (h P List.mem_cons_self).mul (ih fun Q hQ => h Q (List.mem_cons_of_mem _ hQ))

/-- The program of the extraction: run `D`, go through the names of its value with `termF`, and
accept only with the counter at 0. -/
def extF (D : Tree) (W m : ℕ) (T : Tree) : Fm :=
  lett (app D .id) (lett (foldF (termF m T) (.quote (.cons (ofBits (List.replicate W false)) .nil))
    (app flatB.code (.cons (.quote flatB.code) (.cons .id (.quote .nil))))) finF)

/-- **The value of the extraction**: the coefficient of ε^0 of the value of `D`. -/
theorem extF_kv {κ : List Bool → E[T;T⁻¹]} {κ' : List Bool → E} {S : Set (List Bool)} {D z T : Tree}
    {l : List (Run A)} {t W m N : ℕ} (hD : Ev θ (Fm.ofTree D) z l)
    (ht : ∀ r ∈ l, r.cost + r.out.size ≤ t)
    (hn : ∀ r ∈ l, ∀ x ∈ nmT r.out, (κ x.path).coeff.support.card ≤ 2 ^ m ∧ Span N (κ x.path) ∧
      ∀ w : List Bool, w.length = m →
        tget (x.path ++ w) T = ofBits (expBits W (termExp (κ x.path) (KT.val w))) ∧
        κ' (x.path ++ (w ++ [false])) = termCoef (κ x.path) (KT.val w) ∧
        x.path ++ (w ++ [false]) ∈ S)
    (hW : t * N < 2 ^ W) :
    KV θ κ' S (extF D W m T) z ((val κ l).coeff 0)
      (t * (51 * m + 15 * W + 202) + 20 * W + 60) := by
  have he := Ev.run_det (Dt.quote (θ := θ) D z) (Dt.id z) hD
  refine ((KV.app_ev (κ := κ') (S := S) (c := t + 3) (d := t * (51 * m + 15 * W + 201) + 20 * W + 55)
    (ω := fun s => ((names s.out).map κ).prod.coeff 0) he ?_ ?_).mono ?_).congr ?_
  · intro s hs
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hs
    have := ht r hr
    simp only [Run.delay]
    omega
  · intro s hs
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hs
    have hno := hn r hr
    have hto : r.out.size ≤ t := (Nat.le_add_left _ _).trans (ht r hr)
    show KV θ κ' S _ r.out (((names r.out).map κ).prod.coeff 0) _
    generalize r.out = o at hno hto
    rw [Fm.ofTree_code]
    have hl := Gives.lett (Gives.cons (Gives.quote (θ := θ) flatB.code o)
      (Gives.cons (Gives.id o) (Gives.quote (listT []) o))) (flatB_gives o [])
    rw [List.append_nil] at hl
    have hf := foldT (encE := id) (enc := fun s : List Bool × Tree => .cons (ofBits s.1) s.2)
      (f := termL W m κ) (Inv := fun _ s => s.1.length = W)
      (d := fun x => 160 * x.size + 200 * m + 60 * W + 400) (s₀ := (List.replicate W false, .nil))
      (Gives.quote _ o) (by rwa [List.map_id])
      (fun x _ s hx hs => ⟨by
        have := termF_does (θ := θ) (m := m) (T := T) (x := x) (s := s)
          (e := fun w => expBits W (termExp (κ x.path) (KT.val w)))
          (fun w hw => ((hno x hx).2.2 w hw).1) fun w => (length_expBits _ _).trans hs.symm
        rwa [hs] at this, fun q hq => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.1 hq
        exact (length_addc _ (hs.trans (length_expBits _ _).symm)).trans hs⟩)
      (List.length_replicate ..)
    have hm := fun q (hq : q ∈ foldL (A := A) (termL W m κ) (nmT o)
        (List.replicate W false, .nil)) => mem_foldL_term (S := S) (nmT o)
      (fun x hx w hw => ((hno x hx).2.2 w hw).2.2) _ (List.length_replicate ..)
      (by simp [names]) hq
    refine ((KV.lett (ω := fun u => (if KT.val u.hd.path = 0 then 1 else 0) *
        ((names u.tl).map κ').prod) hf
      (d := 20 * W + (1 + ((nmT o).map fun x => x.size + 4 * m + 12).sum) + 20)
      fun q hq => ?_).mono ?_).congr ?_
    · obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      obtain ⟨a1, a2, a3⟩ := hm q' hq'
      have := finF_kv (θ := θ) (κ := κ') (o := q'.2.1) a2
      simp only [Prod.map, id, hd_cons, tl_cons, path_ofBits]
      rw [a1] at this
      exact this.mono (by simp only [Tree.size] at a3; omega)
    · have key : ((nmT o).map fun x => 160 * x.size + 200 * m + 60 * W + 400 + 30).sum +
          ((nmT o).map fun x => x.size + 4 * m + 12).sum ≤ (51 * m + 15 * W + 161) * o.size := by
        rw [← List.sum_map_add]
        calc _ ≤ ((nmT o).map fun x => (51 * m + 15 * W + 161) * (x.size + 4)).sum :=
              List.sum_le_sum fun x _ => by
                have e : (51 * m + 15 * W + 161) * (x.size + 4) =
                    161 * x.size + 204 * m + 60 * W + 644 + (51 * m + 15 * W) * x.size := by ring
                omega
          _ = (51 * m + 15 * W + 161) * ((nmT o).map fun x => x.size + 4).sum := by
              rw [List.sum_map_mul_left]
          _ ≤ _ := Nat.mul_le_mul_left _ (sum_nmT_le o)
      have h2 := Nat.mul_le_mul_right (51 * m + 15 * W + 201) hto
      have e : o.size * (51 * m + 15 * W + 201) =
          (51 * m + 15 * W + 161) * o.size + 40 * o.size := by ring
      omega
    · have e2 := congrArg (fun P : AddMonoidAlgebra E (ZMod (2 ^ W)) => P.coeff 0)
        (sum_foldL_term (A := A) (κ' := κ') (nmT o)
          (fun x hx => ⟨(hno x hx).1, fun w hw => ((hno x hx).2.2 w hw).2.1⟩)
          (List.replicate W false, .nil) (List.length_replicate ..))
      have e0 : mark W (List.replicate W false) (1 : E) = 1 := by
        rw [mark, (all_not_iff _).1 (by simp), Nat.cast_zero]
        rfl
      have hsp : Span ((names o).length * N) ((names o).map κ).prod := by
        have := Span.list_prod (N := N) ((names o).map κ) fun P hP => by
          rw [names_eq, List.map_map] at hP
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hP
          exact (hno x hx).2.1
        rwa [List.length_map] at this
      simp only [coeff_list_sum, List.map_map, names, List.map_nil, List.prod_nil, e0, one_mul] at e2
      rw [show (nmT o).map (fun x => κ x.path) = (names o).map κ by
        rw [names_eq, List.map_map]; rfl, coeff_wrap_zero hsp (lt_of_le_of_lt
          (Nat.mul_le_mul_right N ((length_names_le o).trans hto)) hW)] at e2
      rw [← e2, List.map_map]
      refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
      simp only [Function.comp_apply, Prod.map, id, hd_cons, tl_cons, path_ofBits,
        coeff_mark_zero (hm q hq).1]
      split_ifs <;> simp
  · have e : t * (51 * m + 15 * W + 202) = t * (51 * m + 15 * W + 201) + t := by ring
    omega
  · rw [List.map_map, val, coeff_list_sum, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun r _ => (coeff_algebraMap_mul _ _ _).symm)

end NS1
