/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Eval

/-!
# Constants are postponed

A program names the constants it wants in its value, a tree of names (`names`). `WN` applied to
(program, (argument, budgets)) has, as plain weighted sum, the sum of the weights of the runs whose
values name the constants exactly as the given budgets prescribe. Summed over all budgets with the
powers of the constants this is the value of the program.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R]

/-- A trie with constants of `R` at its leaves. -/
inductive KT (R : Type) where
  /-- no constant -/
  | none
  /-- one constant -/
  | leaf (c : R)
  /-- constants whose names begin with 0, constants whose names begin with 1 -/
  | node (l r : KT R)

namespace KT

/-- The number of nodes. -/
def nds : KT R → ℕ
  | none => 1
  | leaf _ => 1
  | node l r => l.nds + r.nds + 1

/-- The height: a bound for the length of names. -/
def ht : KT R → ℕ
  | none => 0
  | leaf _ => 0
  | node l r => max l.ht r.ht + 1

/-- The constant with a given name (0 if there is none). -/
def lookup : KT R → List Bool → R
  | none, _ => 0
  | leaf c, [] => c
  | leaf _, _ :: _ => 0
  | node _ _, [] => 0
  | node _ r, true :: p => r.lookup p
  | node l _, false :: p => l.lookup p

/-- Numbers with `J` digits. -/
def words : ℕ → List (List Bool)
  | 0 => [[]]
  | J + 1 => [false, true].flatMap fun b => (words J).map (b :: ·)

/-- The value of a number. -/
def val : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 1 else 0) + 2 * val w

/-- All budgets with `J` digits for the names of a trie, with the products of the powers of its constants. -/
def budg (J : ℕ) : KT R → List (Bt × R)
  | none => [(.none, 1)]
  | leaf c => (words J).map fun w => (.leaf w, c ^ val w)
  | node l r => (l.budg J).flatMap fun p => (r.budg J).map fun q => (.node p.1 q.1, p.2 * q.2)

end KT

/-- The names `b` use up the budgets. -/
def ok (t : Bt) (b : List (List Bool)) : Bool := ((Bt.decAll b t).map Bt.zero).getD false

theorem ok_nil (t : Bt) : ok t [] = t.zero := rfl

theorem ok_cons (t : Bt) (p : List Bool) (b : List (List Bool)) :
    ok t (p :: b) = ((Bt.dec p t).map fun t' => ok t' b).getD false := by
  unfold ok
  simp only [Bt.decAll]
  cases Bt.dec p t <;> rfl

theorem all_not_iff (w : List Bool) : (w.all (! ·)) = true ↔ KT.val w = 0 := by
  induction w with
  | nil => simp [KT.val]
  | cons b w ih =>
    cases b with
    | true => simp [KT.val]
    | false => simp [KT.val, ← ih]

theorem decw_val (w : List Bool) : (decw w = none ∧ KT.val w = 0) ∨ ∃ w', decw w = some w' ∧ KT.val w = KT.val w' + 1 := by
  induction w with
  | nil => left; simp [decw, KT.val]
  | cons b w ih =>
    cases b with
    | true => right; exact ⟨false :: w, rfl, by simp [KT.val]; omega⟩
    | false =>
      rcases ih with ⟨h1, h2⟩ | ⟨w', h1, h2⟩
      · left; simp [decw, h1, KT.val, h2]
      · right
        refine ⟨true :: w', by simp [decw, h1], ?_⟩
        simp only [KT.val, h2]
        simp
        omega

theorem ok_leaf (w : List Bool) (b : List (List Bool)) :
    ok (.leaf w) b = true ↔ (∀ p ∈ b, p = []) ∧ KT.val w = b.length := by
  induction b generalizing w with
  | nil =>
    rw [ok_nil, Bt.zero, all_not_iff]
    simp
  | cons p b ih =>
    rw [ok_cons]
    cases p with
    | cons a p => simp [Bt.dec]
    | nil =>
      rcases decw_val w with ⟨h1, h2⟩ | ⟨w', h1, h2⟩
      · simp only [Bt.dec, h1, Option.map_none, Option.getD_none, Bool.false_eq_true, List.length_cons, false_iff]
        rintro ⟨-, h⟩
        omega
      · simp only [Bt.dec, h1, Option.map_some, Option.getD_some, ih, List.mem_cons, forall_eq_or_imp, true_and,
          List.length_cons]
        refine and_congr_right fun _ => ?_
        omega

/-- The names that begin with a given bit. -/
def part (a : Bool) (b : List (List Bool)) : List (List Bool) := b.filterMap fun p => match p with
  | [] => none
  | c :: p => if c = a then some p else none

theorem part_cons (a c : Bool) (p : List Bool) (b : List (List Bool)) :
    part a ((c :: p) :: b) = if c = a then p :: part a b else part a b := by
  unfold part
  by_cases h : c = a <;> simp [h]

theorem length_part_le (a : Bool) (b : List (List Bool)) : (part a b).length ≤ b.length :=
  List.length_filterMap_le _ _

theorem ok_node (l r : Bt) (b : List (List Bool)) :
    ok (.node l r) b = true ↔ [] ∉ b ∧ ok l (part false b) = true ∧ ok r (part true b) = true := by
  induction b generalizing l r with
  | nil => simp [ok_nil, part, Bt.zero]
  | cons p b ih =>
    rw [ok_cons]
    cases p with
    | nil => simp [Bt.dec]
    | cons a p =>
      cases a with
      | true =>
        rw [part_cons, part_cons, if_neg (by simp), if_pos rfl, ok_cons]
        cases h : Bt.dec p r with
        | none => simp [Bt.dec, h]
        | some r' => simp [Bt.dec, h, ih]
      | false =>
        rw [part_cons, part_cons, if_pos rfl, if_neg (by simp), ok_cons]
        cases h : Bt.dec p l with
        | none => simp [Bt.dec, h]
        | some l' => simp [Bt.dec, h, ih]

theorem ok_none (b : List (List Bool)) : ok .none b = true ↔ b = [] := by
  cases b with
  | nil => simp [ok_nil, Bt.zero]
  | cons p b => simp [ok_cons, Bt.dec]

theorem sum_words (J n : ℕ) (c : R) :
    ((KT.words J).map fun w => if KT.val w = n then c else 0).sum = if n < 2 ^ J then c else 0 := by
  induction J generalizing n with
  | zero =>
    by_cases h : n = 0
    · subst h
      simp [KT.words, KT.val]
    · have h' : ¬ 0 = n := fun e => h e.symm
      simp [KT.words, KT.val, h, h']
  | succ J ih =>
    have e0 : ((KT.words J).map fun w => if KT.val (false :: w) = n then c else 0).sum =
        if n % 2 = 0 ∧ n < 2 ^ (J + 1) then c else 0 := by
      by_cases h : n % 2 = 0
      · have : ∀ w, (KT.val (false :: w) = n) = (KT.val w = n / 2) := by
          intro w
          simp only [KT.val, Bool.false_eq_true, if_false, zero_add, eq_iff_iff]
          omega
        simp only [this, ih, h, true_and]
        refine if_congr ?_ rfl rfl
        rw [pow_succ]
        omega
      · have : ∀ w, (KT.val (false :: w) = n) = False := by
          intro w
          simp only [KT.val, Bool.false_eq_true, if_false, zero_add, eq_iff_iff, iff_false]
          omega
        simp [this, h]
    have e1 : ((KT.words J).map fun w => if KT.val (true :: w) = n then c else 0).sum =
        if n % 2 = 1 ∧ n < 2 ^ (J + 1) then c else 0 := by
      by_cases h : n % 2 = 1
      · have : ∀ w, (KT.val (true :: w) = n) = (KT.val w = n / 2) := by
          intro w
          simp only [KT.val, if_true, eq_iff_iff]
          omega
        simp only [this, ih, h, true_and]
        refine if_congr ?_ rfl rfl
        rw [pow_succ]
        omega
      · have : ∀ w, (KT.val (true :: w) = n) = False := by
          intro w
          simp only [KT.val, if_true, eq_iff_iff, iff_false]
          omega
        simp [this, h]
    simp only [KT.words, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.map_map,
      List.sum_append, Function.comp_def]
    rw [e0, e1]
    by_cases hn : n < 2 ^ (J + 1)
    · rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h, hn]
    · simp [hn]

theorem sum_flatMap_map {α β M : Type*} [AddCommMonoid M] (l : List α) (f : α → List β)
    (g : β → M) : ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem prod_lookup_node (l r : KT R) (b : List (List Bool)) : (b.map (KT.node l r).lookup).prod =
    if [] ∈ b then 0 else ((part false b).map l.lookup).prod * ((part true b).map r.lookup).prod := by
  induction b with
  | nil => simp [part]
  | cons p b ih =>
    cases p with
    | nil => simp [KT.lookup]
    | cons a p =>
      rw [List.map_cons, List.prod_cons, ih, part_cons, part_cons]
      cases a with
      | true =>
        by_cases h : [] ∈ b
        · simp [h]
        · simp only [h, KT.lookup, List.mem_cons, if_false, Bool.true_eq_false, if_true, List.map_cons, List.prod_cons,
            reduceCtorEq, or_self]
          ring
      | false =>
        by_cases h : [] ∈ b
        · simp [h]
        · simp only [h, KT.lookup, List.mem_cons, if_false, Bool.false_eq_true, if_true, List.map_cons, List.prod_cons,
            reduceCtorEq, or_self]
          ring

/-- **All budgets together.** -/
theorem sum_budg (J : ℕ) (K : KT R) (b : List (List Bool)) (hb : b.length < 2 ^ J) :
    ((K.budg J).map fun q => if ok q.1 b = true then q.2 else 0).sum = (b.map K.lookup).prod := by
  induction K generalizing b with
  | none =>
    simp only [KT.budg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ok_none]
    cases b with
    | nil => simp
    | cons p b => simp [KT.lookup]
  | leaf c =>
    simp only [KT.budg, List.map_map, Function.comp_def, ok_leaf]
    by_cases h : ∀ p ∈ b, p = []
    · have e1 : ((KT.words J).map fun w => if (∀ p ∈ b, p = []) ∧ KT.val w = b.length then c ^ KT.val w else 0) =
          (KT.words J).map fun w => if KT.val w = b.length then c ^ b.length else 0 := by
        refine List.map_congr_left fun w _ => ?_
        by_cases h2 : KT.val w = b.length
        · simp [h2, if_pos h]
        · simp [h2]
      rw [e1, sum_words, if_pos hb]
      have : b.map (KT.leaf c).lookup = List.replicate b.length c := by
        rw [List.eq_replicate_iff]
        refine ⟨by simp, fun x hx => ?_⟩
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        rw [h p hp]
        rfl
      rw [this, List.prod_replicate]
    · simp only [h, false_and, if_false, List.map_const', List.sum_replicate, smul_zero]
      push Not at h
      obtain ⟨p, hp, hne⟩ := h
      symm
      apply List.prod_eq_zero
      rw [List.mem_map]
      refine ⟨p, hp, ?_⟩
      cases p with
      | nil => exact absurd rfl hne
      | cons a p => rfl
  | node l r ihl ihr =>
    have h1 := ihl (part false b) (lt_of_le_of_lt (length_part_le _ _) hb)
    have h2 := ihr (part true b) (lt_of_le_of_lt (length_part_le _ _) hb)
    rw [prod_lookup_node, ← h1, ← h2]
    simp only [KT.budg, sum_flatMap_map, List.map_map, Function.comp_def, ok_node]
    by_cases h : [] ∈ b
    · simp [h]
    · simp only [h, not_false_eq_true, true_and, if_false]
      rw [← List.sum_map_mul_right]
      congr 1
      refine List.map_congr_left fun p _ => ?_
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun q _ => ?_
      by_cases h3 : ok p.1 (part false b) = true <;> by_cases h4 : ok q.1 (part true b) = true <;> simp [h3, h4]

/-- The names in a tree of names: `nil` and `(nil, nil)` have none, `(x, (_, _))` is the name
`x.path`, and `((a, b), nil)` has the names of `a` and then those of `b`. -/
def names : Tree → List (List Bool)
  | .nil => []
  | .cons .nil .nil => []
  | .cons (.cons a b) .nil => names a ++ names b
  | .cons x (.cons _ _) => [x.path]

/-- A tree has fewer names than nodes. -/
theorem length_names_le (o : Tree) : (names o).length ≤ o.size := by
  induction o using names.induct with
  | case3 a b iha ihb => simp only [names, List.length_append, Tree.size]; omega
  | _ => simp [names, Tree.size]

/-- A tree of names with the one name that `F` gives. -/
def leaf (F : Fm) : Fm := .cons F (.quote (.cons .nil .nil))

/-- A tree of names with the names of `F` and then those of `G`. -/
def node (F G : Fm) : Fm := .cons (.cons F G) (.quote .nil)

/-- Subtract 1 in a budget at all names of a tree of names; the argument is (this program, (the
tree, the budget)). -/
def CK : Fm :=
  .ite (.hd (.tl .id))
    (.ite (.tl (.hd (.tl .id)))
      (.run (.quote DC.code) (.cons (.quote DC.code) (.cons (.hd (.hd (.tl .id))) (.tl (.tl .id)))))
      (.ite (.hd (.hd (.tl .id)))
        (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.hd (.tl .id))))
          (.run (.hd .id) (.cons (.hd .id) (.cons (.hd (.hd (.hd (.tl .id)))) (.tl (.tl .id))))))))
        (.tl (.tl .id))))
    (.tl (.tl .id))

/-- If the names of `o` use up a part of the budget `t`, `CK` gives what is left, within
`(60 H + 41) |o|` steps. -/
theorem CK_some {H : ℕ} (o : Tree) : ∀ {t t' : Bt}, t.ht ≤ H → Bt.decAll (names o) t = some t' →
    ∃ k ≤ (60 * H + 41) * o.size, Dt θ CK (.cons CK.code (.cons o t.enc)) t'.enc k := by
  induction o using names.induct with
  | case1 =>
    intro t t' _ h
    simp only [names, Bt.decAll, Option.some.injEq] at h
    subst h
    exact ⟨_, by simp only [Tree.size]; omega, Dt.ite_false (.hd (.tl (.id _))) (.tl (.tl (.id _)))⟩
  | case2 =>
    intro t t' _ h
    simp only [names, Bt.decAll, Option.some.injEq] at h
    subst h
    exact ⟨_, by simp only [Tree.size]; omega, Dt.ite_true (.hd (.tl (.id _))) (by simp)
      (Dt.ite_false (.tl (.hd (.tl (.id _)))) (Dt.ite_false (.hd (.hd (.tl (.id _))))
          (.tl (.tl (.id _)))))⟩
  | case3 a b iha ihb =>
    intro t t' ht h
    rw [names, Bt.decAll_append, Option.bind_eq_some_iff] at h
    obtain ⟨t₁, h1, h2⟩ := h
    obtain ⟨ka, hka, da⟩ := iha ht h1
    obtain ⟨kb, hkb, db⟩ := ihb (by rw [(Bt.ht_nds_decAll h1).1]; exact ht) h2
    have ea : Dt θ (Fm.ofTree CK.code) (.cons CK.code (.cons a t.enc)) t₁.enc ka := by
      rwa [Fm.ofTree_code]
    have eb : Dt θ (Fm.ofTree CK.code) (.cons CK.code (.cons b t₁.enc)) t'.enc kb := by
      rwa [Fm.ofTree_code]
    refine ⟨_, ?_, Dt.ite_true (.hd (.tl (.id _))) (by simp) (Dt.ite_false (.tl (.hd (.tl (.id _))))
      (Dt.ite_true (.hd (.hd (.tl (.id _)))) (by simp) (Dt.run (.hd (.id _)) (.cons (.hd (.id _))
        (.cons (.tl (.hd (.hd (.tl (.id _))))) (Dt.run (.hd (.id _)) (.cons (.hd (.id _))
          (.cons (.hd (.hd (.hd (.tl (.id _))))) (.tl (.tl (.id _))))) ea))) eb)))⟩
    have e : (60 * H + 41) * (a.size + b.size + 1 + 1 + 1) =
        (60 * H + 41) * a.size + (60 * H + 41) * b.size + 3 * (60 * H + 41) := by ring
    simp only [Tree.size, e]
    omega
  | case4 x u v =>
    intro t t' ht h
    simp only [names, Bt.decAll, Option.bind_eq_some_iff, Option.some.injEq, exists_eq_right] at h
    obtain ⟨k, hk, d⟩ := DC_some (θ := θ) h
    have e : Dt θ (Fm.ofTree DC.code) (.cons DC.code (.cons x t.enc)) t'.enc k := by
      rwa [Fm.ofTree_code]
    refine ⟨_, ?_, Dt.ite_true (.hd (.tl (.id _)))
        (by simp) (Dt.ite_true (.tl (.hd (.tl (.id _)))) (by simp)
      (Dt.run (.quote _ _) (.cons (.quote _ _) (.cons (.hd (.hd (.tl (.id _))))
          (.tl (.tl (.id _))))) e))⟩
    have e : (60 * H + 41) * (x.size + (u.size + v.size + 1) + 1) =
        (60 * H + 41) * x.size + (60 * H + 41) * (u.size + v.size) + 2 * (60 * H + 41) := by ring
    have := Nat.mul_le_mul_left (60 * H + 41) (Tree.size_pos x)
    have := Nat.mul_le_mul_left 60 ht
    simp only [Tree.size, e]
    omega

/-- If the names of `o` do not fit into the budget `t`, `CK` rejects. -/
theorem CK_none (o : Tree) : ∀ {t : Bt}, Bt.decAll (names o) t = none →
    Ev θ CK (.cons CK.code (.cons o t.enc)) [] := by
  induction o using names.induct with
  | case1 => intro t h; simp [names, Bt.decAll] at h
  | case2 => intro t h; simp [names, Bt.decAll] at h
  | case3 a b iha ihb =>
    intro t h
    rw [names, Bt.decAll_append] at h
    refine Ev.ite_true_nil (.hd (.tl (.id _))) (by simp) (Ev.ite_false_nil (.tl (.hd (.tl (.id _))))
      (Ev.ite_true_nil (.hd (.hd (.tl (.id _)))) (by simp) ?_))
    cases h1 : Bt.decAll (names a) t with
    | none =>
      have ea : Ev θ (Fm.ofTree CK.code) (.cons CK.code (.cons a t.enc)) [] := by
        rw [Fm.ofTree_code]; exact iha h1
      have e1 := Ev.cons_nil_right (Dt.hd (Dt.id (θ := θ)
          (.cons CK.code (.cons (.cons (.cons a b) .nil) t.enc))))
        (Ev.cons_nil_right (Dt.tl (Dt.hd (Dt.hd (Dt.tl (Dt.id (θ := θ)
          (.cons CK.code (.cons (.cons (.cons a b) .nil) t.enc)))))))
          (Ev.run_nil (.hd (.id _)) (.cons (.hd (.id _)) (.cons (.hd (.hd (.hd (.tl (.id _)))))
              (.tl (.tl (.id _))))) ea))
      have e2 := Ev.run' (Dt.hd (Dt.id (θ := θ)
          (.cons CK.code (.cons (.cons (.cons a b) .nil) t.enc)))) e1
        (by simp)
      simpa using e2
    | some t₁ =>
      rw [h1, Option.bind_some] at h
      obtain ⟨ka, -, da⟩ := CK_some (θ := θ) (H := t.ht) a le_rfl h1
      have ea : Dt θ (Fm.ofTree CK.code) (.cons CK.code (.cons a t.enc)) t₁.enc ka := by
        rwa [Fm.ofTree_code]
      have eb : Ev θ (Fm.ofTree CK.code) (.cons CK.code (.cons b t₁.enc)) [] := by
        rw [Fm.ofTree_code]; exact ihb h
      exact Ev.run_nil (.hd (.id _)) (.cons (.hd (.id _)) (.cons (.tl (.hd (.hd (.tl (.id _)))))
        (Dt.run (.hd (.id _)) (.cons (.hd (.id _)) (.cons (.hd (.hd (.hd (.tl (.id _)))))
            (.tl (.tl (.id _))))) ea))) eb
  | case4 x u v =>
    intro t h
    have h' : Bt.dec x.path t = none := by
      cases hd : Bt.dec x.path t with
      | none => rfl
      | some t' => simp [names, Bt.decAll, hd] at h
    have e : Ev θ (Fm.ofTree DC.code) (.cons DC.code (.cons x t.enc)) [] := by
      rw [Fm.ofTree_code]; exact DC_none h'
    exact Ev.ite_true_nil (.hd (.tl (.id _))) (by simp)
      (Ev.ite_true_nil (.tl (.hd (.tl (.id _)))) (by simp)
      (Ev.run_nil (.quote _ _) (.cons (.quote _ _) (.cons (.hd (.hd (.tl (.id _))))
          (.tl (.tl (.id _))))) e))

section Weights

variable [Algebra A R]

/-- The weight of a run, if the named constants are `κ`: its weight times the constants its value
names. -/
def wt (κ : List Bool → R) (r : Run A) : R := algebraMap A R r.th * ((names r.out).map κ).prod

/-- The value of a list of runs. -/
def val (κ : List Bool → R) (l : List (Run A)) : R := (l.map (wt κ)).sum

/-- The plain sum of a list of runs: the sum of their weights. -/
def pval (l : List (Run A)) : A := (l.map Run.th).sum

end Weights

/-- Apply a program; then check that the names in its value use up the budgets. The argument is
(program, (argument, budgets)). -/
def WN : Fm := lett (.cons (.quote AZ.code)
  (lett (.cons (.quote CK.code) (.cons (.run (.hd .id) (.hd (.tl .id))) (.tl (.tl .id)))) CK)) AZ

/-- The runs with their budgets after the names of their values. -/
def simN (t : Bt) (l : List (Run A)) : List (Run A × Bt) :=
  l.flatMap fun q => ((Bt.decAll (names q.out) t).map fun t' => (q, t')).toList

/-- A run with its budget in `simN` is a run of the list whose names leave that budget. -/
theorem mem_simN {t : Bt} {l : List (Run A)} {q : Run A × Bt} (h : q ∈ simN t l) :
    q.1 ∈ l ∧ Bt.decAll (names q.1.out) t = some q.2 := by
  obtain ⟨r, hr, hq⟩ := List.mem_flatMap.1 h
  cases hd : Bt.decAll (names r.out) t with
  | none => simp [hd] at hq
  | some t' =>
    simp only [hd, Option.map_some, Option.toList_some, List.mem_singleton] at hq
    subst hq
    exact ⟨hr, hd⟩

/-- The weights of the runs of `simN` with a used up budget are those of the runs that `ok` accepts.
-/
theorem map_simN (t : Bt) (l : List (Run A)) :
    ((simN t l).flatMap fun q => if q.2.zero then [q] else []).map (fun q => q.1.th) =
      (l.filter fun r => ok t (names r.out)).map Run.th := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    rw [simN, List.flatMap_cons, List.flatMap_append, List.map_append, ← simN, ih, List.filter_cons]
    cases hd : Bt.decAll (names r.out) t with
    | none =>
      have : ok t (names r.out) = false := by rw [ok, hd]; rfl
      simp [this]
    | some t' =>
      have : ok t (names r.out) = t'.zero := by rw [ok, hd]; rfl
      rw [this]
      by_cases hz : t'.zero <;> simp [hz]

/-- The sum of the weights of the accepted runs, as a sum with zeros. -/
theorem sum_filter_th (t : Bt) (l : List (Run A)) :
    ((l.filter fun r => ok t (names r.out)).map Run.th).sum =
      (l.map fun r => if ok t (names r.out) = true then r.th else 0).sum := by
  induction l with
  | nil => rfl
  | cons r l ih => cases hr : ok t (names r.out) <;> simp [hr, ih]

/-- **Postponing**: `WN` is plain; it has the runs of the program whose values name the
constants as the budget prescribes, with their weights. -/
theorem WN_ev {H T S : ℕ} {p d : Tree} {l : List (Run A)} (h : Ev θ (Fm.ofTree p) d l)
    (hT : ∀ r ∈ l, r.cost ≤ T ∧ r.out.size ≤ S) {t : Bt} (ht : t.ht ≤ H) :
    ∃ l', Ev θ WN (.cons p (.cons d t.enc)) l' ∧
      (∀ r ∈ l', r.cost ≤ T + (60 * H + 41) * S + 40 * t.nds + 80) ∧
      l'.map Run.th = (l.filter fun r => ok t (names r.out)).map Run.th := by
  have e0 := Ev.cons (Dt.quote (θ := θ) CK.code (.cons p (.cons d t.enc)))
    (Ev.cons (Ev.run_det (Dt.hd (Dt.id (θ := θ) (.cons p (.cons d t.enc))))
      (Dt.hd (Dt.tl (Dt.id (θ := θ) (.cons p (.cons d t.enc))))) h)
      (Dt.tl (Dt.tl (Dt.id (θ := θ) (.cons p (.cons d t.enc))))))
  -- the names of every value
  obtain ⟨l2, e2, r2⟩ := lett_rel (body := CK) e0 (Q := l)
    (R := fun s q => s.th = q.th ∧ s.out = .cons CK.code (.cons q.out t.enc) ∧ s.cost ≤ q.cost + 20)
    (by
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons,
          List.map_nil, flatMap_single,
        List.map_map, List.forall₂_map_left_iff]
      refine List.forall₂_same.2 fun r hr => ⟨?_, ?_, ?_⟩
      · simp [Run.seq, Run.tick, Run.det, Run.delay]
      · simp [Run.seq, Run.tick, Run.det, Run.delay, Tree.tl]
      · simp only [Function.comp, Run.seq, Run.tick, Run.det, Run.delay]
        omega)
    (Q2 := fun q => ((Bt.decAll (names q.out) t).map fun t' => (q, t')).toList)
    (R2 := fun r q => r.th = q.1.th ∧ r.out = q.2.enc ∧ r.cost ≤ q.1.cost + (60 * H + 41) * S + 30)
    (by
      rintro s - q hq ⟨h1, h2, h3⟩
      rw [h2]
      cases hd : Bt.decAll (names q.out) t with
      | none => exact ⟨[], CK_none q.out hd, by simp⟩
      | some t' =>
        obtain ⟨k, hk, dk⟩ := CK_some (θ := θ) q.out ht hd
        refine ⟨_, dk, ?_⟩
        simp only [Option.map_some, Option.toList_some]
        refine .cons ⟨?_, ?_, ?_⟩ .nil
        · simp [Run.det, h1]
        · simp [Run.det]
        · have := Nat.mul_le_mul_left (60 * H + 41) (hT q hq).2
          simp only [Run.det]
          omega)
  -- the check
  have e3 := Ev.cons (Dt.quote (θ := θ) AZ.code (.cons p (.cons d t.enc))) e2
  obtain ⟨l4, e4, r4⟩ := lett_rel (body := AZ) e3 (Q := simN t l)
    (R := fun r q => r.th = q.1.th ∧ r.out = .cons AZ.code q.2.enc ∧
      r.cost ≤ q.1.cost + (60 * H + 41) * S + 40) (by
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.forall₂_map_left_iff]
      refine r2.imp fun r q hr => ?_
      obtain ⟨h1, h2, h3⟩ := hr
      refine ⟨?_, ?_, ?_⟩
      · simp [Run.seq, Run.tick, Run.det, h1]
      · simp [Run.seq, Run.tick, Run.det, h2]
      · simp only [Run.seq, Run.tick, Run.det]
        omega) (Q2 := fun q => if q.2.zero then [q] else [])
    (R2 := fun r q => r.th = q.1.th ∧ r.cost ≤ q.1.cost + (60 * H + 41) * S + 40 * t.nds + 80) (by
      rintro s - q hq ⟨h1, h2, h3⟩
      obtain ⟨k, hk, o, h5⟩ := AZ_ev (θ := θ) q.2
      rw [← h2] at h5
      refine ⟨_, h5, ?_⟩
      have hn : q.2.nds = t.nds := (Bt.ht_nds_decAll (mem_simN hq).2).2
      by_cases hz : q.2.zero
      · simp only [hz, if_true]
        refine .cons ⟨?_, ?_⟩ .nil
        · simp [Run.det, h1]
        · simp only [Run.det]
          omega
      · simp only [hz]
        exact .nil)
  refine ⟨l4, e4, ?_, ?_⟩
  · intro r hr
    obtain ⟨q, hq, h1, h2⟩ := forall₂_exists r4 hr
    refine h2.trans ?_
    rw [List.mem_flatMap] at hq
    obtain ⟨q', hq', hq⟩ := hq
    have : q = q' := by
      split_ifs at hq
      · simpa using hq
      · simp at hq
    subst this
    have := (hT _ (mem_simN hq').1).1
    omega
  · rw [← map_simN]
    clear e4
    generalize ((simN t l).flatMap fun q => if q.2.zero then [q] else []) = Q at r4
    induction r4 with
    | nil => rfl
    | cons h _ ih => simp [h.1, ih]

variable [Algebra A R]

/-- **Lemma 1 (postponing).** The value of a list of runs is the sum, over all budgets, of the powers of the constants
times the sums of the weights of the runs that use up the budgets. -/
theorem val_eq_sum_budg {J : ℕ} {K : KT R} {κ : List Bool → R} {l : List (Run A)}
    (hJ : ∀ r ∈ l, (names r.out).length < 2 ^ J)
    (hκ : ∀ r ∈ l, ∀ p ∈ (names r.out), κ p = K.lookup p) :
    val κ l = ((K.budg J).map fun q =>
      q.2 * algebraMap A R
        (l.map fun r => if ok q.1 (names r.out) = true then r.th else 0).sum).sum := by
  induction l with
  | nil => simp [val]
  | cons r l ih =>
    have h1 := ih (fun r hr => hJ r (List.mem_cons_of_mem _ hr)) fun r hr => hκ r (List.mem_cons_of_mem _ hr)
    have h2 := sum_budg J K (names r.out) (hJ r List.mem_cons_self)
    have h3 : ((names r.out).map κ).prod = ((names r.out).map K.lookup).prod := by
      congr 1
      exact List.map_congr_left fun p hp => hκ r List.mem_cons_self p hp
    have h4 : val κ (r :: l) = wt κ r + val κ l := by simp [val]
    rw [h4, h1, wt, h3, ← h2, ← List.sum_map_mul_left, ← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    simp only [List.map_cons, List.sum_cons, map_add, mul_add]
    congr 1
    by_cases h : ok q.1 (names r.out) = true
    · simp only [h, if_true]
      ring
    · simp [h]

end NS1
