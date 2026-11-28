/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Lists

/-!
# Words of trees, parts of lists, the names of a value against a budget
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

section Word

/-- The brackets of a tree, in preorder; `t0`: empty, `t1`: a node. -/
def wordT (t0 t1 : Tree) : Tree → List Tree
  | .nil => [t0]
  | .cons a b => t1 :: (wordT t0 t1 a ++ wordT t0 t1 b)

theorem length_wordT (t0 t1 z : Tree) : (wordT t0 t1 z).length = z.size := by
  induction z with
  | nil => rfl
  | cons a b iha ihb =>
    simp only [wordT, List.length_cons, List.length_append, iha, ihb, Tree.size]

/-- Write the brackets of a tree in front of a list. The argument is (this program, (tree, list)). -/
def wordB (t0 t1 : Tree) : Fm := .ite (.hd (.tl .id))
  (.cons (.quote t1) (.run (.hd .id) (.cons (.hd .id) (.cons (.hd (.hd (.tl .id)))
    (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.tl (.tl .id)))))))))
  (.cons (.quote t0) (.tl (.tl .id)))

/-- The brackets of a tree. -/
def wordF (t0 t1 : Tree) (z : Fm) : Fm :=
  app (wordB t0 t1).code (.cons (.quote (wordB t0 t1).code) (.cons z (.quote .nil)))

theorem wordB_gives (t0 t1 z : Tree) (acc : List Tree) :
    Gives θ (wordB t0 t1) (.cons (wordB t0 t1).code (.cons z (listT acc))) (listT (wordT t0 t1 z ++ acc))
      (60 * z.size) := by
  induction z generalizing acc with
  | nil =>
    refine ((Gives.id _).tl.hd.ite_false (Gives.cons (Gives.quote t0 _) (Gives.id _).tl.tl)).mono ?_
    simp [Tree.size]
  | cons a b iha ihb =>
    rw [wordT, List.cons_append, List.append_assoc]
    refine Does.mono ((Gives.id _).tl.hd.ite_true (by simp) (Gives.cons (Gives.quote t1 _)
      (Does.self ((Gives.id _).hd.cons ((Gives.id _).tl.hd.hd.cons
        (Does.self ((Gives.id _).hd.cons ((Gives.id _).tl.hd.tl.cons (Gives.id _).tl.tl))
          (ihb acc))))
        (iha _)))) ?_
    simp only [Tree.size]
    omega

theorem wordF_gives {t0 t1 : Tree} {zf : Fm} {x z : Tree} {cz : ℕ} (hz : Gives θ zf x z cz) :
    Gives θ (wordF t0 t1 zf) x (listT (wordT t0 t1 z)) (cz + 60 * z.size + 10) := by
  have h := wordB_gives (θ := θ) t0 t1 z []
  rw [List.append_nil] at h
  exact (Gives.lett (Gives.cons (Gives.quote _ _)
    (Gives.cons hz (Gives.quote (listT []) _))) h).mono (by omega)

end Word

section Take

/-- Is a number not 0? The argument is (this program, number). -/
def nzB : Fm := .ite (.tl .id) (.ite (.hd (.tl .id)) (.quote one) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id)))))
  (.quote .nil)

theorem nzB_gives (w : List Bool) :
    Gives θ nzB (.cons nzB.code (ofBits w)) (bit (decide (KT.val w ≠ 0))) (20 * w.length + 10) := by
  induction w with
  | nil => exact ((Gives.id _).tl.ite_false (Gives.quote .nil _)).mono (by simp)
  | cons b w ih =>
    cases b with
    | true =>
      have e : bit (decide (KT.val (true :: w) ≠ 0)) = one := by
        have : KT.val (true :: w) ≠ 0 := by simp [KT.val]
        simp [this, bit]
      rw [e]
      refine ((Gives.id _).tl.ite_true (by simp [ofBits]) ((Gives.id _).tl.hd.ite_true (by simp [ofBits, bit, one])
        (Gives.quote one _))).mono ?_
      simp only [List.length_cons]
      omega
    | false =>
      have e : decide (KT.val (false :: w) ≠ 0) = decide (KT.val w ≠ 0) := by
        simp [KT.val]
      rw [e]
      refine Does.mono ((Gives.id _).tl.ite_true (by simp [ofBits]) ((Gives.id _).tl.hd.ite_false
        (Does.self ((Gives.id _).hd.cons (Gives.id _).tl.tl) ih))) ?_
      simp only [List.length_cons]
      omega

/-- Take elements from a list, as many as a binary number says. The argument is (this program, (number, (elements
taken, in reversed order, list))); the value is (elements taken, rest). -/
def takeB : Fm := .ite (.tl (.tl (.tl .id)))
  (.ite (app nzB.code (.cons (.quote nzB.code) (.hd (.tl .id))))
    (.run (.hd .id) (.cons (.hd .id) (.cons (app DW.code (.cons (.quote DW.code) (.hd (.tl .id))))
      (.cons (.cons (.hd (.tl (.tl (.tl .id)))) (.hd (.tl (.tl .id)))) (.tl (.tl (.tl (.tl .id))))))))
    (.tl (.tl .id)))
  (.tl (.tl .id))

theorem takeB_gives (w : List Bool) (acc l : List Tree) :
    Gives θ takeB (.cons takeB.code (.cons (ofBits w) (.cons (listT acc) (listT l))))
      (.cons (listT ((l.take (KT.val w)).reverse ++ acc)) (listT (l.drop (KT.val w))))
      (((l.take (KT.val w)).length + 1) * (60 * w.length + 100)) := by
  induction l generalizing w acc with
  | nil =>
    have h : Gives θ takeB (.cons takeB.code (.cons (ofBits w) (.cons (listT acc) (listT []))))
        (.cons (listT acc) (listT [])) 20 := (Gives.ite_false (Gives.id _).tl.tl.tl (Gives.id _).tl.tl).mono (by norm_num)
    rw [List.take_nil, List.drop_nil, List.reverse_nil, List.nil_append]
    refine h.mono ?_
    simp only [List.length_nil, zero_add, one_mul]
    omega
  | cons a l ih =>
    have hnz := Gives.lett (Gives.cons (Gives.quote (θ := θ) nzB.code
      (.cons takeB.code (.cons (ofBits w) (.cons (listT acc) (listT (a :: l))))))
      (Gives.id _).tl.hd) (nzB_gives w)
    rcases decw_val w with ⟨h1, h2⟩ | ⟨w', h1, h2⟩
    · have e : bit (decide (KT.val w ≠ 0)) = .nil := by simp [h2, bit]
      rw [e] at hnz
      have h : Gives θ takeB (.cons takeB.code (.cons (ofBits w) (.cons (listT acc) (listT (a :: l)))))
          (.cons (listT acc) (listT (a :: l))) _ :=
        Gives.ite_true (Gives.id _).tl.tl.tl (by simp [listT]) (Gives.ite_false hnz (Gives.id _).tl.tl)
      rw [h2, List.take_zero, List.drop_zero, List.reverse_nil, List.nil_append]
      refine h.mono ?_
      simp only [List.length_nil, zero_add, one_mul]
      omega
    · have e : bit (decide (KT.val w ≠ 0)) ≠ .nil := by
        have : KT.val w ≠ 0 := by omega
        simp [this, bit, one]
      obtain ⟨k, hk, hdw⟩ := DW_some (θ := θ) h1
      have hd : Gives θ (app DW.code (.cons (.quote DW.code) (.hd (.tl .id))))
          (.cons takeB.code (.cons (ofBits w) (.cons (listT acc) (listT (a :: l))))) (ofBits w') (1 + 3 + 1 + 20 * w.length + 2) :=
        Gives.lett (Gives.cons (Gives.quote DW.code _) (Gives.id _).tl.hd)
          ((Does.of_dt hdw).mono hk)
      have hl : w'.length = w.length := length_decw h1
      have ih' := ih w' (a :: acc)
      rw [hl] at ih'
      have r := Does.self ((Gives.id (θ := θ) (.cons takeB.code (.cons (ofBits w) (.cons (listT acc)
        (listT (a :: l)))))).hd.cons (Gives.cons hd (Gives.cons (Gives.cons (Gives.id _).tl.tl.tl.hd
          (Gives.id _).tl.tl.hd) (Gives.id _).tl.tl.tl.tl))) ih'
      have := ((Gives.id (θ := θ) (.cons takeB.code (.cons (ofBits w) (.cons (listT acc) (listT (a :: l)))))).tl.tl.tl.ite_true
        (H := .tl (.tl .id)) (by simp [listT]) (hnz.ite_true (H := .tl (.tl .id)) e r))
      rw [h2, List.take_succ_cons, List.drop_succ_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
      refine this.mono ?_
      simp only [List.length_cons]
      nlinarith

end Take

section Check

/-! ## The names of a value against a budget -/

open Nc.Grp

/-- A budget is a trie: the number at a name, with at most as many digits as the budget is high,
and what subtracting 1 at the name does. -/
theorem Bt.tget_enc (t : Bt) (p : List Bool) : ∃ w, tget p t.enc = ofBits w ∧ w.length ≤ t.ht ∧
    (Bt.dec p t).map Bt.enc = (decw w).map fun w' => tset p (ofBits w') t.enc := by
  induction t generalizing p with
  | none => exact ⟨[], tget_nil p, Nat.zero_le _, by cases p <;> rfl⟩
  | leaf w =>
    cases p with
    | nil => exact ⟨w, rfl, Nat.le_succ _, by rw [Bt.dec, Option.map_map]; rfl⟩
    | cons b p => exact ⟨[], by cases b <;> exact tget_nil p, Nat.zero_le _, rfl⟩
  | node l r ihl ihr =>
    cases p with
    | nil => exact ⟨[], rfl, Nat.zero_le _, rfl⟩
    | cons b p =>
      cases b with
      | true =>
        obtain ⟨w, h1, h2, h3⟩ := ihr p
        refine ⟨w, h1, h2.trans (by simp only [Bt.ht]; omega), ?_⟩
        have := congrArg (Option.map fun e => Tree.cons .nil (.cons l.enc e)) h3
        simpa [Bt.dec, Bt.enc, tset, Function.comp_def] using this
      | false =>
        obtain ⟨w, h1, h2, h3⟩ := ihl p
        refine ⟨w, h1, h2.trans (by simp only [Bt.ht]; omega), ?_⟩
        have := congrArg (Option.map fun e => Tree.cons .nil (.cons e r.enc)) h3
        simpa [Bt.dec, Bt.enc, tset, Function.comp_def] using this

/-- `DW` subtracts 1 from a number, or has no value. -/
theorem DW_does (w : List Bool) : Does θ DW (.cons DW.code (ofBits w))
    ((decw w).toList.map fun w' => (1, ofBits w')) (20 * w.length) := by
  cases h : decw w with
  | none => exact ⟨[], DW_none h, by simp, by simp⟩
  | some w' =>
    obtain ⟨k, hk, hd⟩ := DW_some (θ := θ) h
    exact (Does.of_dt hd).mono hk

/-- A list of trees has at least two nodes for every element. -/
theorem two_len_lt (x : Tree) : 2 * x.len < x.size := by
  induction x with
  | nil => simp [len, Tree.size]
  | cons a b _ ih => simp only [len, Tree.size]; omega

/-- Subtract 1 in a budget at a name; the argument is (the name, the budget). -/
def DC : Fm := lett (.cons .id (app DW.code (.cons (.quote DW.code) (getF (.hd .id) (.tl .id)))))
  (setF (.hd (.hd .id)) (.tl .id) (.tl (.hd .id)))

theorem DC_does {H : ℕ} (x : Tree) {t : Bt} (ht : t.ht ≤ H) : Does θ DC (.cons x t.enc)
    ((Bt.dec x.path t).toList.map fun t' => (1, t'.enc)) (45 * x.size + 20 * H + 70) := by
  obtain ⟨w, h1, h2, h3⟩ := t.tget_enc x.path
  have hg := getF_gives (θ := θ) (Gives.id (.cons x t.enc)).hd (Gives.id _).tl
  rw [hd_cons, tl_cons, h1] at hg
  have h := Does.letk (Does.of_gives (Gives.cons (Gives.quote DW.code _) hg) (DW_does w))
    (R := fun v => [(1, tset x.path v t.enc)]) (d := 60 * x.len + 38) fun q _ =>
      Does.mono (setF_gives (Gives.id (.cons (.cons x t.enc) q.2)).hd.hd (Gives.id _).tl
        (Gives.id _).hd.tl) (by omega)
  refine (h.replace ?_).mono (by have := two_len_lt x; omega)
  cases hd : decw w with
  | none =>
    rw [hd] at h3
    simp [Option.map_eq_none_iff.1 h3, bindW]
  | some w' =>
    rw [hd] at h3
    obtain ⟨t', ht', he⟩ := Option.map_eq_some_iff.1 h3
    simp [ht', he, bindW]

/-- The names in a tree of names, as trees: `names` lists their paths. -/
def nmT : Tree → List Tree
  | .nil => []
  | .cons .nil .nil => []
  | .cons (.cons a b) .nil => nmT a ++ nmT b
  | .cons x (.cons _ _) => [x]

theorem names_eq (o : Tree) : names o = (nmT o).map Tree.path := by
  induction o using names.induct <;> simp [names, nmT, *]

/-- Every name of a tree of names has its nodes in the tree, and four more. -/
theorem sum_nmT_le (o : Tree) : ((nmT o).map fun x => x.size + 4).sum ≤ o.size := by
  induction o using names.induct with
  | case3 a b iha ihb => simp only [nmT, List.map_append, List.sum_append, Tree.size]; omega
  | case4 x u v =>
    have := size_pos u
    have := size_pos v
    simp only [nmT, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Tree.size]
    omega
  | _ => simp [nmT]

/-- Write the names of a tree of names in front of a list; the argument is (this program, (tree,
list)). -/
def flatB : Fm := .ite (.hd (.tl .id))
  (.ite (.tl (.hd (.tl .id))) (.cons (.hd (.hd (.tl .id))) (.tl (.tl .id)))
    (.ite (.hd (.hd (.tl .id)))
      (.run (.hd .id) (.cons (.hd .id) (.cons (.hd (.hd (.hd (.tl .id))))
        (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.hd (.tl .id)))) (.tl (.tl .id))))))))
      (.tl (.tl .id))))
  (.tl (.tl .id))

theorem flatB_gives (o : Tree) (acc : List Tree) :
    Gives θ flatB (.cons flatB.code (.cons o (listT acc))) (listT (nmT o ++ acc))
      (40 * o.size) := by
  induction o using names.induct generalizing acc with
  | case1 => exact ((Gives.id _).tl.hd.ite_false (Gives.id _).tl.tl).mono (by simp [Tree.size])
  | case2 =>
    exact ((Gives.id _).tl.hd.ite_true (by simp) ((Gives.id _).tl.hd.tl.ite_false
      ((Gives.id _).tl.hd.hd.ite_false (Gives.id _).tl.tl))).mono (by simp [Tree.size])
  | case3 a b iha ihb =>
    rw [nmT, List.append_assoc]
    refine Does.mono ((Gives.id _).tl.hd.ite_true (by simp) ((Gives.id _).tl.hd.tl.ite_false
      ((Gives.id _).tl.hd.hd.ite_true (by simp) (Does.self ((Gives.id _).hd.cons
        ((Gives.id _).tl.hd.hd.hd.cons (Does.self ((Gives.id _).hd.cons
          ((Gives.id _).tl.hd.hd.tl.cons (Gives.id _).tl.tl)) (ihb acc)))) (iha _))))) ?_
    simp only [Tree.size]
    omega
  | case4 x u v =>
    rw [nmT]
    refine Does.mono ((Gives.id _).tl.hd.ite_true (by simp) ((Gives.id _).tl.hd.tl.ite_true
      (by simp) (Gives.cons (Gives.id _).tl.hd.hd (Gives.id _).tl.tl))) ?_
    simp only [Tree.size]
    omega

/-- Subtracting 1 at the names of a list, one after the other. -/
theorem foldL_dec (xs : List Tree) (t : Bt) :
    foldL (A := A) (fun x t => (Bt.dec x.path t).toList.map fun t' => (1, t')) xs t =
      (Bt.decAll (xs.map Tree.path) t).toList.map fun t' => (1, t') := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    rw [foldL, List.map_cons, Bt.decAll]
    cases Bt.dec x.path t with
    | none => rfl
    | some t' => simpa [bindW_single] using ih t'

/-- Check that all numbers of a budget are 0; the argument is (this program, the budget). -/
def AZ : Fm := .ite (.tl .id)
  (.ite (.tl (.tl .id))
    (.cons (.run (.hd .id) (.cons (.hd .id) (.hd (.tl (.tl .id)))))
      (.run (.hd .id) (.cons (.hd .id) (.tl (.tl (.tl .id))))))
    (.ite (app nzB.code (.cons (.quote nzB.code) (.hd (.tl .id)))) .fail (.quote .nil)))
  (.quote .nil)

/-- The value of `AZ` at a budget whose numbers are 0. -/
def Bt.zo : Bt → Tree
  | .node l r => .cons l.zo r.zo
  | _ => .nil

theorem AZ_does (t : Bt) : Does θ AZ (.cons AZ.code t.enc)
    (if t.zero then [(1, t.zo)] else []) (40 * t.nds) := by
  induction t with
  | none => exact ((Gives.id _).tl.ite_false (Gives.quote .nil _)).mono (by simp [Bt.nds])
  | leaf w =>
    have hn := Gives.lett (Gives.cons (Gives.quote (θ := θ) nzB.code
      (.cons AZ.code (Bt.leaf w).enc)) (Gives.id _).tl.hd) (nzB_gives w)
    refine Does.mono (Does.ite_true (Gives.id _).tl (by simp [Bt.enc])
      (Does.ite_false (Gives.id _).tl.tl ?_)) (?_ : 2 + (3 + (20 * w.length + 19) + 1) + 1 ≤ _)
    · by_cases hz : KT.val w = 0
      · rw [show bit (decide (KT.val w ≠ 0)) = .nil by simp [hz, bit]] at hn
        rw [Bt.zero, if_pos ((all_not_iff w).2 hz)]
        exact (hn.ite_false (Gives.quote .nil _)).mono (by omega)
      · rw [Bt.zero, if_neg (mt (all_not_iff w).1 hz)]
        exact (Does.ite_true hn (by simp [hz, bit, one]) (Does.fail _)).mono (by omega)
    · simp only [Bt.nds]
      omega
  | node l r ihl ihr =>
    refine ((Does.ite_true (Gives.id _).tl (by simp [Bt.enc]) (Does.ite_true (Gives.id _).tl.tl
      (by simp [Bt.enc]) (Does.cons (Does.self ((Gives.id _).hd.cons (Gives.id _).tl.tl.hd) ihl)
        (Does.self ((Gives.id _).hd.cons (Gives.id _).tl.tl.tl) ihr)))).replace ?_).mono ?_
    · rw [Bt.zero]
      cases l.zero <;> cases r.zero <;> simp [Bt.zo]
    · simp only [Bt.nds]
      omega

/-- Subtract 1 in a budget at all names of a tree of names, and check that nothing is left. The
argument is ((program, (argument, budget)), tree of names). -/
def CK : Fm := lett (.cons (.quote AZ.code) (foldF DC (.tl (.tl (.hd .id)))
  (app flatB.code (.cons (.quote flatB.code) (.cons (.tl .id) (.quote .nil)))))) AZ

/-- `CK` has a value if the names of `o` use up the budget `t`. The time `(60 H + 41) |o|`: 40 per
node to list the names, and for a name `x` at most `45 |x| + 20 H + 100`, which is at most
`(60 H + 1) (|x| + 4)` if `H` is not 0. -/
theorem CK_does {H : ℕ} (a o : Tree) {t : Bt} (ha : a.tl.tl = t.enc) (ht : t.ht ≤ H + 1) :
    Does θ CK (.cons a o) (bindW ((Bt.decAll (names o) t).toList.map fun t' => (1, t'))
      fun t' => if t'.zero then [(1, t'.zo)] else [])
      ((60 * (H + 1) + 41) * o.size + 40 * t.nds + 36) := by
  have hl := Gives.lett (Gives.cons (Gives.quote (θ := θ) flatB.code (.cons a o))
    (Gives.cons (Gives.id _).tl (Gives.quote (listT []) _))) (flatB_gives o [])
  rw [List.append_nil] at hl
  have hf := foldT (encE := id) (enc := Bt.enc)
    (f := fun x t => (Bt.dec x.path t).toList.map fun t' => (1, t'))
    (Inv := fun _ t => t.ht ≤ H + 1) (d := fun x => 45 * x.size + 20 * (H + 1) + 70)
    (ha ▸ (Gives.id (θ := θ) (.cons a o)).hd.tl.tl) (by rwa [List.map_id])
    (fun x _ s _ hs => ⟨(DC_does x hs).replace (by rw [List.map_map]; rfl), fun q hq => by
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hq
      rw [(Bt.ht_nds_dec (Option.mem_toList.1 ht')).1]
      exact hs⟩) ht
  rw [foldL_dec, ← names_eq] at hf
  have hc := (Does.cons (Gives.quote (θ := θ) AZ.code (.cons a o)) hf).replace
    (Q' := ((Bt.decAll (names o) t).toList.map fun t' => ((1 : A), t')).map
      (Prod.map id fun t' => .cons AZ.code t'.enc)) (by
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
        refine List.map_congr_left fun q _ => ?_
        simp [Prod.map])
  refine (Does.lettT hc (d := 40 * t.nds) fun b hb => ?_).mono ?_
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hb
    rw [← (Bt.ht_nds_decAll (Option.mem_toList.1 ht')).2]
    exact AZ_does t'
  · have key : ((nmT o).map fun x => 45 * x.size + 20 * (H + 1) + 70 + 30).sum ≤
        (60 * (H + 1) + 1) * o.size := by
      calc _ ≤ ((nmT o).map fun x => (60 * (H + 1) + 1) * (x.size + 4)).sum :=
            List.sum_le_sum fun x _ => by
              have e : (60 * (H + 1) + 1) * (x.size + 4) = 45 * x.size + 20 * (H + 1) + 100 +
                  (60 * (H * x.size) + 16 * x.size + 220 * H + 124) := by ring
              omega
        _ = (60 * (H + 1) + 1) * ((nmT o).map fun x => x.size + 4).sum := by
            rw [List.sum_map_mul_left]
        _ ≤ _ := Nat.mul_le_mul_left _ (sum_nmT_le o)
    have e : (60 * (H + 1) + 41) * o.size = (60 * (H + 1) + 1) * o.size + 40 * o.size := by ring
    omega

/-- Apply a program; then check that the names in its value use up the budgets. The argument is
(program, (argument, budgets)). -/
def WN : Fm := lett (.cons .id (.run (.hd .id) (.hd (.tl .id)))) CK

/-- The plain instance for a program `p`, an argument `z` and budgets `t`. -/
def zq (p z : Tree) (t : Bt) : Tree := .cons WN.code (.cons p (.cons z t.enc))

/-- **Postponing**: the instances that arise from budgets are plain, and their sums are those of
the runs that use up the budgets. The time `(60 H + 42) T`: `T` for the program, and `60 H + 41`
per node of its value (`CK_does`), which has at most `T` nodes too. -/
theorem zq_plain {p z : Tree} {l : List (Run A)} (h : Ev θ (Fm.ofTree p) z l) {T H τ : ℕ}
    (hT : ∀ r ∈ l, r.cost + r.out.size ≤ T) {t : Bt} (ht : t.ht ≤ H + 1)
    (hτ : (60 * (H + 1) + 42) * T + 40 * t.nds + 80 ≤ τ) :
    Plain θ τ (zq p z t) ∧
      pv θ (zq p z t) = (l.map fun r => if ok t (names r.out) = true then r.th else 0).sum := by
  have hw := Does.letk (Does.run (Gives.id (θ := θ) (.cons p (.cons z t.enc))).hd
      (Gives.id _).tl.hd (Does.of_ev h fun r hr => (Nat.le_add_right _ _).trans (hT r hr)))
    (R := fun o => bindW ((Bt.decAll (names o) t).toList.map fun t' => (1, t'))
      fun t' => if t'.zero then [(1, t'.zo)] else [])
    (d := (60 * (H + 1) + 41) * T + 40 * t.nds + 36) fun q hq => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
      refine (CK_does _ r.out rfl ht).mono ?_
      have := Nat.mul_le_mul_left (60 * (H + 1) + 41) ((Nat.le_add_left _ _).trans (hT r hr))
      omega
  obtain ⟨h1, h2⟩ := (hw.mono (d := τ) (by
    have e : (60 * (H + 1) + 42) * T = (60 * (H + 1) + 41) * T + T := by ring
    omega)).plain
  refine ⟨h1, h2.trans ?_⟩
  rw [show ∀ Q : List (A × Tree), (Q.map Prod.fst).sum = wsum Q fun _ => 1 from
    fun Q => by simp [wsum], wsum_bindW, wsum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
  rw [Function.comp_apply, wsum_bindW, ok]
  cases Bt.decAll (names r.out) t with
  | none => simp
  | some t' => cases hz : t'.zero <;> simp [hz]

end Check

end NS1
