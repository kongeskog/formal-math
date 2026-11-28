/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Lists

/-!
# Words of trees, parts of lists, choices, straight-line programs
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

section Picks

end Picks

end NS1
