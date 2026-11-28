/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Budget

/-!
# Runs without guesses; subtracting 1 from a number

`DW` subtracts 1 from a number in binary. With it `WN` (`NS1/Check.lean`) checks the names in the
value of a program against a budget.
-/

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- A branch whose test is not `nil` takes the first arm; `o ≠ .nil` comes last and defaults to
`by simp`. -/
theorem Dt.ite_true {a b c : Fm} {x o p : Tree} {k j : ℕ} (ha : Dt θ a x o k) (hb : Dt θ b x p j)
    (ho : o ≠ .nil := by simp) : Dt θ (.ite a b c) x p (k + 1 + j) := Ev.ite_true (c := c) ha ho hb

theorem Dt.ite_false {a b c : Fm} {x p : Tree} {k j : ℕ} (ha : Dt θ a x .nil k) (hc : Dt θ c x p j) :
    Dt θ (.ite a b c) x p (k + 1 + j) := Ev.ite_false (b := b) ha hc

theorem Dt.run {a b B : Fm} {x d o : Tree} {k j i : ℕ} (ha : Dt θ a x B.code k) (hb : Dt θ b x d j)
    (h : Dt θ B d o i) : Dt θ (.run a b) x o (k + j + 1 + i) := by
  rw [← Fm.ofTree_code B] at h
  exact Ev.run_det ha hb h

/-- `Ev.ite_true` with no runs; `o ≠ .nil` comes last and defaults to `by simp`. -/
theorem Ev.ite_true_nil {a b c : Fm} {x o : Tree} {k : ℕ} (ha : Dt θ a x o k) (hb : Ev θ b x [])
    (ho : o ≠ .nil := by simp) : Ev θ (.ite a b c) x [] := Ev.ite_true (c := c) ha ho hb

theorem Ev.ite_false_nil {a b c : Fm} {x : Tree} {k : ℕ} (ha : Dt θ a x .nil k)
    (hc : Ev θ c x []) : Ev θ (.ite a b c) x [] := Ev.ite_false (b := b) ha hc

theorem Ev.run_nil {a b B : Fm} {x d : Tree} {k j : ℕ} (ha : Dt θ a x B.code k) (hb : Dt θ b x d j)
    (h : Ev θ B d []) : Ev θ (.run a b) x [] := by
  rw [← Fm.ofTree_code B] at h
  exact Ev.run_det ha hb h

theorem Ev.cons_nil_right {a b : Fm} {x : Tree} {l : List (Run A)} (ha : Ev θ a x l) (hb : Ev θ b x []) :
    Ev θ (.cons a b) x [] := by
  have := Ev.cons ha hb
  have e : (l.flatMap fun r => ([] : List (Run A)).map fun s => (r.seq s).tick (.cons r.out s.out)) = [] :=
    List.flatMap_eq_nil_iff.2 fun _ _ => rfl
  rw [e] at this
  exact this

section Programs

-- The encoding of words: the branch tests of the program below.
attribute [local simp] ofBits

/-- Subtract 1 from a number; the argument is (this program, the number). -/
def DW : Fm := .ite (.tl .id)
  (.ite (.hd (.tl .id)) (.cons (.quote .nil) (.tl (.tl .id)))
    (.cons (.quote one) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id)))))) .fail

theorem DW_some {w w' : List Bool} (h : decw w = some w') :
    ∃ k ≤ 20 * w.length, Dt θ DW (.cons DW.code (ofBits w)) (ofBits w') k := by
  induction w generalizing w' with
  | nil => simp [decw] at h
  | cons b w ih =>
    cases b with
    | true =>
      simp only [decw, Option.some.injEq] at h
      subst h
      refine ⟨_, ?_, Dt.ite_true (.tl (.id _)) (Dt.ite_true (.hd (.tl (.id _)))
        (.cons (.quote _ _) (.tl (.tl (.id _)))) (by simp [bit, one]))⟩
      simp only [List.length_cons]
      omega
    | false =>
      simp only [decw, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      obtain ⟨k, hk, hd⟩ := ih hv
      refine ⟨_, ?_, Dt.ite_true (.tl (.id _)) (Dt.ite_false (.hd (.tl (.id _)))
        (.cons (.quote _ _) (.run (.hd (.id _)) (.cons (.hd (.id _)) (.tl (.tl (.id _)))) hd)))⟩
      simp only [List.length_cons]
      omega

theorem DW_none {w : List Bool} (h : decw w = none) : Ev θ DW (.cons DW.code (ofBits w)) [] := by
  induction w with
  | nil => exact Ev.ite_false_nil (.tl (.id _)) (.fail _)
  | cons b w ih =>
    cases b with
    | true => simp [decw] at h
    | false =>
      simp only [decw, Option.map_eq_none_iff] at h
      exact Ev.ite_true_nil (.tl (.id _)) (Ev.ite_false_nil (.hd (.tl (.id _)))
        (Ev.cons_nil_right (.quote _ _) (Ev.run_nil (.hd (.id _))
          (.cons (.hd (.id _)) (.tl (.tl (.id _)))) (ih h))))

end Programs

end NS1
