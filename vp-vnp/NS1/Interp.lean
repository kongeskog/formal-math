/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Budget

/-!
# Runs without guesses; subtracting 1 from a number

`DW` subtracts 1 from a number in binary. With it `WN` (`NS1/Util.lean`) checks the names in the
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

/-- Subtract 1 from a number; the argument is (this program, the number). -/
def DW : Fm := .ite (.tl .id)
  (.ite (.hd (.tl .id)) (.cons (.quote .nil) (.tl (.tl .id)))
    (.cons (.quote one) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id)))))) .fail

end NS1
