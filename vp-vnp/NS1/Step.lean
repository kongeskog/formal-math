/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Guess

/-!
# Applying a fixed program; the plain instance of a budget
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

section App

/-- Apply a fixed program. -/
def app (p : Tree) (e : Fm) : Fm := .run (.quote p) e

theorem Ev.app {p x : Tree} {e : Fm} {le : List (Run A)} (he : Ev θ e x le)
    (h : ∀ s ∈ le, Hl θ (Fm.ofTree p) s.out) : Ev θ (app p e) x
      (le.flatMap fun s => (NS1.evl θ (Fm.ofTree p) s.out).map fun t => ((Run.det 1 p).seq s).seq t |>.tick t.out) := by
  have := Ev.run' (Dt.quote (θ := θ) p x) he (fun r hr s hs => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact h s hs)
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
  exact this

theorem mem_app {p : Tree} {le : List (Run A)} {u : Run A}
    (h : u ∈ le.flatMap fun s => (NS1.evl θ (Fm.ofTree p) s.out).map fun t =>
      ((Run.det 1 p).seq s).seq t |>.tick t.out) :
    ∃ s ∈ le, ∃ t ∈ NS1.evl θ (Fm.ofTree p) s.out, u.cost = s.cost + t.cost + 2 ∧ u.out = t.out ∧
      u.th = s.th * t.th := by
  rw [List.mem_flatMap] at h
  obtain ⟨s, hs, h⟩ := h
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  refine ⟨s, hs, t, ht, ?_, rfl, ?_⟩
  · simp only [Run.seq, Run.tick, Run.det]
    omega
  · simp [Run.seq, Run.tick, Run.det]

end App

/-- Apply the program `D` to all trees of a list, and join the names of the values. The argument is
(this program, the list). -/
def LP (D : Tree) : Fm := .ite (.tl .id)
  (node (.run (.quote D) (.hd (.tl .id))) (.run (.hd .id)
      (.cons (.hd .id) (.tl (.tl .id))))) (.quote .nil)

/-- The plain instance for a program `p`, an argument `z` and budgets `t`. -/
def zq (p z : Tree) (t : Bt) : Tree := .cons WN.code (.cons p (.cons z t.enc))

end NS1
