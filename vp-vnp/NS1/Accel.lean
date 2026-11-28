/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Step

/-!
# Accelerators, the cut

Scales are `v ^ H` (`H = 16 / η`). `pv θ z` is the universal plain sum at `z = (program, argument)`.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {R : Type} [CommRing R] [Algebra A R]

/-- The number of binary digits. -/
def lg (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- The program `z.hd` at the argument `z.tl`: all runs stop, the accepting ones within `T` steps.
-/
def Plain (θ : List Bool → A) (T : ℕ) (z : Tree) : Prop :=
  Hl θ (Fm.ofTree z.hd) z.tl ∧ ∀ r ∈ evl θ (Fm.ofTree z.hd) z.tl, r.cost ≤ T

/-- The universal plain sum: the sum of the weights of all accepting runs of the program `z.hd` at `z.tl`. -/
noncomputable def pv (θ : List Bool → A) (z : Tree) : A := pval (evl θ (Fm.ofTree z.hd) z.tl)

/-- A program `G` that cuts plain sums of `τ` steps on instances of size `s` into pieces of `v ^ H` steps. Its values
are lists of instances. -/
structure CutProg (θ : List Bool → A) (H v τ s : ℕ) (G : Tree) : Prop where
  size : G.size ≤ v ^ H
  list : ∀ z, z.size ≤ s → Hl θ (Fm.ofTree G) z ∧ ∀ r ∈ evl θ (Fm.ofTree G) z, r.cost * v ^ 24 ≤ τ ∧
    r.out.toList.length * v ^ H ≤ τ * v ^ 2 ∧ ∀ y ∈ r.out.toList, y.size ≤ v ^ (H - 32)
  val : ∀ z, z.size ≤ s → Plain θ τ z →
    (∀ r ∈ evl θ (Fm.ofTree G) z, ∀ y ∈ r.out.toList, Plain θ (v ^ H) y) ∧
    pv θ z = ((evl θ (Fm.ofTree G) z).map fun r => r.th * (r.out.toList.map (pv θ)).prod).sum

/-- **Theorem C (the cut, at all scales)**, as a property of the ring and its constants. -/
def CutHyp (θ : List Bool → A) (H C₀ v₀ : ℕ) : Prop :=
  ∀ v, v₀ ≤ v → ∀ α τ s, lg v ^ (C₀ * α) ≤ v → v ^ H ≤ τ → τ ≤ v ^ (H * α) → s * v ^ 48 ≤ τ →
    ∃ G, CutProg θ H v τ s G

/-- The program `D`, with the constants `K` and their powers `2 ^ b`, `b < B`, has the values of all
universal plain sums of `v ^ H` steps on instances of size `v ^ (H - 32)`; the cost and the size of
the value of a run are at most `t` together, and the value names constants of `K`. -/
structure IsAccT (θ : List Bool → A) (H v t : ℕ) (K : KT R) (B : ℕ) (D : Tree) : Prop where
  run : ∀ z, z.size ≤ v ^ (H - 32) → Hl θ (Fm.ofTree D) z ∧ ∀ r ∈ evl θ (Fm.ofTree D) z,
      r.cost + r.out.size ≤ t ∧
    ∀ p ∈ names r.out, K.InB B p
  val : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
    val K.lk (evl θ (Fm.ofTree D) z) = algebraMap A R (pv θ z)

variable {θ : List Bool → A}

/-- The universal program: it runs the program `z.hd` at `z.tl`, and its value is empty, so that it
names no constants. -/
def UF : Fm := .tl (.cons (.run (.hd .id) (.tl .id)) (.quote .nil))

theorem UF_ev {z : Tree} {l : List (Run A)} (h : Ev θ (Fm.ofTree z.hd) z.tl l) :
    Ev θ UF z (l.map fun r => ⟨r.cost + 8, r.th, .nil⟩) := by
  have := Ev.tl (Ev.cons (Ev.run_det (Dt.hd (Dt.id z)) (Dt.tl (Dt.id z)) h) (Ev.quote .nil z))
  simp only [List.map_cons, List.map_nil, flatMap_single, List.map_map] at this
  refine Eq.mp ?_ this
  congr 1
  refine List.map_congr_left fun r _ => ?_
  simp [Run.delay, Run.seq, Run.tick, Run.det]
  omega

end NS1
