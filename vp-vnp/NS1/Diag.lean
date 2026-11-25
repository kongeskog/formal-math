/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Scale
import Nc.Acc.CompK

/-!
# The diagonal, over a finite ring

Over a finite ring a program can have the value 1 + its own value, if there is an accelerator at a scale that is
large against the ring and the number of constants.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- 1 + the value of the argument applied to itself. -/
def diagF (D : Tree) (g : Fm) : Fm := .ite .guess (.quote .nil) (guessF g (app D (ZE (.hd .id))))

/-- If `g` guesses the budgets `q.1` with names whose constants multiply to `q.2` and `D` has the
value `ω` at the plain instances `zq z z q.1`, then the value of `diagF D g` is `1` plus the sum
over the guesses of `q.2` times that value. -/
theorem diagF_kv {κ : List Bool → R} {S : Set (List Bool)} {D z : Tree} {g : Fm}
    {cg tD : ℕ} {lg : List (Run A)}
    {Q : List (Bt × R)} {ω : Tree → R} (hg : Ev θ g z lg) (rg : List.Forall₂ (RelG κ
        (· ∈ S) cg) lg Q)
    (hD : ∀ q ∈ Q, KV θ κ S (Fm.ofTree D) (zq z z q.1) (ω (zq z z q.1)) tD) :
    KV θ κ S (diagF D g) z (1 + (Q.map fun q => q.2 * ω (zq z z q.1)).sum) (2 * cg + tD + 30) := by
  have h1 := KV.gives (κ := κ) (S := S) (Gives.quote (θ := θ) .nil z) (by simp [names])
  have h2 := guess_kv (B := app D (ZE (.hd .id))) (ω :=
      fun e => ω (.cons WN.code (.cons z (.cons z e)))) hg rg
    fun q hq u hu => by
      have hZ : Gives θ (ZE (.hd .id)) (.cons z u) (zq z z q.1) 11 := by
        simpa [zq, ZE, hu] using (Gives.quote (θ := θ) WN.code (.cons z u)).cons
          ((Gives.id _).hd.cons ((Gives.id _).hd.cons (Gives.id _).tl.hd))
      exact KV.app_gives hZ (hD q hq)
  refine ((KV.either h1 h2).mono ?_).congr (by simp [names, zq])
  simp only [Tree.size]
  omega

end NS1
