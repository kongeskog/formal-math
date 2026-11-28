/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Util

/-!
# The paper, section "One scale is all scales": constants are postponed
-/

namespace Paper

open NS1
open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- The instance z_e of the paper: run p on the argument and accept exactly the runs whose value
names each constant the prescribed number of times. -/
def postponed (p z : Tree) (e : Bt) : Tree := zq p z e

/-- **Paper: Lemma lem:postpone.** "Let all runs of a program p on an argument halt, the accepting
ones within T < 2^J steps and with names among the leaves of a binary trie with Q′ nodes and height
η; let its leaves stand for powers λ_1, λ_2, … Its value is ∑_e λ^e sum(z_e) over the vectors e with
one entry in {0, …, 2^J−1} for every leaf, where the instance z_e accepts exactly the runs of p that
use each name the prescribed number of times. It is plain within O(T(J + η + 1) + Q′J) steps." Here
a run names its constants in its value, and `T` bounds its cost and the size of its value together.
The trie is L and L.budg J lists the exponent vectors e with their λ^e. "Accepts exactly" enters
through the sums: pv(z_e) is the sum of the weights of the runs of p with ok e (names of the value)
(every counter of e is 0 after the names), by `zq_plain`. The size of z_e is read off its
definition where it is needed. -/
theorem lem_postpone (p z : Tree) {T J : ℕ} (hJ : T < 2 ^ J) (hh : Hl θ (Fm.ofTree p) z)
    (hc : ∀ r ∈ evl θ (Fm.ofTree p) z, r.cost + r.out.size ≤ T) (L : KT R) (κ : List Bool → R)
    (hκ : ∀ r ∈ evl θ (Fm.ofTree p) z, ∀ n ∈ names r.out, κ n = L.lookup n) :
    val κ (evl θ (Fm.ofTree p) z) = ((L.budg J).map fun e => e.2 * algebraMap A R (pv θ (postponed p z e.1))).sum ∧
      ∀ e ∈ L.budg J,
        Plain θ ((60 * (L.ht + J + 1) + 42) * T + 40 * (L.nds * (J + 1)) + 80) (postponed p z e.1) := by
  have hp := fun e (he : e ∈ L.budg J) => zq_plain hh.ev hc (KT.ht_nds_budg he).1
    (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 40 (KT.ht_nds_budg he).2) _) 80)
  refine ⟨?_, fun e he => (hp e he).1⟩
  rw [val_eq_sum_budg (J := J) (K := L) (fun r hr => lt_of_le_of_lt ((length_names_le r.out).trans
    (by have := hc r hr; omega)) hJ) hκ]
  refine congrArg List.sum (List.map_congr_left fun e he => ?_)
  rw [← (hp e he).2]
  rfl

end Paper
