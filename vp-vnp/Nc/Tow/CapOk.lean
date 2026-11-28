/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Cap
import Nc.Tow.Ok
import Nc.Tow.Tree

/-!
# The tower plan: rules, numbers of units of the tree
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b J m Uu AA A' U0 U1 : ℕ} {T : Tower h b J} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}

theorem lev_eq (L : Tg T m AA → ℕ) (j : Fin (J + 1)) : lev L j.1 = fun e => L (.edge j e) := by
  funext e
  unfold lev
  rw [dif_pos j.2]

section

variable (hH : THypR FL)

include hH

/-- **The plan obeys the rules.** -/
theorem plan_ok_cap : (plan R FL Pl lhat U0 U1).Ok (capN FL U0 Uu AA lhat) :=
  plan_ok fun n _ mv => num_le_cap hH
    (fun a c => Nat.le_of_lt_succ (n a c).2) mv

variable {n : Fin AA → Fin AA → ℕ} {o : NM R ch FL → ℕ}

/-- All units of the tree. -/
theorem sum_fb_le :
    ∑ i ∈ range (J + 1), ∑ c, fb (lev (load lhat n o)) i c ≤ 4 * (h * kbar FL Uu AA lhat) := by
  rw [Finset.sum_range]
  refine le_trans (le_of_eq ?_) (sum_bet_le (R := R) (ch := ch) (lhat := lhat) (n := n) (o := o) hH)
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
  unfold fb
  rw [lev_eq]
  rfl

/-- Units between a node and its parent, with the gain `g` of the tower. -/
theorem fb_mul_le {q g : ℕ} (hq : 2 ≤ q) (hb : b ≤ 2 ^ q) (hg : g ^ q ≤ Fintype.card (T.X 0))
    (j : ℕ) (hj : j ≤ J) (c : T.X j) :
    fb (lev (load lhat n o)) j c * g ≤ h * kbar FL Uu AA lhat := by
  refine le_trans (le_of_eq ?_) (bet_mul_le (R := R) (ch := ch) (lhat := lhat) (n := n) (o := o) hH hq hb hg
    ⟨j, Nat.lt_succ_of_le hj⟩ c)
  unfold fb
  have := lev_eq (load lhat n o) ⟨j, Nat.lt_succ_of_le hj⟩
  rw [this]
  rfl

end

end Nc.Tow
