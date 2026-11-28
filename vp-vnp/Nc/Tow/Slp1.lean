/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Slp0
import Nc.Tow.Plan
import Nc.Tow.Load3

/-!
# The program of the tower plan: bounds, loads from numbers of units
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Unc

variable {F : Type} [CommRing F] {h b J m Uu AA A' U0 U1 : ℕ} {T : Tower h b J}

variable (R : Routes T m Uu) (ch : Fin AA ↪ T.X 0) (FL : FlagLaws F T)

/-- A bound for all loads. -/
noncomputable def Wb (U0 U1 : ℕ) : ℕ := AA * AA * U0 + Fintype.card (NM R ch FL) * U1

/-- Bounds for the program. -/
structure Bnd (U0 U1 Y : ℕ) : Prop where
  aa : AA * AA ≤ Y
  w : Wb R ch FL U0 U1 ≤ Y
  nm : Fintype.card (NM R ch FL) ≤ Y
  mv : Fintype.card (Mv R ch FL) ≤ Y
  tg : Fintype.card (Tg T m AA) ≤ Y
  nd : Fintype.card (Nd T) ≤ Y
  fl : Fintype.card (Sym2 T.Fl) ≤ Y
  di : Fintype.card FL.Di ≤ Y
  h : h ≤ Y
  j : J + 1 ≤ Y
  t : tend J m ≤ Y
  tt : b * Fintype.card (Sym2 T.Fl) * Wb R ch FL U0 U1 + 2 ≤ Y

variable {R ch FL}

namespace Bnd

variable {Y : ℕ} (hB : Bnd R ch FL U0 U1 Y)
include hB

theorem u0 (a : Fin AA) : U0 ≤ Y := by
  have h1 := hB.w
  unfold Wb at h1
  have h2 : 0 < AA * AA := Nat.mul_pos (Fin.pos a) (Fin.pos a)
  have h3 : U0 ≤ AA * AA * U0 := Nat.le_mul_of_pos_left _ h2
  omega

theorem u1 (ν : NM R ch FL) : U1 ≤ Y := by
  have h1 := hB.w
  unfold Wb at h1
  have h2 : 0 < Fintype.card (NM R ch FL) := Fintype.card_pos_iff.2 ⟨ν⟩
  have h3 : U1 ≤ Fintype.card (NM R ch FL) * U1 := Nat.le_mul_of_pos_left _ h2
  omega

theorem aa1 : AA ≤ Y := by
  have h1 := hB.aa
  rcases Nat.eq_zero_or_pos AA with h0 | h0
  · omega
  · exact (Nat.le_mul_of_pos_left _ h0).trans h1

theorem ed (j : Fin (J + 1)) : Fintype.card (T.Ed j) ≤ Y := by
  refine (Fintype.card_le_of_injective (fun e : T.Ed j => (Tg.edge j e : Tg T m AA)) ?_).trans hB.tg
  intro e e' he
  injection he

end Bnd

section Bounds

variable {lhat : ℕ} {n : Fin AA → Fin AA → ℕ} {o : NM R ch FL → ℕ}

theorem bt_le (hn : ∀ a c, n a c ≤ U0) (τ : Tg T m AA) : bt R ch lhat n τ ≤ AA * AA * U0 := by
  unfold bt
  split_ifs
  · calc _ ≤ ∑ _a : Fin AA, ∑ _c : Fin AA, U0 := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => ?_
          refine (card_filter_le _ _).trans ?_
          rw [card_range]
          exact hn a c
      _ = AA * AA * U0 := by simp; ring
  · exact Nat.zero_le _

theorem ld_le (hn : ∀ a c, n a c ≤ U0) (ho : ∀ ν, o ν ≤ U1) (N : Mv R ch FL → ℕ) (τ : Tg T m AA) :
    ld lhat n o N τ ≤ Wb R ch FL U0 U1 := by
  unfold ld Wb
  refine add_le_add (bt_le hn τ) ?_
  refine (Finset.sum_le_card_nsmul _ _ U1 fun ν _ => ?_).trans (by simp)
  split_ifs
  · exact (alvN_le _ _).trans (ho ν)
  · exact Nat.zero_le _

theorem fits_mono {L : Tg T m AA → ℕ} {l : LMv FL} {s t : ℕ} (hst : s ≤ t) (hs : Fits L l s) :
    Fits L l t := fun q hq => (hs q hq).trans (Nat.mul_le_mul_left _ hst)

/-- The number of units at a vertex is not large. -/
theorem tmin_lt {L : Tg T m AA → ℕ} (hL : ∀ τ, L τ ≤ Wb R ch FL U0 U1) (l : LMv FL) :
    tmin L l < b * Fintype.card (Sym2 T.Fl) * Wb R ch FL U0 U1 + 2 := by
  have h1 := FL.L1 (fun q => L (.seg l.1 l.2.1 l.2.2.1 q))
    (b * Fintype.card (Sym2 T.Fl) * Wb R ch FL U0 U1) (by
    calc _ ≤ b ^ 2 * ∑ _q : Sym2 T.Fl, Wb R ch FL U0 U1 ^ 2 :=
          Nat.mul_le_mul_left _ (Finset.sum_le_sum fun q _ => Nat.pow_le_pow_left (hL _) 2)
      _ = b ^ 2 * (Fintype.card (Sym2 T.Fl) * Wb R ch FL U0 U1 ^ 2) := by simp
      _ ≤ b ^ 2 * (Fintype.card (Sym2 T.Fl) ^ 2 * Wb R ch FL U0 U1 ^ 2) := by
          gcongr
          exact Nat.le_self_pow two_ne_zero _
      _ = (b * Fintype.card (Sym2 T.Fl) * Wb R ch FL U0 U1) ^ 2 := by ring
      _ ≤ (FL.a₁ * (b * Fintype.card (Sym2 T.Fl) * Wb R ch FL U0 U1)) ^ 2 :=
          Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ FL.a₁_pos) 2
      _ ≤ _ := Nat.le_mul_of_pos_left _ two_pos)
  have h2 := Nat.sInf_le (s := {t | ∃ d, Fits L (withD l d) t}) h1
  change tmin L l ≤ _ at h2
  omega

/-- The number of units at a vertex, as a sum. -/
theorem tmin_sum {L : Tg T m AA → ℕ} {l : LMv FL} {B : ℕ} (hlt : tmin L l < B) :
    tmin L l = ∑ s ∈ range B, ind (fun _ : Unit => ¬ ∃ d, Fits L (withD l d) s) () := by
  classical
  have h1 : ∀ s, (ind (fun _ : Unit => ¬ ∃ d, Fits L (withD l d) s) ()) = if s <
      tmin L l then 1 else 0 := by
    intro s
    by_cases hs : s < tmin L l
    · rw [if_pos hs, ind_true]
      intro hd
      have h3 : tmin L l ≤ s := Nat.sInf_le hd
      omega
    · rw [if_neg hs, ind_false]
      intro hn
      obtain ⟨d, hd⟩ := tmin_spec L l
      exact hn ⟨d, fits_mono (not_lt.1 hs) hd⟩
  rw [Finset.sum_congr rfl fun s _ => h1 s, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  have h2 : (range B).filter (fun s => s < tmin L l) = range (tmin L l) := by
    ext s
    simp only [mem_filter, mem_range]
    omega
  rw [h2, card_range]

end Bounds

end Nc.Tow
