/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Ends
import Nc.Tow.Rank

/-!
# The tower plan
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b J m Uu AA A' U0 U1 : ℕ} {T : Tower h b J} (R : Routes T m Uu)
  {ch : Fin AA ↪ T.X 0} (FL : FlagLaws F T) (Pl : Place T ch A') (lhat : ℕ)

/-- Units. -/
abbrev Un (U0 U1 : ℕ) := Uid AA U0 (sys R FL Pl).N U1

/-- Numbers of initial units. -/
def nn (n : Fin AA → Fin AA → Fin (U0 + 1)) : Fin AA → Fin AA → ℕ := fun a c => (n a c).1

variable {R FL Pl}

/-- Outcomes. -/
noncomputable def oo (o : (sys R FL Pl).N → Fin U1) : NM R ch FL → ℕ := fun ν => (o (eN.symm ν)).1

/-- The target of a unit. -/
noncomputable def tgU : Un R FL Pl U0 U1 → Tg T m AA
  | .init a c k => tgB R ch a c k
  | .new ν _ => tgM (eN ν).1 (eN ν).2

variable (n : Fin AA → Fin AA → Fin (U0 + 1)) (o : (sys R FL Pl).N → Fin U1)

/-- Alive units. -/
def AlU : Un R FL Pl U0 U1 → Prop
  | .init a c k => Valid lhat (nn n) ∧ k.1 < (n a c).1
  | .new ν k => k.1 < alv lhat (nn n) (oo o) (eN ν)

open Classical in
/-- The set of alive units. -/
noncomputable def Al : Finset (Un R FL Pl U0 U1) := univ.filter (AlU lhat n o)

/-- The enumeration of units. -/
noncomputable def ix (u : Un R FL Pl U0 U1) : ℕ := (Fintype.equivFin (Un R FL Pl U0 U1) u).1

/-- The rank of an alive unit among those with the same target. -/
noncomputable def rkU (u : Un R FL Pl U0 U1) : ℕ := rk (ix) (tgU) (Al lhat n o) u

/-- The number of a slot among those of its pair. -/
noncomputable def su (d : FL.Di) (e : (FL.L d).Sl) : ℕ :=
  rk (fun e => (Fintype.equivFin (FL.L d).Sl e).1) (pr d) univ e

open Classical in
/-- The units given at a slot. -/
noncomputable def consM : ZM R ch FL → Finset (Un R FL Pl U0 U1)
  | ⟨.inl x, _⟩ => if ActR (load lhat (nn n) (oo o)) x.1 then
      (Al lhat n o).filter fun u => tgU u = inpR x.1 else ∅
  | ⟨.inr l, e⟩ => if Pick (load lhat (nn n) (oo o)) l then
      (Al lhat n o).filter fun u => tgU u = .seg l.1 l.2.1 l.2.2.1 (pr l.2.2.2 e) ∧
        su l.2.2.2 e * num lhat (nn n) (oo o) (.inr l) ≤ rkU lhat n o u ∧
        rkU lhat n o u < (su l.2.2.2 e + 1) * num lhat (nn n) (oo o) (.inr l) else ∅

variable (R FL Pl) in
/-- **The plan.** -/
noncomputable def plan (U0 U1 : ℕ) : Plan (sys R FL Pl) U0 U1 where
  cons n o z := consM lhat n o (eZ z)
  num n o x := num lhat (nn n) (oo o) (eE R FL x)
  good n o x := GoodMv lhat (nn n) (oo o) (eE R FL x)

variable {lhat n o}

theorem ix_inj : Function.Injective (ix : Un R FL Pl U0 U1 → ℕ) := fun u v huv =>
  (Fintype.equivFin (Un R FL Pl U0 U1)).injective (Fin.ext huv)

theorem mem_Al {u : Un R FL Pl U0 U1} : u ∈ Al lhat n o ↔ AlU lhat n o u := by
  classical
  unfold Al
  simp

theorem card_fin_lt' (N c : ℕ) (hc : c ≤ N) : ((univ : Finset (Fin N)).filter fun k => k.1 < c).card = c := by
  rw [Fin.card_filter_val_lt, min_eq_right hc]

/-- Sums over units. -/
theorem sum_units {N : Type} [Fintype N] {M : Type*} [AddCommMonoid M]
    (f : Uid AA U0 N U1 → M) :
    ∑ u, f u = (∑ a, ∑ c, ∑ k, f (.init a c k)) + ∑ ν, ∑ k, f (.new ν k) := by
  rw [← (proxy_equiv% (Uid AA U0 N U1)).sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma]
  rfl

/-- The number of alive units with a target. -/
theorem load_eq (τ : Tg T m AA) : load lhat (nn n) (oo o) τ =
    ((Al lhat n o).filter fun u => tgU u = τ).card := by
  classical
  have e1 : ((Al lhat n o).filter fun u => tgU u = τ).card =
      ∑ u : Un R FL Pl U0 U1, if AlU lhat n o u ∧ tgU u = τ then 1 else 0 := by
    rw [← card_filter]
    congr 1
    ext u
    simp only [mem_filter, mem_Al, mem_univ, true_and]
  rw [e1, sum_units, load, ld]
  congr 1
  · unfold bt
    by_cases hv : Valid lhat (nn n)
    · rw [if_pos hv]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      rw [← card_filter]
      refine card_bij' (fun k hk => ⟨k, ?_⟩) (fun k _ => k.1) ?_ ?_ ?_ ?_
      · have h1 := mem_range.1 (mem_filter.1 hk).1
        have h2 := (n a c).2
        have h3 : nn n a c = (n a c).1 := rfl
        omega
      · intro k hk
        obtain ⟨h1, h2⟩ := mem_filter.1 hk
        exact mem_filter.2 ⟨mem_univ _, ⟨hv, mem_range.1 h1⟩, h2⟩
      · intro k hk
        obtain ⟨-, h1, h2⟩ := mem_filter.1 hk
        exact mem_filter.2 ⟨mem_range.2 h1.2, h2⟩
      · intro k _; rfl
      · intro k _; rfl
    · rw [if_neg hv]
      symm
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun k _ => if_neg ?_
      rintro ⟨⟨h1, -⟩, -⟩
      exact hv h1
  · rw [← Equiv.sum_comp eN fun ν : NM R ch FL => if tgM ν.1 ν.2 = τ then
      alvN (oo o) ν (num lhat (nn n) (oo o) ν.1) else 0]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have hle : alv lhat (nn n) (oo o) (eN ν) ≤ U1 := by
      refine (alvN_le _ _).trans ?_
      exact (o _).2.le
    by_cases hν : tgM (eN ν).1 (eN ν).2 = τ
    · rw [if_pos hν]
      have e2 : (∑ k : Fin U1, if AlU lhat n o (.new ν k) ∧ tgU (.new ν k : Un R FL Pl U0 U1) = τ
          then 1 else 0) = ((univ : Finset (Fin U1)).filter fun k => k.1 <
            alv lhat (nn n) (oo o) (eN ν)).card := by
        rw [card_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        refine if_congr ?_ rfl rfl
        exact ⟨fun hh => hh.1, fun hh => ⟨hh, hν⟩⟩
      rw [e2, card_fin_lt' _ _ hle]
      rfl
    · rw [if_neg hν]
      symm
      refine Finset.sum_eq_zero fun k _ => if_neg ?_
      rintro ⟨-, h2⟩
      exact hν h2

/-! Membership in the consumers of a slot; used by `Ok` and `Slp4`. -/

theorem consM_inl (x : {x : RM T m AA // okR R ch x}) (e : (kindM FL (.inl x)).Sl)
    (u : Un R FL Pl U0 U1) :
    u ∈ consM lhat n o ⟨.inl x, e⟩ ↔ ActR (load lhat (nn n) (oo o)) x.1 ∧
      AlU lhat n o u ∧ tgU u = inpR x.1 := by
  classical
  rw [consM]
  split_ifs with ha
  · simp [mem_Al, ha]
  · simp [ha]

theorem consM_inr (l : LMv FL) (e : (kindM FL (.inr l)).Sl) (u : Un R FL Pl U0 U1) :
    u ∈ consM lhat n o ⟨.inr l, e⟩ ↔ Pick (load lhat (nn n) (oo o)) l ∧
      AlU lhat n o u ∧ tgU u = .seg l.1 l.2.1 l.2.2.1 (pr l.2.2.2 e) ∧
        su l.2.2.2 e * num lhat (nn n) (oo o) (.inr l) ≤ rkU lhat n o u ∧
        rkU lhat n o u < (su l.2.2.2 e + 1) * num lhat (nn n) (oo o) (.inr l) := by
  classical
  rw [consM]
  split_ifs with ha
  · simp [mem_Al, ha]
  · simp [ha]

end Nc.Tow
