/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Ever1

/-!
# The units given at a node: bounds
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b J m Uu AA : ℕ} {T : Tower h b J}
  {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}

/-- Alive units of some channels with a target. -/
theorem sum_alv_le {κ : Type*} (τ : Tg T m AA) (s : Finset κ) (f : κ → NM R FL)
    (hf : Set.InjOn f s) (hτ : ∀ x ∈ s, tgM R ch FL (f x).1 (f x).2 = τ) :
    ∑ x ∈ s, alv lhat n o (f x) ≤ load lhat n o τ := by
  classical
  rw [load_def]
  refine le_trans ?_ (Nat.le_add_left _ _)
  have h1 : ∑ x ∈ s, alv lhat n o (f x) = ∑ ν ∈ s.image f, alv lhat n o ν :=
    (Finset.sum_image hf).symm
  rw [h1]
  calc ∑ ν ∈ s.image f, alv lhat n o ν =
      ∑ ν ∈ s.image f, if tgM R ch FL ν.1 ν.2 = τ then alv lhat n o ν else 0 := by
        refine Finset.sum_congr rfl fun ν hν => ?_
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hν
        rw [if_pos (hτ x hx)]
    _ ≤ _ := Finset.sum_le_sum_of_subset (subset_univ _)

section

variable
  -- every move is good (`GoodMv`): relays exact, laws neither too long nor too short
  (hg : ∀ mv, GoodMv lhat n o mv)

include hg in
theorem alv_relay (x : {x : RM T m AA // okR R ch x}) (ν : Bool) :
    alv lhat n o ⟨.inl x, ν⟩ = num lhat n o (.inl x) := by
  unfold alv
  have h1 : alvN o ⟨.inl x, ν⟩ (num lhat n o (.inl x)) =
      if o ⟨.inl x, ν⟩ = num lhat n o (.inl x) then num lhat n o (.inl x) else 0 := rfl
  rw [h1, if_pos (hg (.inl x) ν)]

theorem ok_mid2 (j : Fin J) (e : T.Ed j) : okR R ch (.mid j e 2) :=
  ⟨fun hh => absurd hh (by decide), fun hh => absurd hh (by decide)⟩


theorem nR_mid3 (j : Fin J) (e : T.Ed j) : nR lhat n o (.mid j e 3) ≤ nR lhat n o (.mid j e 2) := by
  classical
  unfold nR
  rw [dif_pos (ok_mid2 j e)]
  split_ifs with hx
  · refine (num_inl _).trans ?_
    refine (load_le_sum {(⟨.inl ⟨.mid j e 2, ok_mid2 j e⟩, true⟩ : NM R FL)} (bt_mid j e 3) ?_).trans ?_
    · rintro ⟨⟨x, hx'⟩ | l, ν⟩ hν -
      · obtain ⟨h1, h2⟩ := tgR_mid (ν := ν) hν
        have h3 : x = .mid j e 2 := by
          rcases h2 with h2 | h2 | h2
          · exact absurd h2.1 (by decide)
          · exact absurd h2.1 (by decide)
          · exact h2.2
        subst h3
        have h1 : ν = true := h1
        subst h1
        exact mem_singleton_self _
      · simp [tgM] at hν
    · rw [Finset.sum_singleton]
      exact alv_le_num _ _
  · exact Nat.zero_le _

include hg

theorem nR_mid1 (j : Fin J) (e : T.Ed j) : nR lhat n o (.mid j e 1) ≤ nR lhat n o (.mid j e 2) := by
  classical
  unfold nR
  rw [dif_pos (ok_mid2 j e)]
  split_ifs with hx
  · have h1 : num lhat n o (.inl ⟨.mid j e 2, ok_mid2 j e⟩) = load lhat n o (.nxt (.mid j e 2)) := by
      rw [num_eq, numF, if_pos]
      · rfl
      · intro hh
        exact absurd hh (by decide)
    rw [h1, ← alv_relay hg ⟨.mid j e 1, hx⟩ true]
    have h2 := sum_alv_le (lhat := lhat) (n := n) (o := o) (.nxt (.mid j e 2)) ({()} : Finset Unit)
      (fun _ => (⟨.inl ⟨.mid j e 1, hx⟩, true⟩ : NM R FL)) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl)
    rw [Finset.sum_singleton] at h2
    exact h2
  · exact Nat.zero_le _

open Classical in
/-- The middle segments at a chamber. -/
theorem sum_mid2 (j : Fin J) (c : T.X (j + 1)) :
    ((∑ e : T.Ed j, if T.π (T.e0 e) = c then nR lhat n o (.mid j e 2) else 0) +
      ∑ e : T.Ed j, if T.π (T.e1 e) = c then nR lhat n o (.mid j e 2) else 0) ≤
      fb (ldL lhat n o) (j + 1) c := by
  have h1 : ∀ e : T.Ed j, (if T.π (T.e0 e) = c then nR lhat n o (.mid j e 2) else 0) +
      (if T.π (T.e1 e) = c then nR lhat n o (.mid j e 2) else 0) =
      if T.e0 (T.πE e) = c ∨ T.e1 (T.πE e) = c then alv lhat n o
        (⟨.inl ⟨.mid j e 2, ok_mid2 j e⟩, false⟩ : NM R FL) else 0 := by
    intro e
    have h2 : nR lhat n o (.mid j e 2) = alv lhat n o
        (⟨.inl ⟨.mid j e 2, ok_mid2 j e⟩, false⟩ : NM R FL) := by
      unfold nR
      rw [dif_pos (ok_mid2 j e)]
      exact (alv_relay hg ⟨.mid j e 2, ok_mid2 j e⟩ false).symm
    rw [h2]
    have hne := π_ne e
    have h3 := T.π_ends e
    have h4 : (T.e0 (T.πE e) = c ∨ T.e1 (T.πE e) = c) ↔ (T.π (T.e0 e) = c ∨ T.π (T.e1 e) = c) := by
      have h5 : ∀ x y : T.X (j + 1), (x = c ∨ y = c) ↔ c ∈ s(x, y) := fun x y => by
        rw [Sym2.mem_iff]
        exact or_congr eq_comm eq_comm
      rw [h5, h5, h3]
    by_cases h0 : T.π (T.e0 e) = c
    · have h5 : ¬ T.π (T.e1 e) = c := fun hc => hne (h0.trans hc.symm)
      rw [if_pos h0, if_neg h5, if_pos (h4.2 (Or.inl h0)), Nat.add_zero]
    · rw [if_neg h0, Nat.zero_add]
      by_cases h5 : T.π (T.e1 e) = c
      · rw [if_pos h5, if_pos (h4.2 (Or.inr h5))]
      · rw [if_neg h5, if_neg]
        rw [h4]
        rintro (hc | hc)
        · exact h0 hc
        · exact h5 hc
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun e _ => h1 e,
    sum_end (fun e => T.πE e) (fun ē => T.e0 ē = c ∨ T.e1 ē = c)]
  unfold fb Tower.bet
  refine Finset.sum_le_sum fun ē _ => ?_
  split_ifs with hc
  · rw [← lev_succ, ← Finset.sum_filter]
    refine sum_alv_le (.edge j.succ ē) (univ.filter fun e : T.Ed j => T.πE e = ē)
      (fun e => (⟨.inl ⟨.mid j e 2, ok_mid2 j e⟩, false⟩ : NM R FL)) ?_ ?_
    · intro e _ e' _ hee
      have h2 : (Sum.inl ⟨.mid j e 2, ok_mid2 j e⟩ : Mv R ch FL) = .inl ⟨.mid j e' 2, ok_mid2 j e'⟩ :=
        congrArg Sigma.fst hee
      have h3 := congrArg Subtype.val (Sum.inl_injective h2)
      simp only [RM.mid.injEq, heq_eq_eq, true_and, and_true] at h3
      exact h3
    · intro e he
      have h2 := (mem_filter.1 he).2
      subst h2
      rfl
  · exact le_rfl

end

section Node

variable (lhat n o) in
open Classical in
/-- The number of units given in relays at a node. -/
noncomputable def NR (P : Nd T) : ℕ := ∑ x : RM T m AA, ∑ q : Fin 3, if tri R ch x q = P then nR lhat n o x else 0

variable (lhat n o) in
open Classical in
/-- The part of the start. -/
noncomputable def NR0 (P : Nd T) : ℕ := ∑ a, ∑ c, ∑ γ, ∑ s, ∑ q : Fin 3,
  if tri R ch (.start a c γ s) q = P then nR lhat n o (.start a c γ s) else 0

variable
  -- every move is good (`GoodMv`): relays exact, laws neither too long nor too short
  (hg : ∀ mv, GoodMv lhat n o mv)
include hg

open Classical in
/-- Relays of the stages, by the levels of the nodes. -/
theorem NR_le (P : Nd T) : NR lhat n o P ≤ NR0 lhat n o P +
    (∑ j : Fin J, ∑ x : T.X j, if nd j.2.le x = P then 5 * fb (ldL lhat n o) j x else 0) +
    (∑ j : Fin J, ∑ x : T.X (j + 1), if nd j.2 x = P then
      3 * chs (ldL lhat n o) j x + 2 * fb (ldL lhat n o) (j + 1) x else 0) +
    (∑ x : T.X J, if nd le_rfl x = P then fb (ldL lhat n o) J x else 0) +
    (if none = P then ∑ e : T.Ed J, ldL lhat n o J e else 0) := by
  set Lf := ldL lhat n o with hLf
  unfold NR NR0
  rw [sum_RM]
  -- the units of a level by the two ends of the edges
  have hfb : ∀ k (hk : k ≤ J), (∑ x : T.X k, if nd hk x = P then fb Lf k x else 0) =
      (∑ x : T.X k, if nd hk x = P then (∑ e, if T.e0 e = x then Lf k e else 0) else 0) +
      ∑ x : T.X k, if nd hk x = P then (∑ e, if T.e1 e = x then Lf k e else 0) else 0 := by
    intro k hk
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs
    · exact fb_eq Lf k x
    · rfl
  have hinn : ∀ j : Fin J, (∑ i, ∑ e : T.Ed j, ∑ q : Fin 3, if tri R ch (.inn j i e) q = P then
      nR lhat n o (.inn j i e) else 0) ≤
      (∑ x : T.X j, if nd j.2.le x = P then fb Lf j x else 0) +
      ∑ e : T.Ed j, if nd j.2 (hostj Lf (T.e0 e)) = P then Lf j e else 0 := by
    intro j
    have h1 : ∀ i, (∑ e : T.Ed j, ∑ q : Fin 3, if tri R ch (.inn j i e) q = P then
        nR lhat n o (.inn j i e) else 0) ≤ if i = imin Lf j then
        ∑ e : T.Ed j, ((if nd j.2.le (T.e0 e) = P then Lf j e else 0) +
          (if nd j.2 (hostj Lf (T.e0 e)) = P then Lf j e else 0) +
          if nd j.2.le (T.e1 e) = P then Lf j e else 0) else 0 := by
      intro i
      split_ifs with hi
      · subst hi
        refine Finset.sum_le_sum fun e _ => ?_
        rw [Fin.sum_univ_three]
        have h2 := nR_inn (lhat := lhat) (n := n) (o := o)
          (R := R) (ch := ch) (FL := FL) j (imin Lf j) e
        rw [if_pos rfl] at h2
        refine add_le_add (add_le_add ?_ ?_) ?_ <;> split_ifs <;>
          first | exact h2 | exact le_rfl | contradiction
      · refine le_of_eq (Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun q _ => ?_)
        have h2 := nR_inn (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) (FL := FL) j i e
        rw [if_neg hi] at h2
        split_ifs
        · omega
        · rfl
    refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
    rw [Finset.sum_ite_eq', if_pos (mem_univ _), Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_end (fun e => T.e0 e) (fun x => nd j.2.le x = P), sum_end (fun e => T.e1 e) (fun x => nd j.2.le x = P)]
    rw [hfb _ j.2.le]
    omega
  have hmid : ∀ j : Fin J, (∑ e : T.Ed j, ∑ s : Fin 4, ∑ q : Fin 3, if tri R ch (.mid j e s) q = P then
      nR lhat n o (.mid j e s) else 0) ≤
      4 * (∑ x : T.X j, if nd j.2.le x = P then fb Lf j x else 0) +
      (2 * (∑ e : T.Ed j, if nd j.2 (hostj Lf (T.e0 e)) = P then Lf j e else 0) +
        ∑ e : T.Ed j, if nd j.2 (hostj Lf (T.e1 e)) = P then Lf j e else 0) +
      2 * ∑ x : T.X (j + 1), if nd j.2 x = P then fb Lf (j + 1) x else 0 := by
    intro j
    have h1 : ∀ e : T.Ed j, (∑ s : Fin 4, ∑ q : Fin 3, if tri R ch (.mid j e s) q = P then
        nR lhat n o (.mid j e s) else 0) ≤
        ((if nd j.2.le (T.e0 e) = P then Lf j e else 0) + 4 * if nd j.2.le (T.e1 e) = P then Lf j e else 0) +
        (2 * (if nd j.2 (hostj Lf (T.e0 e)) = P then Lf j e else 0) +
          if nd j.2 (hostj Lf (T.e1 e)) = P then Lf j e else 0) +
        (2 * (if nd j.2 (T.π (T.e0 e)) = P then nR lhat n o (.mid j e 2) else 0) +
          2 * if nd j.2 (T.π (T.e1 e)) = P then nR lhat n o (.mid j e 2) else 0) := by
      intro e
      have hs : ∀ s, nR lhat n o (.mid j e s) ≤ Lf j e ∧ (T.ty e ≠ imin Lf j →
          nR lhat n o (.mid j e s) = 0) := by
        intro s
        have h2 := nR_mid (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) (FL := FL) j e s
        constructor
        · refine h2.trans ?_
          split_ifs
          · exact le_rfl
          · exact Nat.zero_le _
        · intro hne
          rw [if_neg hne] at h2
          omega
      have h3 := nR_mid3 (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) (FL := FL) j e
      have h4 := nR_mid1 hg j e
      -- the chambers on the next level
      have hH : ∀ s (c : T.X j), (if nd j.2 (hst (T.ty e) c) = P then nR lhat n o (.mid j e s) else 0) ≤
          if nd j.2 (hostj Lf c) = P then Lf j e else 0 := by
        intro s c
        by_cases ht : T.ty e = imin Lf j
        · have : hst (T.ty e) c = hostj Lf c := by rw [ht]; rfl
          rw [this]
          split_ifs
          · exact (hs s).1
          · exact le_rfl
        · rw [(hs s).2 ht]
          split_ifs <;> exact Nat.zero_le _
      have hle : ∀ s (p : Prop) [Decidable p], (if p then nR lhat n o (.mid j e s) else 0) ≤
          if p then Lf j e else 0 := by
        intro s p _
        split_ifs
        · exact (hs s).1
        · exact le_rfl
      have hp : ∀ s (p : Prop) [Decidable p], s = 1 ∨ s = 2 ∨ s = 3 → (if p then nR lhat n o (.mid j e s) else 0) ≤
          if p then nR lhat n o (.mid j e 2) else 0 := by
        intro s p _ hs'
        split_ifs
        · rcases hs' with rfl | rfl | rfl
          · exact h4
          · exact le_rfl
          · exact h3
        · exact le_rfl
      rw [Fin.sum_univ_four, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
      have a0 := hle 0 (nd j.2.le (T.e0 e) = P)
      have b0 := hle 0 (nd j.2.le (T.e1 e) = P)
      have b1 := hle 1 (nd j.2.le (T.e1 e) = P)
      have b2 := hle 2 (nd j.2.le (T.e1 e) = P)
      have b3 := hle 3 (nd j.2.le (T.e1 e) = P)
      have c0 := hH 0 (T.e0 e)
      have c1 := hH 1 (T.e0 e)
      have c3 := hH 3 (T.e1 e)
      have d1 := hp 1 (nd j.2 (T.π (T.e0 e)) = P) (Or.inl rfl)
      have d4 := hp 3 (nd j.2 (T.π (T.e1 e)) = P) (Or.inr (Or.inr rfl))
      change ((if nd j.2.le (T.e0 e) = P then _ else 0) + (if nd j.2 (hst (T.ty e) (T.e0 e)) = P then _ else 0) +
          if nd j.2.le (T.e1 e) = P then _ else 0) +
        ((if nd j.2 (hst (T.ty e) (T.e0 e)) = P then _ else 0) +
          (if nd j.2 (T.π (T.e0 e)) = P then _ else 0) + if nd j.2.le (T.e1 e) = P then _ else 0) +
        ((if nd j.2 (T.π (T.e0 e)) = P then _ else 0) +
          (if nd j.2 (T.π (T.e1 e)) = P then _ else 0) + if nd j.2.le (T.e1 e) = P then _ else 0) +
        ((if nd j.2 (T.π (T.e1 e)) = P then _ else 0) +
          (if nd j.2 (hst (T.ty e) (T.e1 e)) = P then _ else 0) +
            if nd j.2.le (T.e1 e) = P then _ else 0) ≤ _
      omega
    refine (Finset.sum_le_sum fun e _ => h1 e).trans ?_
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have e0 := sum_end (fun e : T.Ed j => T.e0 e) (fun x => nd j.2.le x = P) (fun e => Lf j e)
    have e1 := sum_end (fun e : T.Ed j => T.e1 e) (fun x => nd j.2.le x = P) (fun e => Lf j e)
    have e2 := sum_end (fun e : T.Ed j => T.π (T.e0 e)) (fun x => nd j.2 x = P)
      (fun e => nR lhat n o (.mid j e 2))
    have e3 := sum_end (fun e : T.Ed j => T.π (T.e1 e)) (fun x => nd j.2 x = P)
      (fun e => nR lhat n o (.mid j e 2))
    have h4 : (∑ x : T.X (j + 1), if nd j.2 x = P then
          (∑ e, if T.π (T.e0 e) = x then nR lhat n o (.mid j e 2) else 0) else 0) +
        (∑ x : T.X (j + 1), if nd j.2 x = P then
          (∑ e, if T.π (T.e1 e) = x then nR lhat n o (.mid j e 2) else 0) else 0) ≤
        ∑ x : T.X (j + 1), if nd j.2 x = P then fb Lf (j + 1) x else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun x _ => ?_
      split_ifs
      · exact sum_mid2 hg j x
      · exact le_rfl
    rw [e0, e1, e2, e3, hfb _ j.2.le]
    omega
  have hfin : (∑ e : T.Ed J, ∑ q : Fin 3, if tri R ch (.fin e) q = P then nR lhat n o (.fin e) else 0) ≤
      (∑ x : T.X J, if nd le_rfl x = P then fb Lf J x else 0) +
      if none = P then ∑ e : T.Ed J, Lf J e else 0 := by
    have h1 : ∀ e : T.Ed J, (∑ q : Fin 3, if tri R ch (.fin e) q = P then nR lhat n o (.fin e) else 0) ≤
        (if nd le_rfl (T.e0 e) = P then Lf J e else 0) + (if none = P then Lf J e else 0) +
          if nd le_rfl (T.e1 e) = P then Lf J e else 0 := by
      intro e
      have h2 := nR_fin (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) (FL := FL) e
      rw [Fin.sum_univ_three]
      refine add_le_add (add_le_add ?_ ?_) ?_ <;> split_ifs <;>
        first | exact h2 | exact le_rfl | contradiction
    refine (Finset.sum_le_sum fun e _ => h1 e).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_end (fun e => T.e0 e) (fun x => nd le_rfl x = P),
      sum_end (fun e => T.e1 e) (fun x => nd le_rfl x = P)]
    rw [hfb J le_rfl, Finset.sum_ite_irrel, Finset.sum_const_zero]
    omega
  have hchs : ∀ j : Fin J, (∑ x : T.X (j + 1), if nd j.2 x = P then chs Lf j x else 0) =
      (∑ e : T.Ed j, if nd j.2 (hostj Lf (T.e0 e)) = P then Lf j e else 0) +
      ∑ e : T.Ed j, if nd j.2 (hostj Lf (T.e1 e)) = P then Lf j e else 0 := by
    intro j
    rw [sum_end (fun e : T.Ed j => hostj Lf (T.e0 e)) (fun x => nd j.2 x = P),
      sum_end (fun e : T.Ed j => hostj Lf (T.e1 e)) (fun x => nd j.2 x = P),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs
    · unfold chs
      rw [sum_end (fun e => T.e0 e) (fun c => hostj Lf c = x),
        sum_end (fun e => T.e1 e) (fun c => hostj Lf c = x), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs
      · exact fb_eq Lf j c
      · rfl
    · rfl
  have hall : (∑ j, ∑ i, ∑ e, ∑ q : Fin 3, if tri R ch (.inn j i e) q = P then nR lhat n o (.inn j i e) else 0) +
      (∑ j, ∑ e, ∑ s, ∑ q : Fin 3, if tri R ch (.mid j e s) q = P then nR lhat n o (.mid j e s) else 0) ≤
      (∑ j : Fin J, ∑ x : T.X j, if nd j.2.le x = P then 5 * fb Lf j x else 0) +
      ∑ j : Fin J, ∑ x : T.X (j + 1),
        if nd j.2 x = P then 3 * chs Lf j x + 2 * fb Lf (j + 1) x else 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [ite_add_zero, ← mul_ite_zero, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := hinn j
    have h2 := hmid j
    rw [hchs j]
    omega
  omega

end Node

end Nc.Tow
