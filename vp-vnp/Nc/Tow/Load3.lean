/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Load2

/-!
# The tower plan: the norms of the loads
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J m Uu AA : ℕ} {T : Tower h b D J} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}

/-- The first index with the smallest value. -/
theorem exists_im {h : ℕ} (hh : 0 < h) (f : Fin h → ℕ) : ∃ i, (∀ i', f i ≤ f i') ∧ ∀ i' < i, ¬ ∀ i'', f i' ≤ f i'' := by
  classical
  obtain ⟨i0, -, hi0⟩ := exists_min_image (univ : Finset (Fin h)) f ⟨⟨0, hh⟩, mem_univ _⟩
  have hex : ∃ k : ℕ, ∃ hk : k < h, ∀ i', f ⟨k, hk⟩ ≤ f i' := ⟨i0, i0.2, fun i' => hi0 i' (mem_univ _)⟩
  obtain ⟨hk, h1⟩ := Nat.find_spec hex
  exact ⟨⟨Nat.find hex, hk⟩, h1, fun i' hi' hcon => Nat.find_min hex hi' ⟨i'.2, hcon⟩⟩

/-- A type is chosen: `exists_im` for `f = sqs L j`. -/
theorem exists_isMin (hh : 0 < h) (L : Tg T m AA → ℕ) (j : Fin (J + 1)) : ∃ i, IsMin L j i :=
  exists_im hh (sqs L j)

/-- The chosen type has a small part of the loads. -/
theorem isMin_le {L : Tg T m AA → ℕ} {j : Fin (J + 1)} {i : Fin h} (hi : IsMin L j i) :
    (h : ℝ) * ∑ e ∈ univ.filter (fun e : T.Ed j => T.ty e = i), (L (.edge j e) : ℝ) ^ 2 ≤
      ∑ e : T.Ed j, (L (.edge j e) : ℝ) ^ 2 := by
  have h1 : h * sqs L j i ≤ ∑ i', sqs L j i' := by
    calc h * sqs L j i = ∑ _i' : Fin h, sqs L j i := by simp
      _ ≤ _ := Finset.sum_le_sum fun i' _ => hi.1 i'
  have h2 : ∑ i', sqs L j i' = ∑ e : T.Ed j, L (.edge j e) ^ 2 := by
    unfold sqs
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp
  have h3 : (sqs L j i : ℝ) = ∑ e ∈ univ.filter (fun e : T.Ed j => T.ty e = i), (L (.edge j e) : ℝ) ^ 2 := by
    unfold sqs
    rw [Finset.sum_filter]
    push_cast
    rfl
  rw [h2] at h1
  rw [← h3]
  exact_mod_cast h1

theorem vN2_mono {n n' : Sym2 T.Fl → ℕ} (hb : 0 < b) (hn : ∀ q, n q ≤ n' q) : vN2 b n ≤ vN2 b n' := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  unfold vN2
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => ?_) ?_
  · split_ifs
    · exact le_rfl
    · exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hn q) 2
  · positivity

/-- Some number of units is enough. -/
theorem exists_fits (L : Tg T m AA → ℕ) (l : LMv FL) : ∃ t d, Fits FL L (withD FL l d) t := by
  have ha : (0 : ℝ) < FL.a₁ := by exact_mod_cast FL.a₁_pos
  obtain ⟨t, ht⟩ := exists_nat_ge (√(vN2 b fun q => L (.seg l.1 l.2.1 l.2.2.1 q)) / FL.a₁)
  obtain ⟨d, hd⟩ := FL.L1 (fun q => L (.seg l.1 l.2.1 l.2.2.1 q)) t (by
    rw [div_le_iff₀ ha] at ht
    linarith)
  exact ⟨t, d, hd⟩

theorem tmin_spec (L : Tg T m AA → ℕ) (l : LMv FL) : ∃ d, Fits FL L (withD FL l d) (tmin FL L l) := by
  obtain ⟨t, ht⟩ := exists_fits L l
  exact Nat.sInf_mem (s := {t | ∃ d, Fits FL L (withD FL l d) t}) ⟨t, ht⟩

/-- A kind of law is chosen. -/
theorem exists_pick (L : Tg T m AA → ℕ) (l : LMv FL) : ∃ d, Pick FL L (withD FL l d) := by
  classical
  obtain ⟨d0, hd0⟩ := tmin_spec L l
  obtain ⟨d, hd, hmin⟩ := exists_min_image (univ.filter fun d => Fits FL L (withD FL l d) (tmin FL L l))
    (fun d => Fintype.equivFin FL.Di d) ⟨d0, mem_filter.2 ⟨mem_univ _, hd0⟩⟩
  refine ⟨d, (mem_filter.1 hd).2, fun d' hd' hf => ?_⟩
  have := hmin d' (mem_filter.2 ⟨mem_univ _, hf⟩)
  exact absurd hd' (not_lt.2 this)

/-- The number of units at a vertex is small. -/
theorem tmin_le (hb : 0 < b) (L : Tg T m AA → ℕ) (l : LMv FL) {n' : Sym2 T.Fl → ℕ}
    (hn' : ∀ q, L (.seg l.1 l.2.1 l.2.2.1 q) ≤ n' q) :
    (FL.a₁ : ℝ) * tmin FL L l ≤ √(vN2 b n') + FL.a₁ := by
  have ha : (0 : ℝ) < FL.a₁ := by exact_mod_cast FL.a₁_pos
  rcases Nat.eq_zero_or_pos (tmin FL L l) with h0 | h0
  · rw [h0]
    have := Real.sqrt_nonneg (vN2 b n')
    simp only [Nat.cast_zero, mul_zero]
    linarith
  · have h1 : ¬ ∃ d, Fits FL L (withD FL l d) (tmin FL L l - 1) := by
      intro hcon
      have := Nat.sInf_le (s := {t | ∃ d, Fits FL L (withD FL l d) t}) hcon
      change tmin FL L l ≤ _ at this
      omega
    have h2 : ¬ √(vN2 b fun q => L (.seg l.1 l.2.1 l.2.2.1 q)) ≤ (FL.a₁ : ℝ) * (tmin FL L l - 1 : ℕ) := by
      intro hcon
      obtain ⟨d, hd⟩ := FL.L1 _ _ hcon
      exact h1 ⟨d, hd⟩
    have h3 : √(vN2 b fun q => L (.seg l.1 l.2.1 l.2.2.1 q)) ≤ √(vN2 b n') :=
      Real.sqrt_le_sqrt (vN2_mono hb hn')
    rw [Nat.cast_sub h0] at h2
    push_cast at h2
    linarith [not_le.1 h2]

theorem tmin_zero {L : Tg T m AA → ℕ} {l : LMv FL} (hL : ∀ q, L (.seg l.1 l.2.1 l.2.2.1 q) = 0) : tmin FL L l = 0 := by
  have : (0 : ℕ) ∈ {t | ∃ d, Fits FL L (withD FL l d) t} := by
    refine ⟨l.2.2.2, fun q _ => ?_⟩
    change L (.seg l.1 l.2.1 l.2.2.1 q) ≤ _
    rw [hL]
    exact Nat.zero_le _
  exact Nat.le_zero.1 (Nat.sInf_le this)

section Stage

theorem num_inr_le (l : LMv FL) : num lhat n o (.inr l) ≤ tmin FL (load lhat n o) l := by
  classical
  rw [num_eq, numF]
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

variable (hb : 0 < b)
include hb

theorem num_inr_zero {l : LMv FL} (hl : ¬ IsMin (load lhat n o) l.1.castSucc l.2.1 ∨
    ¬ Pick FL (load lhat n o) l) : num lhat n o (.inr l) = 0 := by
  classical
  rcases hl with hl | hl
  · have h1 : tmin FL (load lhat n o) l = 0 := tmin_zero fun q => seg_zero hb hl _ q
    have := num_inr_le (R := R) (ch := ch) (FL := FL) (lhat := lhat) (n := n) (o := o) l
    omega
  · rw [num_eq, numF, if_neg hl]

theorem alv_inr_zero {l : LMv FL} (hl : ¬ IsMin (load lhat n o) l.1.castSucc l.2.1 ∨
    ¬ Pick FL (load lhat n o) l) (ν : (kindM R ch FL (.inr l)).Cn) :
    alv lhat n o (⟨.inr l, ν⟩ : NM R FL (ch := ch)) = 0 := by
  unfold alv
  rw [num_inr_zero hb hl]
  exact alvN_zero hb _

/-- Loads on middle segments. -/
theorem mid_load_le (j : Fin J) {i : Fin h} (hi : IsMin (load lhat n o) j.castSucc i) (e' : T.Ed (j + 1))
    (he' : T.ty e' = i) : load lhat n o (.edge j.succ e') ≤
      ∑ e ∈ univ.filter (fun e : T.Ed j => T.πE e = e'), load lhat n o (.edge j.castSucc e) := by
  classical
  have hx2 : ∀ e : T.Ed j, okR R ch (.mid j e 2) :=
    fun e => ⟨fun hh => absurd hh (by decide), fun hh => absurd hh (by decide)⟩
  refine (load_le_sum ((univ.filter fun e : T.Ed j => T.πE e = e').image
    fun e => (⟨.inl ⟨.mid j e 2, hx2 e⟩, false⟩ : NM R FL (ch := ch))) (bt_edge_succ j e') ?_).trans ?_
  · rintro ⟨⟨x, hx⟩ | l, ν⟩ hν hne
    · obtain ⟨e, h1, h2, h3⟩ := tgR_edge_succ (x := x) (ν := ν) hν
      subst h1
      have h2 : ν = false := h2
      subst h2
      exact mem_image.2 ⟨e, mem_filter.2 ⟨mem_univ _, h3⟩, rfl⟩
    · exfalso
      obtain ⟨j', i', ω, d⟩ := l
      obtain ⟨h1, h2⟩ := Tg.edge.inj hν
      have hj : j' = j := Fin.succ_injective _ h1
      subst hj
      have h3 := eq_of_heq h2
      have h4 := ((T.nr j'.2 i').symm (ω, FL.cn d ν)).2
      rw [h3, he'] at h4
      refine hne (alv_inr_zero hb (Or.inl fun hcon => ?_) ν)
      have : IsMin (load lhat n o) j'.castSucc i' := hcon
      exact h4 (firstMin_eq hi this)
  · refine Finset.sum_image_le_of_nonneg ?_ |>.trans ?_
    · intro _ _; exact Nat.zero_le _
    · exact Finset.sum_le_sum fun e _ => (alv_mid_le hb j e 2 (hx2 e) false).1

/-- Alive units at a vertex. -/
theorem alive_sq (l : LMv FL) : b * ∑ ν : (FL.L l.2.2.2).Cn, (alv lhat n o (⟨.inr l, ν⟩ : NM R FL (ch := ch))) ^ 2 ≤
    FL.G₁ * (num lhat n o (.inr l)) ^ 2 := by
  classical
  set t := num lhat n o (.inr l) with ht
  by_cases hg : GoodL o l t
  · have h1 : ∀ ν : (FL.L l.2.2.2).Cn, alv lhat n o (⟨.inr l, ν⟩ : NM R FL (ch := ch)) = o ⟨.inr l, ν⟩ := by
      intro ν
      rw [alv_inr, ← ht, if_pos hg]
    rw [Finset.sum_congr rfl fun ν _ => by rw [h1 ν]]
    exact hg
  · have h1 : ∀ ν : (FL.L l.2.2.2).Cn, alv lhat n o (⟨.inr l, ν⟩ : NM R FL (ch := ch)) ≤ t := by
      intro ν
      rw [alv_inr, ← ht, if_neg hg]
      exact min_le_right _ _
    obtain ⟨i0⟩ := FL.nonempty l.2.2.2
    have h2 := FL.L2 l.2.2.2 i0
    have h3 : ∑ ν : (FL.L l.2.2.2).Cn, (alv lhat n o (⟨.inr l, ν⟩ : NM R FL (ch := ch))) ^ 2 ≤
        (∑ ν : (FL.L l.2.2.2).Cn, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len i0 ν) ^ 2) * t ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun ν _ => ?_
      have h4 := FL.lam_pos l.2.2.2
      have h5 : 1 ≤ ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len i0 ν) ^ 2 := Nat.one_le_pow _ _ (by omega)
      calc _ ≤ t ^ 2 := Nat.pow_le_pow_left (h1 ν) 2
        _ ≤ _ := Nat.le_mul_of_pos_left _ h5
    calc _ ≤ b * ((∑ ν : (FL.L l.2.2.2).Cn, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len i0 ν) ^ 2) * t ^ 2) :=
          Nat.mul_le_mul_left _ h3
      _ = (b * ∑ ν : (FL.L l.2.2.2).Cn, ((FL.L l.2.2.2).lam + (FL.L l.2.2.2).len i0 ν) ^ 2) * t ^ 2 := by ring
      _ ≤ FL.G₁ * t ^ 2 := Nat.mul_le_mul_right _ h2

/-- Loads on the edges at vertices. -/
theorem other_load_le (j : Fin J) {i : Fin h} (hi : IsMin (load lhat n o) j.castSucc i) (ω : T.V (j + 1) i)
    (d : FL.Di) (hd : Pick FL (load lhat n o) ⟨j, i, ω, d⟩) (ν : T.Nr) :
    load lhat n o (.edge j.succ ((T.nr j.2 i).symm (ω, ν)).1) ≤
      alv lhat n o (⟨.inr ⟨j, i, ω, d⟩, (FL.cn d).symm ν⟩ : NM R FL (ch := ch)) := by
  classical
  refine (load_le_sum {(⟨.inr ⟨j, i, ω, d⟩, (FL.cn d).symm ν⟩ : NM R FL (ch := ch))} (bt_edge_succ j _) ?_).trans ?_
  · rintro ⟨⟨x, hx⟩ | l, ν'⟩ hν hne
    · exfalso
      obtain ⟨e, h1, h2, h3⟩ := tgR_edge_succ (x := x) (ν := ν') hν
      subst h1
      refine hne ((alv_mid_le hb j e 2 hx ν').2 fun hcon => ?_)
      have h4 : T.ty e = i := firstMin_eq hcon hi
      have h5 := ((T.nr j.2 i).symm (ω, ν)).2
      rw [← h3, T.π_ty j.2, h4] at h5
      exact h5 rfl
    · obtain ⟨j', i', ω', d'⟩ := l
      obtain ⟨h1, h2⟩ := Tg.edge.inj hν
      have hj : j' = j := Fin.succ_injective _ h1
      subst hj
      have h3 := eq_of_heq h2
      have hmin : IsMin (load lhat n o) j'.castSucc i' := by
        by_contra hcon
        exact hne (alv_inr_zero hb (Or.inl hcon) ν')
      obtain rfl : i' = i := firstMin_eq hmin hi
      have h4 : (T.nr j'.2 i').symm (ω', FL.cn d' ν') = (T.nr j'.2 i').symm (ω, ν) := Subtype.ext h3
      have h5 := (T.nr j'.2 i').symm.injective h4
      simp only [Prod.mk.injEq] at h5
      obtain ⟨h6, h7⟩ := h5
      subst h6
      have hpk : Pick FL (load lhat n o) ⟨j', i', ω', d'⟩ := by
        by_contra hcon
        exact hne (alv_inr_zero hb (Or.inr hcon) ν')
      have hdd : d' = d := pick_eq _ (l := ⟨j', i', ω', d'⟩) hpk hd
      subst hdd
      have h8 : ν' = (FL.cn d').symm ν := by
        rw [← h7]
        exact ((FL.cn d').symm_apply_apply ν').symm
      subst h8
      exact mem_singleton_self _
  · rw [Finset.sum_singleton]

/-- **Paper: Theorem thm:tree, One stage.** "κ_{j+1} ≤ κ_j/2 + c'|X^(j+1)|", with ρ for 1/2, where 1 + 8C₁ ≤ ρ²h. -/
theorem _root_.Paper.thm_tree_kappa (hh : 0 < h) (hbD : b ≤ 2 * D) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : 1 + 8 * FL.C₁ ≤ ρ ^ 2 * h) (j : Fin J) :
    T.kap (fun e : T.Ed (j + 1) => load lhat n o (.edge j.succ e)) ≤
      ρ * T.kap (fun e : T.Ed j => load lhat n o (.edge j.castSucc e)) +
        √FL.C₁ * FL.a₁ / b * Fintype.card (T.X (j + 1)) := by
  classical
  obtain ⟨i, hi⟩ := exists_isMin hh (load lhat n o) j.castSucc
  obtain ⟨d0, -⟩ := FL.L1 (fun _ => 0) 0 (by simp [vN2])
  refine Tower.load_step j.2 hb hbD FL.C₁_nonneg (Nat.cast_nonneg _) hρ hρ1 (i := i) ?_ ?_
    (fun ω => tmin FL (load lhat n o) (⟨j, i, ω, d0⟩ : LMv FL)) ?_ ?_
  · exact isMin_le hi
  · intro e' he'
    exact mid_load_le hb j hi e' he'
  · intro ω
    obtain ⟨d, hd⟩ := exists_pick (load lhat n o) (⟨j, i, ω, d0⟩ : LMv FL)
    have h4 : ∑ ν : T.Nr, (load lhat n o (.edge j.succ ((T.nr j.2 i).symm (ω, ν)).1)) ^ 2 ≤
        ∑ ν : (FL.L d).Cn, (alv lhat n o (⟨.inr ⟨j, i, ω, d⟩, ν⟩ : NM R FL (ch := ch))) ^ 2 := by
      rw [← Equiv.sum_comp (FL.cn d)]
      refine Finset.sum_le_sum fun ν _ => Nat.pow_le_pow_left ?_ 2
      have := other_load_le hb j hi ω d hd (FL.cn d ν)
      rwa [Equiv.symm_apply_apply] at this
    -- the squares are bounded by the length of the laws, `G₁ ≤ 2 C₁ a₁²`, and `num ≤ tmin`
    have h5 := (Nat.mul_le_mul_left b h4).trans ((alive_sq hb _).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (num_inr_le (⟨j, i, ω, d⟩ : LMv FL)) 2)))
    have h6 : (b : ℝ) * ∑ ν : T.Nr,
          (load lhat n o (.edge j.succ ((T.nr j.2 i).symm (ω, ν)).1) : ℝ) ^ 2 ≤
        FL.G₁ * (tmin FL (load lhat n o) (⟨j, i, ω, d0⟩ : LMv FL) : ℝ) ^ 2 := by
      exact_mod_cast h5
    linarith [mul_le_mul_of_nonneg_right FL.G₁_le
      (sq_nonneg (tmin FL (load lhat n o) (⟨j, i, ω, d0⟩ : LMv FL) : ℝ))]
  · intro ω
    exact tmin_le hb _ _ fun q => seg_le hb j i ω q

end Stage

end Nc.Tow
