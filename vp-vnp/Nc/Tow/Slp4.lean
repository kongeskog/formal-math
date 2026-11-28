/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Slp3

/-!
# The program of the tower plan: units
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G Unc

variable {F : Type} [CommRing F] {h b J m Uu AA A' U0 U1 : ℕ} {T : Tower h b J}
variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}

section Mem

variable {n : Fin AA → Fin AA → Fin (U0 + 1)} {o : (sys R FL Pl).N → Fin U1}

theorem rkU_sum (u : Un R FL Pl U0 U1) : rkU lhat n o u =
    ∑ v ∈ univ.filter (fun v : Un R FL Pl U0 U1 => tgU v = tgU u ∧ ix v < ix u),
      ind (fun _ : Unit => AlU lhat n o v) () := by
  classical
  have h1 : ∀ v, ind (fun _ : Unit => AlU lhat n o v) () = if AlU lhat n o v then 1 else 0 := by
    intro v
    by_cases hv : AlU lhat n o v
    · rw [if_pos hv, ind_true (P := fun _ : Unit => AlU lhat n o v) hv]
    · rw [if_neg hv, ind_false (P := fun _ : Unit => AlU lhat n o v) hv]
  rw [Finset.sum_congr rfl fun v _ => h1 v, ← Finset.card_filter, Finset.filter_filter]
  unfold rkU rk
  congr 1
  ext v
  simp only [mem_filter, mem_Al, mem_univ, true_and]
  tauto

/-- The unit is made at some time. -/
def SeenU (n : Fin AA → Fin AA → Fin (U0 + 1)) (o : (sys R FL Pl).N → Fin U1) : Un R FL Pl U0 U1 → Prop
  | .init a c k => k.1 < (n a c).1
  | .new ν k => k.1 ≤ (o ν).1

theorem mem_cur (u : Un R FL Pl U0 U1) :
    u ∈ (plan R FL Pl lhat U0 U1).cur n o (Fintype.card (Mv R ch FL)) ↔
      SeenU n o u ∧ ¬ ∃ z : ZM R ch FL, u ∈ consM lhat n o z := by
  classical
  unfold Plan.cur
  rw [mem_sdiff]
  refine and_congr ?_ (not_congr ?_)
  · unfold Plan.seenAt
    rw [mem_union, mem_biUnion]
    rcases u with ⟨a, c, k⟩ | ⟨ν, k⟩
    · simp [seen0, newUnits, SeenU]
    · constructor
      · rintro (h1 | ⟨x', -, h2⟩)
        · simp [seen0] at h1
        · simp only [newUnits, mem_filter, mem_univ, true_and, decide_eq_true_eq] at h2
          exact h2.2
      · intro h1
        refine Or.inr ⟨ν.1, mem_filter.2 ⟨mem_univ _, ν.1.2⟩, ?_⟩
        simp only [newUnits, mem_filter, mem_univ, true_and, decide_eq_true_eq]
        exact h1
  · unfold Plan.used
    rw [mem_biUnion]
    constructor
    · rintro ⟨z, -, hz⟩
      exact ⟨eZ z, hz⟩
    · rintro ⟨z, hz⟩
      refine ⟨eZ.symm z, mem_filter.2 ⟨mem_univ _, (eZ.symm z).1.2⟩, ?_⟩
      change u ∈ consM lhat n o (eZ (eZ.symm z))
      rw [Equiv.apply_symm_apply]
      exact hz

end Mem

variable {Inp ι : Type} {Dd Y p c : ℕ} {inp : ι → Inp → Fin Dd} {H : Set (Inp → ℕ)}
variable {nI : Inp → Fin AA → Fin AA → Fin (U0 + 1)} {oI : Inp → (sys R FL Pl).N → Fin U1}

/-- More bounds. -/
structure Bnd2 (R : Routes T m Uu) (FL : FlagLaws F T) (Pl : Place T ch A') (U0 U1 Y : ℕ) :
    Prop where
  zm : Fintype.card (ZM R ch FL) ≤ Y
  un : Fintype.card (Un R FL Pl U0 U1) ≤ Y

/-- The numbers of initial units. -/
def nX (nI : Inp → Fin AA → Fin AA → Fin (U0 + 1)) (x : Inp) : Fin AA → Fin AA → ℕ := nn (nI x)

/-- The outcomes. -/
noncomputable def oX (oI : Inp → (sys R FL Pl).N → Fin U1) (x : Inp) : NM R ch FL → ℕ := oo (oI x)

theorem rng : Rng (nX nI) (oX oI : Inp → NM R ch FL → ℕ) U0 U1 where
  n x a c := Nat.le_of_lt_succ (nI x a c).2
  o x _ := (oI x _).2.le

/-- What is known about units. -/
structure Units (nI : Inp → Fin AA → Fin AA → Fin (U0 + 1)) (oI : Inp → (sys R FL Pl).N → Fin U1)
    (lhat : ℕ) (H : Set (Inp → ℕ)) : Prop where
  cons : ∀ z u, ind (fun x => u ∈ consM lhat (nI x) (oI x) z) ∈ H
  num : ∀ mv : Mv R ch FL, (fun x => num lhat (nn (nI x)) (oo (oI x)) mv) ∈ H
  cur : ∀ u, ind (fun x => u ∈
      (plan R FL Pl lhat U0 U1).cur (nI x) (oI x) (Fintype.card (Mv R ch FL))) ∈ H
  good : ∀ mv : Mv R ch FL, ind (fun x => GoodMv lhat (nn (nI x)) (oo (oI x)) mv) ∈ H

theorem Units.weaken {H H' : Set (Inp → ℕ)} (hu : Units nI oI lhat H) (hH : H ⊆ H') :
    Units nI oI lhat H' :=
  ⟨fun z u => hH (hu.cons z u), fun mv => hH (hu.num mv), fun u => hH (hu.cur u),
    fun mv => hH (hu.good mv)⟩

variable (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hB2 : Bnd2 R FL Pl U0 U1 Y)
include hA hB hB2

theorem py_al (ha : After (nX nI) (oX oI) lhat H) (u : Un R FL Pl U0 U1) :
    PY Dd H Y 2 fun x => AlU lhat (nI x) (oI x) u := by
  rcases u with ⟨a, c, k⟩ | ⟨ν, k⟩
  · exact PY.and hA (PY.base ha.valid)
      (PY.rel1 hA (fun s => k.1 < s) (CY.base (ha.n a c)))
  · exact PY.rel1 hA (fun s => k.1 < s) (CY.base (ha.alv (eN ν)))

theorem cy_rk (hal : ∀ u, ind (fun x => AlU lhat (nI x) (oI x) u) ∈ H) (u : Un R FL Pl U0 U1) :
    CY Dd H Y 2 fun x => rkU lhat (nI x) (oI x) u := by
  have e : ∀ x, rkU lhat (nI x) (oI x) u =
      ∑ v ∈ univ.filter (fun v : Un R FL Pl U0 U1 => tgU v = tgU u ∧ ix v < ix u),
        ind (fun x => AlU lhat (nI x) (oI x) v) x := by
    intro x
    rw [rkU_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : AlU lhat (nI x) (oI x) v
    · rw [ind_true (P := fun x => AlU lhat (nI x) (oI x) v) hv,
        ind_true (P := fun _ : Unit => AlU lhat (nI x) (oI x) v) hv]
    · rw [ind_false (P := fun x => AlU lhat (nI x) (oI x) v) hv,
        ind_false (P := fun _ : Unit => AlU lhat (nI x) (oI x) v) hv]
  refine CY.congr ?_ fun x => (e x).symm
  refine CY.sum hA _ ((card_filter_le _ _).trans hB2.un) (fun v _ => CY.base (hal v))
    fun x => hA.lt_of_le ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 fun v _ => ind_le _ _).trans ?_
  rw [smul_eq_mul, mul_one]
  exact (card_filter_le _ _).trans hB2.un

theorem py_cons (ha : After (nX nI) (oX oI) lhat H)
    (hal : ∀ u, ind (fun x => AlU lhat (nI x) (oI x) u) ∈ H)
    (hrk : ∀ u, (fun x => rkU lhat (nI x) (oI x) u) ∈ H) (z : ZM R ch FL) (u : Un R FL Pl U0 U1) :
    PY Dd H Y 5 fun x => u ∈ consM lhat (nI x) (oI x) z := by
  have hY := hA.pos
  rcases z with ⟨y | l, e⟩
  · have h1 : PY Dd H Y 0 fun x => ActR (load lhat (nX nI x) (oX oI x)) y.1 :=
      py_actR hA hB ha.isMin y.1
    have h2 := PY.and hA (h1.mono hY (Nat.zero_le 1)) (PY.and hA (PY.base (hal u))
      (PY.const hA (tgU u = inpR y.1)))
    exact (h2.congr fun x => (consM_inl y e u).symm).mono hY (by omega)
  · have h1 : PY Dd H Y 0 fun x => Pick (load lhat (nX nI x) (oX oI x)) l :=
      PY.base (ha.pick l)
    have h3 : PY Dd H Y 1 fun x => su l.2.2.2 e * Tow.num lhat (nX nI x) (oX oI x) (.inr l) ≤
        rkU lhat (nI x) (oI x) u :=
      PY.rel hA (fun s t => su l.2.2.2 e * s ≤ t) (CY.base (ha.num (.inr l))) (CY.base (hrk u))
    have h4 : PY Dd H Y 1 fun x => rkU lhat (nI x) (oI x) u <
        (su l.2.2.2 e + 1) * Tow.num lhat (nX nI x) (oX oI x) (.inr l) :=
      PY.rel hA (fun s t => t < (su l.2.2.2 e + 1) * s) (CY.base (ha.num (.inr l)))
        (CY.base (hrk u))
    have h5 := PY.and hA (h1.mono hY (Nat.zero_le 4)) (PY.and hA (PY.base (hal u))
      (PY.and hA
        ((PY.const hA (tgU u = .seg l.1 l.2.1 l.2.2.1 (pr l.2.2.2 e))).mono hY (Nat.zero_le 2))
        (PY.and hA h3 h4)))
    exact h5.congr fun x => (consM_inr l e u).symm

theorem py_cur (ha : After (nX nI) (oX oI) lhat H)
    (hco : ∀ z u, ind (fun x => u ∈ consM lhat (nI x) (oI x) z) ∈ H) (u : Un R FL Pl U0 U1) :
    PY Dd H Y 4 fun x =>
      u ∈ (plan R FL Pl lhat U0 U1).cur (nI x) (oI x) (Fintype.card (Mv R ch FL)) := by
  have hY := hA.pos
  have h1 : PY Dd H Y 1 fun x => SeenU (nI x) (oI x) u := by
    rcases u with ⟨a, c, k⟩ | ⟨ν, k⟩
    · exact PY.rel1 hA (fun s => k.1 < s) (CY.base (ha.n a c))
    · refine (PY.rel1 hA (fun s => k.1 ≤ s) (CY.base (ha.o (eN ν)))).congr fun x => ?_
      have : oX oI x (eN ν) = (oI x ν).1 := by
        unfold oX oo
        rw [Equiv.symm_apply_apply]
      rw [this]
      exact Iff.rfl
  have h2 : PY Dd H Y 2 fun x => ∃ z, u ∈ consM lhat (nI x) (oI x) z :=
    PY.exists_univ hA hB2.zm fun z => PY.base (hco z u)
  exact (PY.and hA (h1.mono hY (by omega)) (PY.not hA h2)).congr fun x => (mem_cur u).symm

theorem py_good (ha : After (nX nI) (oX oI) lhat H) (mv : Mv R ch FL) :
    PY Dd H Y 4 fun x => GoodMv lhat (nX nI x) (oX oI x) mv := by
  have hY := hA.pos
  rcases mv with y | l
  · have hc : Fintype.card (kindM FL (.inl y)).Cn ≤ Y := by
      refine (Fintype.card_le_of_injective
        (fun ν : (kindM FL (.inl y)).Cn => (⟨Sum.inl y, ν⟩ : NM R ch FL)) ?_).trans hB.nm
      intro ν ν' he
      exact eq_of_heq (Sigma.mk.inj he).2
    have h1 : PY Dd H Y 3 fun x => ∀ ν : (kindM FL (.inl y)).Cn, oX oI x ⟨.inl y, ν⟩ =
        Tow.num lhat (nX nI x) (oX oI x) (.inl y) :=
      PY.forall_univ hA hc fun ν => PY.rel hA (fun s t => s = t) (CY.base (ha.o _))
        (CY.base (ha.num _))
    exact h1.mono hY (by omega)
  · have hc : Fintype.card (FL.L l.2.2.2).Cn ≤ Y := card_cn hB l
    have h1 : PY Dd H Y 1 fun x => GoodL (oX oI x) l (Tow.num lhat (nX nI x) (oX oI x) (.inr l)) :=
      PY.rel hA (fun q t => b * q ≤ FL.G₁ * t ^ 2) (CY.base (ha.q l)) (CY.base (ha.num (.inr l)))
    have h2 : PY Dd H Y 3 fun x => ∀ ν : (kindM FL (.inr l)).Cn,
        Tow.num lhat (nX nI x) (oX oI x) (.inr l) ≤ oX oI x ⟨.inr l, ν⟩ :=
      PY.forall_univ hA hc fun ν => PY.rel hA (fun s t => s ≤ t) (CY.base (ha.num _))
        (CY.base (ha.o _))
    exact PY.and hA (h1.mono hY (by omega)) h2

theorem units_stage (hS : SY inp Y p c H) (ha : After (nX nI) (oX oI) lhat H) :
    ∃ H', SY inp Y p (c + 5) H' ∧ H ⊆ H' ∧ Units nI oI lhat H' := by
  have hun : Fintype.card (Un R FL Pl U0 U1) ≤ Y ^ 1 := by simpa using hB2.un
  have hzu : Fintype.card (ZM R ch FL × Un R FL Pl U0 U1) ≤ Y ^ 2 := by
    rw [Fintype.card_prod, pow_two]
    exact Nat.mul_le_mul hB2.zm hB2.un
  obtain ⟨H1, s1, u1, f1⟩ := hS.add hA (κ := Un R FL Pl U0 U1)
    (fun u => ind fun x => AlU lhat (nI x) (oI x) u) (a := 2) (e := 1) hun
    (fun u => py_al hA hB hB2 ha u) (by omega)
  obtain ⟨H2, s2, u2, f2⟩ := s1.add hA (κ := Un R FL Pl U0 U1)
    (fun u x => rkU lhat (nI x) (oI x) u) (a := 2) (e := 1) hun
    (fun u => cy_rk hA hB hB2 f1 u) (by omega)
  have a2 := ha.weaken (u1.trans u2)
  obtain ⟨H3, s3, u3, f3⟩ := s2.add hA (κ := ZM R ch FL × Un R FL Pl U0 U1)
    (fun q => ind fun x => q.2 ∈ consM lhat (nI x) (oI x) q.1) (a := 5) (e := 2) hzu
    (fun q => py_cons hA hB hB2 a2 (fun u => u2 (f1 u)) f2 q.1 q.2) (by omega)
  have a3 := a2.weaken u3
  obtain ⟨H7, s7, u7, f7⟩ := s3.add hA (κ := Un R FL Pl U0 U1)
    (fun u => ind fun x => u ∈
        (plan R FL Pl lhat U0 U1).cur (nI x) (oI x) (Fintype.card (Mv R ch FL)))
    (a := 4) (e := 1) hun (fun u => py_cur hA hB hB2 a3 (fun z u => f3 (z, u)) u) (by omega)
  have a7 := a3.weaken u7
  obtain ⟨H8, s8, u8, f8⟩ := s7.add hA (κ := Mv R ch FL)
    (fun mv => ind fun x => GoodMv lhat (nX nI x) (oX oI x) mv) (a := 4) (e := 1)
    (by simpa using hB.mv)
    (fun mv => py_good hA hB hB2 a7 mv) (by omega)
  exact ⟨H8, s8, u1.trans (u2.trans (u3.trans (u7.trans u8))),
    fun z u => u8 (u7 (f3 (z, u))), fun mv => u8 (a7.num mv), fun u => u8 (f7 u), f8⟩

end Nc.Tow
