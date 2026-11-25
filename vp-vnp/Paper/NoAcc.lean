/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Main
import NS1.Diag
import NS1.Finite

/-!
# The paper, section "One scale is all scales": the ingredients of Theorem thm:noacc

The reduction to a finite field (`thm_noacc_finite_field`), the period of the squarings in a finite ring
(`thm_noacc_periodic`) and the diagonal program (`thm_noacc_diagonal`). The theorem itself is proved in
`Paper/ApproxScales`, where the approximate rounds carry the accelerator to a large scale.
-/

namespace Paper

open NS1
open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- **Paper: proof of Theorem thm:noacc, the finite field.** "As A is finitely generated, so is the ring that its
constants generate over A; modulo a maximal ideal this is a finite field E, over which it is still an accelerator." -/
theorem thm_noacc_finite_field [Algebra.FiniteType ℤ A] [Nontrivial R] {H v t : ℕ} {K : KT R} {B : ℕ} {D : Tree}
    (h : IsAccT θ H v t K B D) : ∃ (E : Type) (_ : Field E) (_ : Algebra A E) (_ : Finite E) (K' : KT E),
      IsAccT θ H v t K' B D ∧ K'.nds = K.nds ∧ K'.ht = K.ht := by
  let S : Subalgebra A R := Algebra.adjoin A K.consts
  obtain ⟨K', hK'⟩ := KT.exists_lift S K Algebra.subset_adjoin
  have h1 : IsAccT θ H v t K' B D := by
    rw [← hK'] at h
    exact h.of_map Subtype.val_injective
  have f1 : (Int.castRingHom A).FiniteType := by
    rw [← algebraMap_int_eq, RingHom.finiteType_algebraMap]
    infer_instance
  have f2 : (algebraMap A S).FiniteType := by
    rw [RingHom.finiteType_algebraMap]
    exact .adjoin_of_finite K.consts_finite
  obtain ⟨I, hI⟩ := Ideal.exists_maximal S
  have f3 : (Ideal.Quotient.mk I).FiniteType := RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective
  have f4 : (Int.castRingHom (S ⧸ I)).FiniteType := by
    have := (f3.comp f2).comp f1
    rwa [Subsingleton.elim (((Ideal.Quotient.mk I).comp (algebraMap A S)).comp (Int.castRingHom A))
      (Int.castRingHom (S ⧸ I))] at this
  let _ : Field (S ⧸ I) := Ideal.Quotient.field I
  refine ⟨S ⧸ I, inferInstance, inferInstance, finite_of_finiteType_int _ f4, K'.map (Ideal.Quotient.mkₐ A I), h1.map _, ?_, ?_⟩
  · rw [KT.nds_map, ← hK', KT.nds_map]
  · rw [KT.ht_map, ← hK', KT.ht_map]

/-- **Paper: proof of Theorem thm:noacc, the number m_E.** "As E is finite, there is m_E such that every j ≥ 0 has an
r(j) < m_E with c^(2^j) = c^(2^r(j)) for all c ∈ E; this is where finiteness is needed." Here M is m_E and red is r. -/
theorem thm_noacc_periodic (R : Type) [CommRing R] [Finite R] :
    ∃ (M : ℕ) (red : ℕ → ℕ), (∀ i, red i < M) ∧ ∀ (c : R) i, c ^ 2 ^ red i = c ^ 2 ^ i := by
  classical
  let f : ℕ → R → R := fun i c => c ^ 2 ^ i
  have hfin : (Set.range f).Finite := Set.toFinite _
  let red : ℕ → ℕ := fun i => Nat.find (⟨i, rfl⟩ : ∃ j, f j = f i)
  have hred : ∀ i, f (red i) = f i := fun i => Nat.find_spec (⟨i, rfl⟩ : ∃ j, f j = f i)
  have hinj : ∀ i j, f i = f j → red i = red j := by
    intro i j hij
    simp only [red, hij]
  have hbdd : (Set.range red).Finite := by
    have : Set.range red ⊆ (fun g : R → R => if h : ∃ i, f i = g then red h.choose else 0) '' Set.range f := by
      rintro _ ⟨i, rfl⟩
      refine ⟨f i, ⟨i, rfl⟩, ?_⟩
      have h : ∃ j, f j = f i := ⟨i, rfl⟩
      show (if h : ∃ j, f j = f i then red h.choose else 0) = red i
      rw [dif_pos h]
      exact hinj _ _ h.choose_spec
    exact (hfin.image _).subset this
  obtain ⟨M, hM⟩ := hbdd.bddAbove
  refine ⟨M + 1, red, fun i => Nat.lt_succ_of_le (hM ⟨i, rfl⟩), fun c i => congrFun (hred i) c⟩

set_option maxHeartbeats 1000000 in
/-- **Paper: proof of Theorem thm:noacc, the diagonal.** "Let v be large against E and the number of constants": the
program P guesses a bit, and for one value accepts with weight 1, for the other guesses exponents e, names λ^e and runs D
on the instance z_e of P applied to P; so its value V satisfies V = 1 + V, "impossible in E". -/
theorem thm_noacc_diagonal {h : ℕ} (hh : 17 ≤ h) [Nontrivial R] {v : ℕ} {K : KT R} {B : ℕ} {D : Tree}
    (hD : IsAccT θ (16 * h) v (v ^ (16 * h - 16)) K B D) (hcst : cst ≤ v) (hK : K.nds ≤ v) (hDs : D.size ≤ v ^ (4 * h))
    {M : ℕ} {red : ℕ → ℕ} (hM : ∀ i, red i < M) (hred : ∀ (c : R) i, c ^ 2 ^ red i = c ^ 2 ^ i) {J X : ℕ}
    (hJ : v ^ (16 * h - 15) < 2 ^ J) (hX : K.ht + max B M + J + 1 ≤ X) (hX10 : 10 ≤ X) (hXv : 1000 * X ^ 3 ≤ v) :
    False := by
  set B' := max B M with hB'
  have hX3 : 10 * X ^ 2 ≤ X ^ 3 := by
    have : X ^ 3 = X * X ^ 2 := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ hX10
  have hX2 : 10 * X ≤ X ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ hX10
  rw [cst_def] at hcst
  generalize hsU : UF.code.size = sU
  generalize hsW : WF.code.size = sW
  rw [hsU, hsW] at hcst
  have hv4 : 2000 ≤ v := by omega
  have hv1 : 1 ≤ v := by omega
  have pu : ∀ a, v ^ (a + 1) = v * v ^ a := fun a => by rw [pow_succ]; ring
  have pbig : ∀ a, 2000 * v ^ a ≤ v ^ (a + 1) := fun a => by rw [pu]; exact Nat.mul_le_mul_right _ hv4
  have ppos : ∀ a, 1 ≤ v ^ a := fun a => Nat.one_le_pow _ _ (by omega)
  set nB := (K.expand B').nds with hnB
  have hnB1 : nB ≤ K.nds * (2 * X) := (KT.nds_expand B' K).trans (Nat.mul_le_mul_left _ (by omega))
  have hnBX : ∀ c, c * X ^ 2 ≤ 1000 * X ^ 3 → nB * (c * X) ≤ 2 * v ^ 2 := by
    intro c hc
    calc nB * (c * X) ≤ K.nds * (2 * X) * (c * X) := Nat.mul_le_mul_right _ hnB1
      _ = K.nds * (2 * (c * X ^ 2)) := by ring
      _ ≤ v * (2 * v) := Nat.mul_le_mul hK (by omega)
      _ = 2 * v ^ 2 := by ring
  have hJX : J + 1 ≤ X := by omega
  -- the program
  set g : Fm := gt red J B' K [] with hg
  set p : Tree := (diagF D g).code with hp
  have hps : p.size ≤ v ^ (4 * h + 1) := by
    have s3 := size_gt red J B' K [] M (fun i _ => (hM i).le)
    rw [List.length_nil] at s3
    have s4 : g.code.size ≤ 2 * v ^ 2 := by
      have := hnBX (14 * X) (by
        rw [show 14 * X * X ^ 2 = 14 * X ^ 3 by ring]
        omega)
      calc g.code.size ≤ nB * ((J + 1) * (4 * (0 + K.ht + M) + 100)) := s3
        _ ≤ nB * (X * (14 * X)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hJX (by
            have := le_max_right B M
            omega))
        _ = nB * (14 * X * X) := by ring
        _ ≤ 2 * v ^ 2 := this
    have s5 : p.size ≤ D.size + g.code.size + sW + 500 := by
      simp only [hp, diagF, app, ZE, Fm.code, Tree.size, size_num, ← hsW]
      omega
    have s6 : v ^ 2 ≤ v ^ (4 * h) := pow_le_pow hv1 (by omega)
    have s7 : sW + 500 ≤ v ^ (4 * h) := by
      calc sW + 500 ≤ v ^ 1 := by rw [pow_one]; omega
        _ ≤ _ := pow_le_pow hv1 (by omega)
    have := pbig (4 * h)
    omega
  have hgev : ∀ z : Tree, ∃ l, Ev θ g z l ∧ List.Forall₂ (RelG K.lk (K.InB B') ((8 * J + 10) * nB)) l
      ((K.expand B').budg J) := by
    intro z
    refine gt_ev z K [] fun q hq i _ => ⟨?_, ?_⟩
    · obtain ⟨c, hc⟩ := hq.lk
      rw [List.nil_append, hc, hc, hred]
    · exact hq.inB (lt_of_lt_of_le (hM i) (le_max_right _ _))
  have hqs : ∀ q ∈ (K.expand B').budg J, q.1.ht ≤ K.ht + B' + J + 1 ∧ q.1.nds ≤ nB * (J + 1) := by
    intro q hq
    obtain ⟨h1, h3⟩ := KT.ht_nds_budg hq
    have h2 := KT.ht_expand B' K
    exact ⟨by omega, h3⟩
  have hn4 : 4 * (nB * (J + 1)) ≤ 2 * v ^ 2 := by
    have := hnBX 4 (by omega)
    calc 4 * (nB * (J + 1)) ≤ 4 * (nB * X) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hJX)
      _ = nB * (4 * X) := by ring
      _ ≤ _ := this
  have hsz : ∀ q ∈ (K.expand B').budg J, (zq p p q.1).size ≤ v ^ (16 * h - 32) := by
    intro q hq
    have h1 := Bt.size_enc q.1
    have h2 := (hqs q hq).2
    have s1 : v ^ 2 ≤ v ^ (4 * h + 1) := pow_le_pow hv1 (by omega)
    have s2 : sW + 10 ≤ v ^ (4 * h + 1) := by
      calc sW + 10 ≤ v ^ 1 := by rw [pow_one]; omega
        _ ≤ _ := pow_le_pow hv1 (by omega)
    have s3 := pbig (4 * h + 1)
    have s4 : v ^ (4 * h + 1 + 1) ≤ v ^ (16 * h - 32) := pow_le_pow hv1 (by omega)
    simp only [zq, Tree.size]
    rw [hsW]
    omega
  -- its runs
  obtain ⟨lg, eg, rg⟩ := hgev p
  obtain ⟨l, e, hl, hval⟩ := diagF_ev (D := D) eg rg (tD := v ^ (16 * h - 16)) fun q hq => by
    obtain ⟨a1, a2⟩ := hD.run _ (hsz q hq)
    exact ⟨a1, fun r hr => ⟨(a2 r hr).1, fun n hn => ((a2 r hr).2 n hn).mono (le_max_left _ _)⟩⟩
  have ep : Ev θ (Fm.ofTree p) p l := by rw [hp, Fm.ofTree_code]; exact e
  -- time
  have hT : ∀ r ∈ l, r.cost ≤ v ^ (16 * h - 15) := by
    intro r hr
    refine (hl r hr).1.trans ?_
    have m1 : (8 * J + 10) * nB ≤ 2 * v ^ 2 := by
      have := hnBX 9 (by omega)
      calc (8 * J + 10) * nB ≤ 9 * X * nB := Nat.mul_le_mul_right _ (by omega)
        _ = nB * (9 * X) := by ring
        _ ≤ _ := this
    have m2 : v ^ 2 ≤ v ^ (16 * h - 16) := pow_le_pow hv1 (by omega)
    have m3 := pbig (16 * h - 16)
    have m4 := ppos (16 * h - 16)
    have m5 : 16 * h - 15 = 16 * h - 16 + 1 := by omega
    rw [m5]
    omega
  have hJ' : ∀ r ∈ l, r.bill.length < 2 ^ J := fun r hr =>
    lt_of_le_of_lt ((bill_le ep r hr).trans (hT r hr)) hJ
  -- Lemma lem:postpone for the program applied to itself
  have hbill : ∀ r ∈ l, ∀ n ∈ r.bill, K.lk n = (K.expand B').lookup n := fun r hr n hn => KT.lookup_expand ((hl r hr).2 n hn)
  obtain ⟨hsum, hze⟩ := lem_postpone p p (T := v ^ (16 * h - 15)) hJ ep.hl (by rw [ep.evl]; exact hT)
    (K.expand B') K.lk (by rw [ep.evl]; exact hbill)
  rw [ep.evl] at hsum
  have hpl : ∀ q ∈ (K.expand B').budg J, Plain θ (v ^ (16 * h)) (zq p p q.1) := by
    intro q hq
    obtain ⟨pl, -, -⟩ := hze q hq
    refine Plain.of_le pl ?_
    have hht := KT.ht_expand B' K
    have m1 : 1000 + 100 * ((K.expand B').ht + J + 1) + 2 ≤ v := by omega
    have m2 : 40 * (nB * (J + 1)) ≤ 20 * v ^ 2 := by omega
    have m3 : v ^ 2 ≤ v ^ (16 * h - 16) := pow_le_pow hv1 (by omega)
    have m4 := pbig (16 * h - 16)
    have m5 : 16 * h - 15 = 16 * h - 16 + 1 := by omega
    have m6 : 1 ≤ v ^ (16 * h - 16) := ppos _
    have m7 : 40 * (nB * (J + 1)) + 40 ≤ v ^ (16 * h - 15) := by
      rw [m5]
      omega
    have m8 : v * v ^ (16 * h - 15) ≤ v ^ (16 * h) := by
      rw [← pu]
      exact pow_le_pow hv1 (by omega)
    rw [← hnB]
    calc (1000 + 100 * ((K.expand B').ht + J + 1)) * v ^ (16 * h - 15) + 40 * (nB * (J + 1)) + 40
        ≤ (1000 + 100 * ((K.expand B').ht + J + 1) + 2) * v ^ (16 * h - 15) := by rw [add_mul _ 2]; omega
      _ ≤ v * v ^ (16 * h - 15) := Nat.mul_le_mul_right _ m1
      _ ≤ _ := m8
  -- 1 + its own value
  have key : val K.lk l = 1 + val K.lk l := by
    conv_lhs => rw [hval]
    congr 1
    rw [hsum]
    refine congrArg List.sum (List.map_congr_left fun q hq => congrArg (q.2 * ·) ?_)
    exact hD.val _ (hsz q hq) (hpl q hq)
  have : (1 : R) = 0 := by
    have := congrArg (· - val K.lk l) key
    simpa using this.symm
  exact one_ne_zero this

end Paper
