/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.ApproxOrd
import Paper.Postpone
import Nc.Acc.CompK

/-!
# One round for approximate accelerators

The budgets of the outer program are guessed and multiplied exactly, as in an exact round. The constants of the inner
program are rescaled by ε ↦ ε^r, with r above every exponent in the outer weights. To give the rescaled constants names
of their own the round guesses budgets for all inner calls at once and runs the list program inside the interpreter.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree LaurentPolynomial

variable {A : Type} [CommRing A] {θ : List Bool → A}

section Programs

variable {R : Type} [CommRing R] [Algebra A R] {κ : List Bool → R} {S : Set (List Bool)}

theorem gt_map {R' : Type} [CommRing R'] (f : R → R') (ν : ℕ → ℕ) (J B : ℕ) (K : KT R) (pre : List Bool) :
    gt ν J B (K.map f) pre = gt ν J B K pre := by
  induction K generalizing pre with
  | none => rfl
  | leaf c => rfl
  | node l r ihl ihr => simp only [KT.map, gt, ihl, ihr]

theorem nds_expand_map {R' : Type} [CommRing R'] (f : R → R') (B : ℕ) (K : KT R) :
    ((K.map f).expand B).nds = (K.expand B).nds := by
  induction K with
  | none => rfl
  | leaf c => simp only [KT.map, KT.expand, KT.nds_comb]
  | node l r ihl ihr => simp only [KT.map, KT.expand, KT.nds, ihl, ihr]

/-- Guess budgets with `g`; run the interpreted program `P` on the argument with these budgets. -/
def rebF (g : Fm) (P : Tree) : Fm := app UF.code (ZE (.quote P) g)

/-- **The weight of a budget times the runs that use it up**, summed over the budgets. -/
theorem rebF_kv {g : Fm} {P z : Tree} {cg T H n : ℕ} {lg l : List (Run A)} {Q : List (Bt × R)} (hg : Ev θ g z lg)
    (rg : List.Forall₂ (RelG κ (· ∈ S) cg) lg Q) (hP : Ev θ (Fm.ofTree P) z l) (hT : ∀ r ∈ l, r.cost ≤ T)
    (hQ : ∀ q ∈ Q, q.1.ht ≤ H ∧ q.1.nds ≤ n) :
    KV θ κ S (rebF g P) z
      (Q.map fun q => q.2 * algebraMap A R (l.map fun r => if ok q.1 r.bill = true then r.th else 0).sum).sum
      (cg + MM H * T + 40 * n + 60) := by
  obtain ⟨lZ, eZ, rZ⟩ := ZE_ev (Dt.quote P z) hg rg
  have hZ : ∀ s ∈ lZ, ∃ q ∈ Q, wt κ s = q.2 ∧ s.out = zq P z q.1 ∧ (∀ m ∈ s.bill, m ∈ S) ∧ s.cost ≤ cg + 1 + 5 :=
    fun s hs => forall₂_exists rZ hs
  have key : ∀ q ∈ Q, ∃ l', Ev θ UF (zq P z q.1) l' ∧ (∀ r ∈ l', r.bill = [] ∧ r.cost ≤ MM H * T + 40 * n + 45) ∧
      val κ l' = algebraMap A R (l.map fun r => if ok q.1 r.bill = true then r.th else 0).sum := by
    intro q hq
    obtain ⟨h1, h2⟩ := hQ q hq
    obtain ⟨pl, pe, -⟩ := zq_plain hP hT h1 (τ := MM H * T + 40 * n + 40) (by omega)
    refine ⟨_, UF_ev pl.1.ev, ?_, ?_⟩
    · intro r hr
      rw [List.mem_map] at hr
      obtain ⟨s, hs, rfl⟩ := hr
      obtain ⟨b1, b2⟩ := pl.2 s hs
      refine ⟨b1, ?_⟩
      simp only [Run.delay]
      omega
    · rw [← pe, pv, val_plain]
      · simp [pval, Function.comp_def, Run.delay]
      · intro r hr
        rw [List.mem_map] at hr
        obtain ⟨s, hs, rfl⟩ := hr
        exact (pl.2 s hs).1
  have eU := Ev.app (p := UF.code) eZ fun s hs => by
    obtain ⟨q, hq, -, h, -⟩ := hZ s hs
    obtain ⟨l', e, -⟩ := key q hq
    rw [Fm.ofTree_code, h]
    exact e.hl
  refine ⟨_, eU, ?_, ?_⟩
  · intro u hu
    obtain ⟨s, hs, t, ht, h1, h2, -, -⟩ := mem_app hu
    obtain ⟨q, hq, -, h4, h5, h6⟩ := hZ s hs
    obtain ⟨l', e, hl', -⟩ := key q hq
    rw [Fm.ofTree_code, h4, e.evl] at ht
    obtain ⟨c1, c2⟩ := hl' t ht
    refine ⟨by omega, ?_⟩
    rw [h2, c1, List.append_nil]
    exact h5
  · rw [val_eq_sumF, sumF_app]
    rw [sum_rel (c := fun q : Bt × R => q.2) (o := fun q : Bt × R => zq P z q.1)
      (rZ.imp fun r q hr => ⟨hr.1, hr.2.1⟩)]
    congr 1
    refine List.map_congr_left fun q hq => ?_
    obtain ⟨l', e, -, hv⟩ := key q hq
    rw [Fm.ofTree_code, e.evl, ← val_eq_sumF, hv]

/-- **A program with renamed constants**: with the names `pre ++ p` for the images under `f` of its constants. -/
theorem rebill_kv (f : R →ₐ[A] R) {K : KT R} {B J : ℕ} {pre : List Bool} {P z : Tree} {T : ℕ} {l : List (Run A)}
    (hP : Ev θ (Fm.ofTree P) z l) (hT : ∀ r ∈ l, r.cost ≤ T ∧ ∀ p ∈ r.bill, K.InB B p) (hJ : T < 2 ^ J)
    (hS : ∀ p, K.InB (B + J) p → κ (pre ++ p) = f (K.lk p) ∧ pre ++ p ∈ S) :
    KV θ κ S (rebF (gt id J B K pre) P) z (f (val K.lk l))
      ((8 * J + 10) * (K.expand B).nds + MM (K.ht + B + J + 1) * T + 40 * ((K.expand B).nds * (J + 1)) + 60) := by
  obtain ⟨lg, eg, rg⟩ := gt_ev (θ := θ) (ν := id) (J := J) (B := B) (κ := κ) (P := (· ∈ S)) z (K.map f) pre
    (fun p hp i hi => by
      have h1 : K.InB (B + J) (p ++ KT.pw i) := (KT.inB_map f _ K _).1 (hp.inB hi)
      obtain ⟨h2, h3⟩ := hS _ h1
      exact ⟨h2.trans (KT.lk_map (f : R →+* R) K _).symm, h3⟩)
  rw [gt_map] at eg
  have hn : ((K.map f).expand B).nds = (K.expand B).nds := nds_expand_map f B K
  rw [hn] at rg
  refine (rebF_kv eg rg hP (fun r hr => (hT r hr).1) fun q hq => ?_).congr ?_
  · obtain ⟨h1, h3⟩ := KT.ht_nds_budg hq
    have h2 := KT.ht_expand B (K.map f)
    rw [KT.ht_map] at h2
    exact ⟨by omega, hn ▸ h3⟩
  · -- Lemma lem:postpone
    rw [← val_map f K l]
    obtain ⟨hsum, hze⟩ := Paper.lem_postpone P z hJ hP.hl (by rw [hP.evl]; exact fun r hr => (hT r hr).1)
      ((K.map f).expand B) (K.map f).lk (by
        rw [hP.evl]
        exact fun r hr p hp => KT.lookup_expand ((KT.inB_map f _ K p).2 ((hT r hr).2 p hp)))
    rw [hP.evl] at hsum
    rw [hsum]
    refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
    rw [(hze q hq).2.2.1, hP.evl]

-- `KV` unfolds to the statement of `stepA_ev` with `P := (· ∈ S)`.
theorem stepA_kv {F g : Fm} {c G p z : Tree} {cg tG tF : ℕ} {lg : List (Run A)} {Q : List (Bt × R)} {ω : Tree → R}
    (hg : Ev θ g z lg) (rg : List.Forall₂ (RelG κ (· ∈ S) cg) lg Q)
    (hG : ∀ q ∈ Q, Hl θ (Fm.ofTree G) (zq p z q.1) ∧ ∀ r ∈ evl θ (Fm.ofTree G) (zq p z q.1), r.bill = [] ∧
      r.cost ≤ tG ∧ KV θ κ S F (.cons c r.out) (ω r.out) tF) :
    KV θ κ S (stepA F c G p g) z
      (Q.map fun q => q.2 * sumF κ (evl θ (Fm.ofTree G) (zq p z q.1)) ω).sum (cg + tG + tF + 20) :=
  stepA_ev hg rg hG

end Programs

section Round

variable {E : Type} [CommRing E] [Algebra A E]

/-- **Paper: the definition of an approximate accelerator.** The program `D`, with constants in E[ε,ε⁻¹], has values in pv z + ε E[ε], in `t`
steps, on the instances of size `v ^ (H - 32)` of the universal plain sums of `v ^ H` steps. -/
structure IsAccA (θ : List Bool → A) (H v t : ℕ) (K : KT E[T;T⁻¹]) (B : ℕ) (D : Tree) : Prop where
  run : ∀ z, z.size ≤ v ^ (H - 32) → Hl θ (Fm.ofTree D) z ∧ ∀ r ∈ evl θ (Fm.ofTree D) z, r.cost ≤ t ∧
    ∀ p ∈ r.bill, K.InB B p
  val : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
    OrdGE 1 (val K.lk (evl θ (Fm.ofTree D) z) - algebraMap A E[T;T⁻¹] (pv θ z))

/-- The same, where runs have to stop only if the sum is plain. -/
structure IsPreA (θ : List Bool → A) (H v t : ℕ) (K : KT E[T;T⁻¹]) (B : ℕ) (D : Tree) : Prop where
  run : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z → Hl θ (Fm.ofTree D) z ∧
    ∀ r ∈ evl θ (Fm.ofTree D) z, r.cost ≤ t ∧ ∀ p ∈ r.bill, K.InB B p
  val : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
    OrdGE 1 (val K.lk (evl θ (Fm.ofTree D) z) - algebraMap A E[T;T⁻¹] (pv θ z))

theorem IsAccA.pre {H v t : ℕ} {K : KT E[T;T⁻¹]} {B : ℕ} {D : Tree} (h : IsAccA θ H v t K B D) :
    IsPreA θ H v t K B D :=
  ⟨fun z hz _ => h.run z hz, h.val⟩

theorem IsAccA.mono {H v t t' : ℕ} {K : KT E[T;T⁻¹]} {B B' : ℕ} {D : Tree} (h : IsAccA θ H v t K B D) (ht : t ≤ t')
    (hB : B ≤ B') : IsAccA θ H v t' K B' D :=
  ⟨fun z hz => ⟨(h.run z hz).1, fun r hr => ⟨((h.run z hz).2 r hr).1.trans ht, fun p hp =>
    (((h.run z hz).2 r hr).2 p hp).mono hB⟩⟩, h.val⟩

/-- The universal program needs no constants. -/
theorem UF_preA (θ : List Bool → A) (H v : ℕ) (B : ℕ) :
    IsPreA (E := E) θ H v (v ^ H + 5) KT.none B UF.code := by
  have h := UF_pre (A := A) (R := E[T;T⁻¹]) θ H v KT.none B
  refine ⟨h.run, fun z hz hp => ?_⟩
  rw [h.val z hz hp, sub_self]
  exact OrdGE.zero 1

/-- The program of a round: outer budgets with the names that begin with 0, inner ones with those that begin with 1. -/
def roundA {R : Type} (K : KT R) (B : ℕ) (K' : KT R) (B' J : ℕ) (D G p : Tree) : Fm :=
  stepA (rebF (gt id J B' K' [true]) (LP D).code) (LP D).code G p (gt id J B K [false])

end Round

end NS1
