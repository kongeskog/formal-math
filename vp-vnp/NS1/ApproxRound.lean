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

The budgets of the outer program are guessed and multiplied exactly. The constants of the inner
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

/-- Guess budgets with `g`; run the plain instance of the program `P` on the argument with these budgets. -/
def rebF (g : Fm) (P : Tree) : Fm := guessF g (app UF.code (ZE (.quote P)))

/-- The universal program on a plain instance: its value is the plain sum. -/
theorem UF_kv {y : Tree} {τ : ℕ} (hy : Plain θ τ y) : KV θ κ S UF y (algebraMap A R (pv θ y)) (τ + 9) := by
  refine ⟨_, UF_ev hy.1.ev, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    have := hy.2 s hs
    simp only [Tree.size, names]
    exact ⟨by omega, by simp⟩
  · simp [val, wt, names, pv, pval, map_list_sum, Function.comp_def]

/-- **The weight of a budget times the plain sum of its instance**, summed over the budgets. -/
theorem rebF_kv {g : Fm} {P z : Tree} {cg τ : ℕ} {lg : List (Run A)} {Q : List (Bt × R)} (hg : Ev θ g z lg)
    (rg : List.Forall₂ (RelG κ (· ∈ S) cg) lg Q) (hP : ∀ q ∈ Q, Plain θ τ (zq P z q.1)) :
    KV θ κ S (rebF g P) z (Q.map fun q => q.2 * algebraMap A R (pv θ (zq P z q.1))).sum (2 * cg + τ + 40) := by
  refine (guess_kv (ω := fun e => algebraMap A R (pv θ (.cons WN.code (.cons P (.cons z e))))) (d := τ + 21) hg rg
    fun q hq u hu => ?_).mono (by omega)
  have hZ : Gives θ (ZE (.quote P)) (.cons z u) (zq P z q.1) 10 := by
    simpa [zq, ZE, hu] using (Gives.quote (θ := θ) WN.code (.cons z u)).cons
      ((Gives.quote P _).cons ((Gives.id _).hd.cons (Gives.id _).tl.hd))
  exact (KV.app_gives (d := τ + 9) hZ (by rw [Fm.ofTree_code]; exact UF_kv (hP q hq))).mono (by omega)

/-- **A program with renamed constants**: with the names `pre ++ p` for the images under `f` of its constants. -/
theorem rebill_kv (f : R →ₐ[A] R) {K : KT R} {B J : ℕ} {pre : List Bool} {P z : Tree} {T L : ℕ} {l : List (Run A)}
    (hP : Ev θ (Fm.ofTree P) z l) (hT : ∀ r ∈ l, r.cost + r.out.size ≤ T ∧ ∀ p ∈ names r.out, K.InB B p)
    (hJ : T < 2 ^ J) (hS : ∀ p, K.InB (B + J) p → κ (pre ++ p) = f (K.lk p) ∧ pre ++ p ∈ S ∧ (pre ++ p).length ≤ L) :
    KV θ κ S (rebF (gt id J B K pre) P) z (f (val K.lk l))
      (2 * (((4 * L + 48) * J + 80) * (K.expand B).nds) + (60 * (K.ht + B + J + 1) + 42) * T +
        40 * ((K.expand B).nds * (J + 1)) + 120) := by
  obtain ⟨lg, eg, rg⟩ := gt_ev (θ := θ) (ν := id) (J := J) (B := B) (L := L) (κ := κ) (P := (· ∈ S)) z (K.map f) pre
    (fun p hp i hi => by
      have h1 : K.InB (B + J) (p ++ KT.pw i) := (KT.inB_map f _ K _).1 (hp.inB hi)
      obtain ⟨h2, h3, h4⟩ := hS _ h1
      exact ⟨h2.trans (KT.lk_map (f : R →+* R) K _).symm, h3, h4⟩)
  rw [gt_map] at eg
  have hn : ((K.map f).expand B).nds = (K.expand B).nds := nds_expand_map f B K
  rw [hn] at rg
  -- Lemma lem:postpone
  obtain ⟨hsum, hze⟩ := Paper.lem_postpone P z hJ hP.hl (by rw [hP.evl]; exact fun r hr => (hT r hr).1)
    ((K.map f).expand B) (K.map f).lk (by
      rw [hP.evl]
      exact fun r hr p hp => KT.lookup_expand ((KT.inB_map f _ K p).2 ((hT r hr).2 p hp)))
  have h2 := KT.ht_expand B (K.map f)
  rw [KT.ht_map] at h2
  refine ((rebF_kv eg rg fun q hq => (hze q hq).1).mono ?_).congr ?_
  · rw [hn]
    have := Nat.mul_le_mul_right T (show 60 * (((K.map f).expand B).ht + J + 1) + 42 ≤
      60 * (K.ht + B + J + 1) + 42 by omega)
    omega
  · rw [← val_map f K l, ← hP.evl, hsum]
    rfl

end Programs

section Round

variable {E : Type} [CommRing E] [Algebra A E]

/-- **Paper: the definition of an approximate accelerator.** The program `D`, with constants in E[ε,ε⁻¹], has values in pv z + ε E[ε], in `t`
steps, on the instances of size `v ^ (H - 32)` of the universal plain sums of `v ^ H` steps. -/
structure IsAccA (θ : List Bool → A) (H v t : ℕ) (K : KT E[T;T⁻¹]) (B : ℕ) (D : Tree) : Prop where
  run : ∀ z, z.size ≤ v ^ (H - 32) → Hl θ (Fm.ofTree D) z ∧ ∀ r ∈ evl θ (Fm.ofTree D) z, r.cost + r.out.size ≤ t ∧
    ∀ p ∈ names r.out, K.InB B p
  val : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
    OrdGE 1 (val K.lk (evl θ (Fm.ofTree D) z) - algebraMap A E[T;T⁻¹] (pv θ z))

/-- The same, where runs have to stop only if the sum is plain. -/
structure IsPreA (θ : List Bool → A) (H v t : ℕ) (K : KT E[T;T⁻¹]) (B : ℕ) (D : Tree) : Prop where
  run : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z → Hl θ (Fm.ofTree D) z ∧
    ∀ r ∈ evl θ (Fm.ofTree D) z, r.cost + r.out.size ≤ t ∧ ∀ p ∈ names r.out, K.InB B p
  val : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
    OrdGE 1 (val K.lk (evl θ (Fm.ofTree D) z) - algebraMap A E[T;T⁻¹] (pv θ z))

theorem IsAccA.pre {H v t : ℕ} {K : KT E[T;T⁻¹]} {B : ℕ} {D : Tree} (h : IsAccA θ H v t K B D) :
    IsPreA θ H v t K B D :=
  ⟨fun z hz _ => h.run z hz, h.val⟩

theorem IsAccA.mono {H v t t' : ℕ} {K : KT E[T;T⁻¹]} {B B' : ℕ} {D : Tree} (h : IsAccA θ H v t K B D) (ht : t ≤ t')
    (hB : B ≤ B') : IsAccA θ H v t' K B' D :=
  ⟨fun z hz => ⟨(h.run z hz).1, fun r hr => ⟨((h.run z hz).2 r hr).1.trans ht, fun p hp =>
    (((h.run z hz).2 r hr).2 p hp).mono hB⟩⟩, h.val⟩

/-- The universal program is a program for the universal plain sums; it needs no constants. -/
theorem UF_preA (θ : List Bool → A) (H v : ℕ) (B : ℕ) :
    IsPreA (E := E) θ H v (v ^ H + 9) KT.none B UF.code := by
  constructor
  · intro z _ hp
    have e := UF_ev hp.1.ev
    rw [Fm.ofTree_code]
    refine ⟨e.hl, fun r hr => ?_⟩
    rw [e.evl, List.mem_map] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    have := hp.2 s hs
    simp only [Tree.size, names]
    exact ⟨by omega, by simp⟩
  · intro z _ hp
    rw [Fm.ofTree_code, (UF_ev hp.1.ev).evl,
      show val KT.none.lk _ = algebraMap A E[T;T⁻¹] (pv θ z) by simp [val, wt, names, pv, pval, map_list_sum,
        Function.comp_def], sub_self]
    exact OrdGE.zero 1

/-- The constants of `E` as constant Laurent polynomials. -/
noncomputable def cstL : E →ₐ[A] E[T;T⁻¹] := IsScalarTower.toAlgHom A E E[T;T⁻¹]

/-- An exact accelerator is an approximate one with constants in `E`. -/
theorem IsAccT.toA {H v t : ℕ} {K : KT E} {B : ℕ} {D : Tree} (h : IsAccT θ H v t K B D) :
    IsAccA θ H v t (K.map (cstL (A := A))) B D := by
  have h' := h.map (cstL (A := A) (E := E))
  refine ⟨h'.run, fun z hz hp => ?_⟩
  rw [h'.val z hz hp, sub_self]
  exact OrdGE.zero 1

/-- If the constants of an approximate accelerator are constant Laurent polynomials, the images of a trie `K`
over `E`, then the same program with `K` is an exact accelerator: the value minus pv(z) then lies in `E`, and
having no term in ε⁰ it is zero. -/
theorem IsAccA.toT {H v t : ℕ} {K : KT E} {B : ℕ} {D : Tree}
    (h : IsAccA θ H v t (K.map (cstL (A := A))) B D) : IsAccT θ H v t K B D := by
  refine ⟨fun z hz => ⟨(h.run z hz).1, fun r hr => ⟨((h.run z hz).2 r hr).1, fun p hp =>
    (KT.inB_map _ B K p).1 (((h.run z hz).2 r hr).2 p hp)⟩⟩, fun z hz hp => ?_⟩
  have h0 := h.val z hz hp 0 (by norm_num)
  rw [NS1.val_map, ← AlgHom.commutes (cstL (A := A) (E := E)), ← map_sub] at h0
  have : (cstL (A := A) (E := E)) (NS1.val K.lk (evl θ (Fm.ofTree D) z) - algebraMap A E (pv θ z)) =
      algebraMap E E[T;T⁻¹] (NS1.val K.lk (evl θ (Fm.ofTree D) z) - algebraMap A E (pv θ z)) := rfl
  rw [this, coeff_algebraMap (A := E) (E := E), if_pos rfl] at h0
  exact sub_eq_zero.1 (by simpa using h0)

/-- Rescaling `ε ↦ ε ^ r` fixes the constants of `E`. -/
theorem rescale_cstL (r : ℕ) (e : E) : rescale A r (cstL (A := A) e) = cstL (A := A) e := by
  show rescale A r (algebraMap E E[T;T⁻¹] e) = algebraMap E E[T;T⁻¹] e
  rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply]
  simp only [rescale, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidHom.coe_mulLeft]
  rw [AddMonoidAlgebra.mapDomain_single, mul_zero]

/-- The program of a round: outer budgets with the names that begin with 0, inner ones with those that begin with 1. -/
def roundA {R : Type} (K : KT R) (B : ℕ) (K' : KT R) (B' J : ℕ) (D G p : Tree) : Fm :=
  stepA (rebF (gt id J B' K' [true]) (LP D).code) (LP D).code G p (gt id J B K [false])

end Round

end NS1
