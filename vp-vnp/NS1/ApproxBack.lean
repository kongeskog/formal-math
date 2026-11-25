/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.ApproxExtract
import Nc.Acc.Main

/-!
# An approximate accelerator gives an exact one

The program that reads the coefficient of ε^0 out of an approximate accelerator, its constants and its size.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree LaurentPolynomial

variable {A : Type} [CommRing A] {θ : List Bool → A} {E : Type} [CommRing E] [Algebra A E]

/-- Accept only with the counter at 0; then run the plain instance. The argument is
(argument, ((budgets, counter), names)). -/
def finF (P : Tree) : Fm :=
  .tl (.cons (.run (.quote AZ.code) (.cons (.quote AZ.code)
      (.cons (.quote .nil) (.tl (.hd (.tl .id))))))
    (app UF.code (.cons (.quote WN.code) (.cons (.quote P)
        (.cons (.hd .id) (.hd (.hd (.tl .id))))))))

theorem finF_kv {κ : List Bool → E} {S : Set (List Bool)} {P z u : Tree} {t : Bt}
    {o : List Bool} {τ : ℕ}
    (hu : u.hd = .cons t.enc (ofBits o)) (hP : Plain θ τ (zq P z t)) :
    KV θ κ S (finF P) (.cons z u) ((if KT.val o = 0 then 1 else 0)
        * algebraMap A E (pv θ (zq P z t)))
      (40 * (o.length + 1) + τ + 40) := by
  obtain ⟨k, hk, v, hv⟩ := AZ_ev (θ := θ) (.leaf o)
  generalize hx : Tree.cons z u = x
  have hv' : Ev θ (Fm.ofTree AZ.code) (.cons AZ.code (.cons .nil (ofBits o)))
      (if (Bt.leaf o).zero then [.det k v] else []) := by
    rw [Fm.ofTree_code]
    exact hv
  have eA := Ev.run_det (Dt.quote (θ := θ) AZ.code x) (Dt.cons (Dt.quote AZ.code x) (Dt.cons (Dt.quote .nil x)
    (Dt.tl (Dt.hd (Dt.tl (Dt.id x)))))) (by rw [← hx]; simpa [hu] using hv')
  have g : Gives θ (.cons (.quote WN.code) (.cons (.quote P)
      (.cons (.hd .id) (.hd (.hd (.tl .id)))))) x
      (zq P z t) 11 := by
    subst hx
    simpa [zq, hu] using (Gives.cons (Gives.quote (θ := θ) WN.code (.cons z u))
        (Gives.cons (Gives.quote P _)
      (Gives.cons (Gives.id _).hd (Gives.id _).tl.hd.hd)))
  obtain ⟨l, e, h1, h2⟩ := KV.app_gives (κ := κ) (S := S) (p := UF.code) g
    (by rw [Fm.ofTree_code]; exact NS1.UF_kv (κ := κ) (S := S) hP)
  have e' := Ev.tl (Ev.cons eA e)
  simp only [Bt.nds] at hk
  have hz : (Bt.leaf o).zero = true ↔ KT.val o = 0 := by rw [Bt.zero]; exact all_not_iff o
  refine ⟨_, e', ?_, ?_⟩
  · intro r hr
    by_cases hb : (Bt.leaf o).zero <;> simp only [hb, if_true, if_false,
        List.map_cons, List.map_nil,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map, reduceCtorEq] at hr
    · obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hr
      obtain ⟨a1, a2⟩ := h1 s hs
      simp only [Run.tick, Run.seq, Run.delay, Run.det, tl_cons]
      exact ⟨by omega, a2⟩
    · simp at hr
  · by_cases hb : KT.val o = 0
    · simp [hz.2 hb, hb, ← h2, val, wt, Run.tick, Run.seq, Run.delay, Run.det,
        Function.comp_def]
      rfl
    · simp [Bool.eq_false_iff.2 (fun h => hb (hz.1 h)), hb, val]

theorem nds_coefK (J m : ℕ) (K : KT E[T;T⁻¹]) : (coefK J m K).nds ≤ K.nds * 2 ^ (J + m + 1) := by
  induction K with
  | none => simpa [coefK, KT.nds] using Nat.one_le_two_pow
  | leaf c =>
    have := KT.nds_full (J + m) fun w => termCoef (c ^ KT.val (w.take J)) (KT.val (w.drop J))
    simp only [coefK, KT.nds]
    omega
  | node l r ihl ihr =>
    simp only [coefK, KT.nds]
    have := Nat.one_le_two_pow (n := J + m + 1)
    linarith

theorem ht_coefK (J m : ℕ) (K : KT E[T;T⁻¹]) : (coefK J m K).ht ≤ K.ht + J + m := by
  induction K with
  | none => simp [coefK, KT.ht]
  | leaf c => simp [coefK, KT.ht, KT.ht_full]
  | node l r ihl ihr =>
    simp only [coefK, KT.ht]
    omega

/-- The program of the extraction: guess with `g`, then check the counter and run the plain instance. -/
def extF (P : Tree) (g : Fm) : Fm := guessF g (finF P)

/-- **The value of the extraction.** -/
theorem extF_kv {κ : List Bool → E} {S : Set (List Bool)} {P z : Tree} {g : Fm} {cg τ W : ℕ}
    {lg : List (Run A)} {Q : List (Bt × E × List Bool)} (hg : Ev θ g z lg) (rg : List.Forall₂
        (RelX κ S cg) lg Q)
    (hP : ∀ q ∈ Q, Plain θ τ (zq P z q.1) ∧ q.2.2.length = W) :
    KV θ κ S (extF P g) z (Q.map fun q => q.2.1 * ((if KT.val q.2.2 = 0 then 1 else 0) *
      algebraMap A E (pv θ (zq P z q.1)))).sum (2 * cg + 40 * (W + 1) + τ + 60) := by
  refine (guess_kv (cg := cg) (o := fun q : Bt × E × List Bool => .cons q.1.enc (ofBits q.2.2))
      (v := fun q => q.2.1)
    (ω := fun e => (if KT.val e.tl.path = 0 then 1 else 0)
        * algebraMap A E (pv θ (.cons WN.code (.cons P (.cons z
      e.hd))))) (d := 40 * (W + 1) + τ + 40) hg rg fun q hq u hu => ?_).mono (by omega) |>.congr ?_
  · obtain ⟨h1, h2⟩ := hP q hq
    rw [← h2]
    simpa [path_ofBits, zq] using finF_kv (κ := κ) (S := S) hu h1
  · simp [path_ofBits, zq]

/-- The sizes of the fixed programs of the extraction. -/
def xcst : ℕ := combF.code.size + 2 * AZ.code.size + UF.code.size + WN.code.size + 1000

theorem xcst_def : xcst = combF.code.size + 2 * AZ.code.size + UF.code.size + WN.code.size + 1000 :=
  rfl

theorem size_chT {n C : ℕ} {f : List Bool → Fm} (h : ∀ w : List Bool, w.length = n → (f w).code.size ≤ C) :
    (chT n f).code.size + 31 ≤ 2 ^ n * (C + 31) := by
  induction n generalizing f with
  | zero => simpa [chT] using h [] rfl
  | succ n ih =>
    have h1 := ih (f := fun w => f (true :: w)) fun w hw => h _ (by simp [hw])
    have h2 := ih (f := fun w => f (false :: w)) fun w hw => h _ (by simp [hw])
    rw [chT, size_ite, size_guess, pow_succ]
    linarith

theorem size_xF (J m W : ℕ) (K : KT E[T;T⁻¹]) (pre : List Bool) :
    (xF J m W K pre).code.size ≤ K.nds * (2 ^ (J + m) * (4 * (pre.length + K.ht) + 8 * (J + m + W) + xcst + 31)) := by
  induction K generalizing pre with
  | none =>
    have h2 := size_ofBits (List.replicate W false)
    rw [List.length_replicate] at h2
    rw [KT.nds, one_mul]
    refine le_trans ?_ (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
    rw [xcst_def]
    simp only [xF, size_quote, Bt.enc, Tree.size, KT.ht]
    omega
  | leaf c =>
    have h := size_chT (n := J + m) (C := 4 * (pre.length + KT.ht (KT.leaf c)) + 8 * (J + m + W) + xcst)
      (f := fun w => .cons
      (.quote (.cons (Bt.leaf (w.take J)).enc (ofBits (expBits W (termExp (c ^ KT.val (w.take J))
          (KT.val (w.drop J)))))))
      (leaf (.quote (ofBits (pre ++ (w ++ [false]))))))
      fun w hw => by
        have h1 := size_ofBits (pre ++ (w ++ [false]))
        have h2 := size_ofBits (w.take J)
        have h3 := size_ofBits (expBits W (termExp (c ^ KT.val (w.take J)) (KT.val (w.drop J))))
        rw [length_expBits] at h3
        have h4 : (w.take J).length ≤ J := List.length_take_le _ _
        simp only [List.length_append, List.length_singleton, hw] at h1
        rw [xcst_def, size_cons, size_leaf, size_quote, size_quote]
        simp only [Bt.enc, Tree.size, KT.ht]
        omega
    rw [KT.nds, one_mul]
    exact (Nat.le_add_right _ 31).trans h
  | node l r ihl ihr =>
    have h1 := ihl (pre ++ [false])
    have h2 := ihr (pre ++ [true])
    simp only [List.length_append, List.length_singleton] at h1 h2
    obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ (J + m) * (4 * (pre.length + KT.ht (KT.node l r)) + 8 * (J + m + W) + xcst + 31) :=
      ⟨_, rfl⟩
    have e1 := h1.trans (Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left _ (by simp only [KT.ht]; omega)).trans_eq hP.symm :
      2 ^ (J + m) * (4 * (pre.length + 1 + l.ht) + 8 * (J + m + W) + xcst + 31) ≤ P))
    have e2 := h2.trans (Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left _ (by simp only [KT.ht]; omega)).trans_eq hP.symm :
      2 ^ (J + m) * (4 * (pre.length + 1 + r.ht) + 8 * (J + m + W) + xcst + 31) ≤ P))
    have e3 : combF.code.size + 130 ≤ P := by
      rw [hP]
      refine le_trans ?_ (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
      rw [xcst_def]
      omega
    rw [← hP, KT.nds, xF, zipF, size_lett, size_cons, size_cons, node, size_cons,
        size_cons, size_quote]
    simp only [size_tl, size_hd, size_id, Tree.size]
    linarith

set_option maxHeartbeats 1000000 in
theorem size_extF (P : Tree) (g : Fm) : (extF P g).code.size ≤ P.size + g.code.size + xcst := by
  rw [xcst_def, extF, guessF, finF, size_lett, node]
  simp only [size_quote, size_cons, size_hd, size_tl, size_id, size_run, size_app, Tree.size]
  omega

end NS1
