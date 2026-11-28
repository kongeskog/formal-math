/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.SumBase

/-!
# The instruction of a base party
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {A' K E U0 U1 ub c T : ℕ}
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}
  {M : Sys A (K + K + A') E} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {key : Cell M U0 U1 → List Bool}

theorem ofBits_injective : Function.Injective ofBits := by
  intro v w h
  rw [← path_ofBits v, h, path_ofBits]

theorem getElem_map_filter {U d : ℕ} (h : d ≤ U) (f : Fin U → List Bool) (i : Fin U) (hi : i.1 < d) :
    (((List.finRange U).filter fun k => k.1 < d).map f)[i.1]? = some (f i) := by
  rw [filter_finRange h, List.map_ofFn, List.getElem?_eq_getElem (by simpa using hi)]
  simp

theorem uwBits_ne_nil (hub : 0 < ub) (w : UW ub) : uwBits w ≠ [] ↔ w ≠ none := by
  cases w with
  | none => simp [uwBits]
  | some w =>
    have : (List.ofFn w).length ≠ 0 := by
      rw [List.length_ofFn]
      omega
    simp only [uwBits, ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
    intro h
    rw [h] at this
    simp at this

theorem uwBits_injective (hub : 0 < ub) : Function.Injective (uwBits (ub := ub)) := by
  intro v w h
  by_cases hv : v = none
  · by_cases hw : w = none
    · rw [hv, hw]
    · have := (uwBits_ne_nil hub w).2 hw
      rw [← h, hv] at this
      exact absurd rfl this
  · by_cases hw : w = none
    · have := (uwBits_ne_nil hub v).2 hv
      rw [h, hw] at this
      exact absurd rfl this
    · exact G.uwBits_inj hv hw h

/-- The units of a string are the contents at the keys of the cells `f k`, `k < d`, and there are
`d` of them: the
contents of all cells `f k` are the units. -/
theorem fits_iff (hub : 0 < ub) {t : Tree} {σ : Cell M U0 U1 → UW ub} (h : Rep ub key t σ) {U d : ℕ}
    (hd : d ≤ U)
    (f : Fin U → Cell M U0 U1) (hf : ∀ k : Fin U, d ≤ k.1 → σ (f k) = none) (L : List Bool) :
    (ucount ub L = (((List.finRange U).filter fun k => k.1 < d).map fun k => key (f k)).length ∧
      Fits (((List.finRange U).filter fun k => k.1 < d).map fun k => key (f k))
        (fun i => uwBits (unitsOf ub L i)) t) ↔ ucount ub L = d ∧ ∀ k : Fin U, σ (f k) = unitsOf ub
            L k := by
  have hlen : (((List.finRange U).filter fun k => k.1 < d).map fun k => key (f k)).length = d := by
    rw [List.length_map, filter_finRange hd, List.length_ofFn]
  have hget : ∀ (k : Fin U) (hk : k.1 < d),
      (((List.finRange U).filter fun k => k.1 < d).map fun k => key (f k))[k.1]'(lt_of_lt_of_eq hk
          hlen.symm) = key (f k) := by
    intro k hk
    have := getElem_map_filter hd (fun k => key (f k)) k hk
    rw [List.getElem?_eq_getElem (lt_of_lt_of_eq hk hlen.symm)] at this
    exact Option.some.inj this
  rw [hlen]
  refine and_congr_right fun hc => ⟨fun hF k => ?_, fun hσ i hi => ?_⟩
  · by_cases hk : k.1 < d
    · have := hF k.1 (lt_of_lt_of_eq hk hlen.symm)
      rw [hget k hk, h] at this
      exact uwBits_injective hub (ofBits_injective this)
    · rw [hf k (not_lt.1 hk)]
      exact (unitsOf_eq_none.2 (by rw [hc]; exact not_lt.1 hk)).symm
  · have hi' : i < d := lt_of_lt_of_eq hi hlen
    have e : (((List.finRange U).filter fun k => k.1 < d).map fun k => key (f k))[i] =
        key (f ⟨i, lt_of_lt_of_le hi' hd⟩) := hget ⟨i, lt_of_lt_of_le hi' hd⟩ hi'
    rw [e, h, hσ]

open Classical in
/-- What a base party does with given letters. -/
theorem base_core (hub : 0 < ub) {p : Fin (K + K)} (hρ : ∀ s, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s
    p).2.2)
    {wl rl : Option S → List Γ} (hwl : ∀ s, (wl s).length ≤ T) (hrl : ∀ s, (rl s).length ≤ T) {out : Outs S}
    (h1 : ∀ i, out (Fin.castAdd (nT S) i) = ((wl ((tapes S).get i)).map (code cb)).reverse)
    (h2 : ∀ i, out (Fin.natAdd (nT S) i) = ((rl ((tapes S).get i)).map (code cb)).reverse) {t : Tree}
    {σ : Cell M U0 U1 → UW ub} (h : Rep ub key t σ)
    (hσ : ∀ a b (k : Fin U0), (n a b).1 ≤ k.1 → σ (Fin.castAdd A' p, .init a b k) = none) :
    wsum (packSem A (sepOf cb) ub (bodyOf ρ n key p) out t) (fun _ => 1) =
      ∑ R : Segs S Γ (K + K) T, ∑ C : Segs S Γ (K + K) T,
        if (∀ s, cat (R.words s) = wl s) ∧ (∀ s, cat (C.words s) = rl s) ∧ (∀ s, RowOk (ρ s p)
            (R.words s)) ∧
          (∀ b, ucount ub (strOf cb fun s => R.words s b) = n p b ∧
            ∀ k : Fin U0, σ (Fin.castAdd A' p, .init p b k) = unitsOf ub (strOf cb fun s => R.words
                s b) k) ∧
          (∀ b, ucount ub (strOf cb fun s => C.words s b) = n b p ∧
            ∀ k : Fin U0, σ (Fin.castAdd A' p, .init b p k) = unitsOf ub (strOf cb fun s => C.words
                s b) k)
        then 1 else 0 := by
  have hK : 0 < K + K := Nat.lt_of_le_of_lt (Nat.zero_le _) p.2
  rw [wsum_pack hub hK hρ hwl hrl h1 h2]
  refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun C _ => if_congr ?_ rfl rfl
  have eR : FitsAll ub (PR n key cb p R.words) t ↔ ∀ b, ucount ub (strOf cb fun s => R.words s b) =
      n p b ∧
      ∀ k : Fin U0, σ (Fin.castAdd A' p, .init p b k) = unitsOf ub (strOf cb fun s => R.words s b) k
          := by
    rw [FitsAll, PR, List.forall_mem_ofFn_iff]
    exact forall_congr' fun b => fits_iff hub h (by have := (n p b).2; omega) _ (fun k hk => hσ p b
        k hk) _
  have eC : FitsAll ub (PC n key cb p C.words) t ↔ ∀ b, ucount ub (strOf cb fun s => C.words s b) =
      n b p ∧
      ∀ k : Fin U0, σ (Fin.castAdd A' p, .init b p k) = unitsOf ub (strOf cb fun s => C.words s b) k
          := by
    rw [FitsAll, PC, List.forall_mem_ofFn_iff]
    exact forall_congr' fun b => fits_iff hub h (by have := (n b p).2; omega) _ (fun k hk => hσ b p
        k hk) _
  rw [eR, eC]

theorem length_wr (w : List (Letter S Unit Γ)) (s : Option S) : (wr w s).length ≤ w.length := by
  cases s with
  | none => exact Nat.zero_le _
  | some s => exact length_emit_le w _

theorem length_rdr (w : List (Letter S Unit Γ)) (s : Option S) : (rdr w s).length ≤ w.length := by
  cases s with
  | none => exact length_emit_le w _
  | some s => exact length_emit_le w _

theorem emit_eq_vec {m : ℕ} (w : List (Letter S Unit Γ)) (R C : Option S → Fin m → List Γ) :
    ((∀ s, cat (R s) = wr w s) ∧ ∀ s, cat (C s) = rdr w s) ↔ (∀ b, R none b = []) ∧ emit w = vec R C := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨cat_eq_nil.1 (h1 none), funext fun z => ?_⟩
    cases z with
    | tp s b =>
      cases b with
      | false => exact (h1 (some s)).symm
      | true => exact (h2 (some s)).symm
    | inp u => exact (h2 none).symm
  · rintro ⟨h1, h2⟩
    refine ⟨fun s => ?_, fun s => ?_⟩
    · cases s with
      | none => exact cat_eq_nil.2 h1
      | some s => exact (congrFun h2 (.tp s false)).symm
    · cases s with
      | none => exact (congrFun h2 (.inp ())).symm
      | some s => exact (congrFun h2 (.tp s true)).symm

open Classical in
/-- **The instruction of a base party** sums to the table of the party at the contents of the trie.
-/
theorem wsum_base (hub : 0 < ub) (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q') (hx : ∀ κ, (x
    κ).length ≤ T)
    {p : Fin (K + K)} (hρ : ∀ s, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) {t : Tree}
    {σ : Cell M U0 U1 → UW ub} (h : Rep ub key t σ)
    (hσ : ∀ a b (k : Fin U0), (n a b).1 ≤ k.1 → σ (Fin.castAdd A' p, .init a b k) = none) :
    wsum (insSem θ mu cb kinds T ub (baseIns (fun z => (qn Q z : ℕ)) cb q x ρ n key p) t) (fun _ =>
        1) =
      G.tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p fun id => σ (Fin.castAdd A' p,
          id) := by
  have hL : wsum (insSem θ mu cb kinds T ub (baseIns (fun z => (qn Q z : ℕ)) cb q x ρ n key p) t)
      (fun _ => 1) =
      ∑ R : Segs S Γ (K + K) T, ∑ C : Segs S Γ (K + K) T,
        if (∀ s, RowOk (ρ s p) (R.words s)) ∧
          (∀ b, ucount ub (strOf cb fun s => R.words s b) = n p b ∧
            ∀ k : Fin U0, σ (Fin.castAdd A' p, .init p b k) = unitsOf ub (strOf cb fun s => R.words
                s b) k) ∧
          (∀ b, ucount ub (strOf cb fun s => C.words s b) = n b p ∧
            ∀ k : Fin U0, σ (Fin.castAdd A' p, .init b p k) = unitsOf ub (strOf cb fun s => C.words
                s b) k)
        then partyW mu T q x p R.words C.words else 0 := by
    unfold baseIns
    induction p using Fin.addCases with
    | left κ =>
      rw [Fin.addCases_left, insSem, dif_pos ⟨(qn Q _).2, (qn Q _).2⟩, wsum_bindW, wsum_simSem mu cb
          hmu]
      have h1 : ∀ w : Fin T → Letter S Unit Γ, wsum (packSem A (sepOf cb) ub (bodyOf ρ n key
          (Fin.castAdd K κ))
          (outsOf cb (List.ofFn w)) t) (fun _ => 1) = _ :=
        fun w => base_core hub hρ (T := T) (wl := wr (List.ofFn w)) (rl := rdr (List.ofFn w))
          (fun s => (length_wr _ s).trans (by simp)) (fun s => (length_rdr _ s).trans (by simp))
          (outsOf_left cb _) (outsOf_right cb _) h hσ
      simp only [h1, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun R _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun C _ => ?_
      rw [partyW_block, blockW]
      split_ifs with hi hn
      · refine Finset.sum_congr rfl fun w _ => ?_
        have he := emit_eq_vec (List.ofFn w) R.words C.words
        by_cases hw : emit (List.ofFn w) = vec R.words C.words
        · obtain ⟨e1, e2⟩ := he.2 ⟨hn, hw⟩
          rw [if_pos hw, if_pos ⟨e1, e2, hi⟩, mul_one]
        · rw [if_neg hw, if_neg fun hh => hw (he.1 ⟨hh.1, hh.2.1⟩).2, mul_zero]
      · refine Finset.sum_eq_zero fun w _ => ?_
        rw [if_neg fun hh => hn ((emit_eq_vec (List.ofFn w) R.words C.words).1 ⟨hh.1, hh.2.1⟩).1, mul_zero]
      · refine Finset.sum_eq_zero fun w _ => ?_
        rw [if_neg fun hh => hi hh.2.2, mul_zero]
    | right κ =>
      rw [Fin.addCases_right, insSem]
      refine (base_core hub hρ (T := T) (wl := fun s => if s = none then x κ else []) (rl := fun _
          => [])
        (out := inOuts (S := S) ((x κ).map (code cb)).reverse)
        (fun s => by split_ifs; exacts [hx κ, Nat.zero_le _]) (fun s => Nat.zero_le _)
        (fun i => inOuts_left cb (x κ) i) (fun i => inOuts_right cb (x κ) i) h hσ).trans ?_
      refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun C _ => ?_
      rw [partyW_input]
      have he : ((∀ s, cat (R.words s) = if s = none then x κ else []) ∧ ∀ s, cat (C.words s) = [])
          ↔
          (∀ s b, R.words (some s) b = []) ∧ (∀ s b, C.words s b = []) ∧ cat (R.words none) = x κ :=
              by
        constructor
        · rintro ⟨a, b⟩
          refine ⟨fun s => cat_eq_nil.1 ?_, fun s => cat_eq_nil.1 (b s), ?_⟩
          · have := a (some s)
            simpa using this
          · have := a none
            simpa using this
        · rintro ⟨a, b, d⟩
          refine ⟨fun s => ?_, fun s => cat_eq_nil.2 (b s)⟩
          cases s with
          | none => simpa using d
          | some s => simpa using cat_eq_nil.2 (a s)
      split_ifs with h1 h2 h3 h4 h5
      · rfl
      · exact absurd (he.1 ⟨h1.1, h1.2.1⟩) h3
      · exact absurd h1.2.2 h2
      · exact absurd ⟨(he.2 h5).1, (he.2 h5).2, h4⟩ h1
      · rfl
      · rfl
  rw [hL, G.tabInit, sum_pi_pi_coe]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [sum_pi_pi_coe]
  rfl

end Nc.Grp
