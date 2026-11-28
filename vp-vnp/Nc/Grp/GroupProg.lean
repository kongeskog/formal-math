/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.Guess

/-!
# The program GROUP

GROUP runs over the script twice. First every instruction guesses the contents at its keys that
have none; then every instruction compares what it computes with the contents, and the trie does
not change any more.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

section unary

/-- Unary from binary (most significant bit first). -/
def unF (b : Fm) : Fm := foldF (.ite (.hd .id) (.cons (.quote .nil) (appF (.tl .id) (.tl .id))) (appF (.tl .id) (.tl .id)))
  (.quote .nil) b

theorem le_foldl_bval (w : List Bool) (a : ℕ) : a ≤ w.foldl (fun a b => 2 * a + b.toNat) a := by
  induction w generalizing a with
  | nil => exact le_rfl
  | cons b w ih => exact le_trans (by omega) (ih (2 * a + b.toNat))

theorem unStep_gives (b : Bool) (a v : ℕ) (ha : a ≤ v) :
    Gives θ (.ite (.hd .id) (.cons (.quote .nil) (appF (.tl .id) (.tl .id))) (appF (.tl .id) (.tl .id)))
      (.cons (bit b) (num a)) (num (2 * a + b.toNat)) (v * 62 + 90) := by
  have e1 : Gives θ (.tl .id) (.cons (bit b) (num a)) (ofBits (List.replicate a false)) 2 := by
    rw [← num_eq_ofBits]
    exact (Gives.id _).tl
  have e2 := appBits_gives e1 e1
  rw [← List.replicate_add, ← num_eq_ofBits, List.length_replicate, ← two_mul] at e2
  cases b with
  | false => exact (Gives.ite_false (Gives.id _).hd e2).mono (by omega)
  | true =>
    have e3 : Gives θ (.cons (.quote .nil) (appF (.tl .id) (.tl .id))) (.cons (bit true) (num a)) (num (2 * a + 1))
        (v * 62 + 80) := (Gives.cons (Gives.quote .nil _) e2).mono (by omega)
    exact (Gives.ite_true (Gives.id _).hd (by simp [bit, one]) e3).mono (by omega)

theorem unF_gives {b : Fm} {x : Tree} {w : List Bool} {c : ℕ} (h : Gives θ b x (ofBits w) c) :
    Gives θ (unF b) x (num (bval w)) (c + w.length * (bval w * 62 + 130) + 30) := by
  have hl : Gives θ b x (listT (w.map bit)) c := by
    rw [listT_ofBits]
    exact h
  have h1 := foldTG (θ := θ) (s₀ := 0) (g := fun b a => 2 * a + b.toNat)
    (Inv := fun ys a => ys.foldl (fun a b => 2 * a + b.toNat) a = bval w) (d := fun _ => bval w * 62 + 90)
    (step := .ite (.hd .id) (.cons (.quote .nil) (appF (.tl .id) (.tl .id))) (appF (.tl .id) (.tl .id)))
    (s := .quote .nil) (Gives.quote _ _) hl (fun b ys a _ hinv => ⟨unStep_gives b a _ (by
      rw [← hinv]
      exact le_trans (by omega) (le_foldl_bval ys (2 * a + b.toNat))), hinv⟩) rfl
  refine h1.mono ?_
  simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  ring_nf
  omega

end unary

section group

variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}
  (mu : Letter S Unit Γ → Matrix Q Q A) (cb : Option Γ → Fin c → Bool) (kinds : List (Σ L : G.Law A, L.Ro))

/-- The separator. -/
def sepOf : List Bool := List.ofFn (cb none)

variable (θ) in
/-- What an instruction does with a trie. -/
noncomputable def insSem (T ub : ℕ) : Ins → Tree → List (A × Tree)
  | .block q q' B, t => if h : q < Fintype.card Q ∧ q' < Fintype.card Q then
      bindW (simSem θ mu cb T ⟨q, h.1⟩ ⟨q', h.2⟩) fun o => packSem A (sepOf cb) ub B o t else []
  | .input part B, t => packSem A (sepOf cb) ub B (inOuts (S := S) part) t
  | .both k k', t => if tget k t = tget k' t then [(1, t)] else []
  | .one k w, t => if tget k t = ofBits w then [(1, t)] else []
  | .role j tt slots keys, t => match kinds[j]? with
    | some z => roleSem θ z.1 z.2 ub (fun k => (tget k t).path) tt slots keys t
    | none => []

/-- Conditions on an instruction. -/
def InsOk (S Q : Type) [Fintype S] [DecidableEq S] [Fintype Q] (c : ℕ) (kinds : List (Σ L : G.Law A, L.Ro)) : Ins → Prop
  | .block q q' _ => q < Fintype.card Q ∧ q' < Fintype.card Q
  | .input part _ => ∀ a ∈ part, a.length ≤ c
  | .both _ _ => True
  | .one _ _ => True
  | .role j _ slots _ => ∃ z, kinds[j]? = some z ∧ slots.length = (slList z.1 z.2).length

/-- Costs of the body of an instruction. -/
def bodyCost (ub : ℕ) (B : Body) : ℕ := flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1

/-- Costs of an instruction. -/
def insCost (T ub : ℕ) : Ins → ℕ
  | .block _ _ B => T + bodyCost ub B
  | .input part B => part.length + bodyCost ub B
  | .both k k' => k.length + k'.length + ub + 1
  | .one k w => k.length + w.length + ub + 1
  | .role _ tt slots keys => tt * (ub + 1) + putCost ub slots + putCost ub keys + 1

/-- All contents are lists of at most `ub` bits. -/
def TOk (ub : ℕ) (t : Tree) : Prop := ∀ k, ∃ w : List Bool, tget k t = ofBits w ∧ w.length ≤ ub

theorem TOk.path {ub : ℕ} {t : Tree} (h : TOk ub t) (k : List Bool) : tget k t = ofBits (tget k t).path ∧
    (tget k t).path.length ≤ ub := by
  obtain ⟨w, h1, h2⟩ := h k
  rw [h1, path_ofBits]
  exact ⟨rfl, h2⟩

theorem tOk_nil (ub : ℕ) : TOk ub .nil := fun k => ⟨[], by rw [tget_nil]; rfl, Nat.zero_le _⟩

theorem TOk.tset {ub : ℕ} {t : Tree} (h : TOk ub t) (k w : List Bool) (hw : w.length ≤ ub) :
    TOk ub (tset k (ofBits w) t) := by
  intro k'
  rw [tget_tset]
  split_ifs
  · exact ⟨w, rfl, hw⟩
  · exact h k'

theorem putL_out {ub : ℕ} {keys : List (List Bool)} {r : List Bool} {t : Tree} :
    ∀ t' ∈ putL ub keys r t, t' = t := by
  induction keys generalizing r with
  | nil =>
    intro t' ht'
    rw [Grp.putL] at ht'
    split_ifs at ht'
    · exact List.mem_singleton.1 ht'
    · simp at ht'
  | cons k ks ih =>
    intro t' ht'
    rw [Grp.putL] at ht'
    split_ifs at ht'
    · exact ih t' ht'
    · simp at ht'

theorem putsL_out {ub : ℕ} {kss : List (List (List Bool))} {strs : List (List Bool)} {t : Tree} :
    ∀ t' ∈ putsL ub kss strs t, t' = t := by
  induction kss generalizing strs with
  | nil =>
    intro t' ht'
    rw [Grp.putsL] at ht'
    exact List.mem_singleton.1 ht'
  | cons ks kss ih =>
    intro t' ht'
    rw [Grp.putsL, List.mem_flatMap] at ht'
    obtain ⟨t1, h1, h2⟩ := ht'
    rw [putL_out t1 h1] at h2
    exact ih t' h2

theorem mem_encT {l : List Tree} {q : A × Tree} (h : q ∈ encT l) : q.2 ∈ l := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  exact ht

theorem pack_out {sep : List Bool} {ub : ℕ} {B : Body} {o : Outs S} {t : Tree} :
    ∀ q ∈ packSem A sep ub B o t, q.2 = t := by
  intro q hq
  obtain ⟨a, -, r, hr, e1, -⟩ := mem_bindW hq
  obtain ⟨b, hb, r', hr', e2, -⟩ := mem_bindW hr
  obtain ⟨d, -, r'', hr'', e3, -⟩ := mem_bindW hr'
  rw [e1, e2, e3, putsL_out _ (mem_encT hr''), putsL_out _ (mem_encT hb)]

/-- An instruction does not change the trie. -/
theorem insSem_out {T ub : ℕ} {i : Ins} {t : Tree} :
    ∀ q ∈ insSem θ mu cb kinds T ub i t, q.2 = t := by
  intro q hq
  cases i with
  | block q₁ q₂ B =>
    rw [Grp.insSem] at hq
    split_ifs at hq
    · obtain ⟨a, -, r, hr, e1, -⟩ := mem_bindW hq
      rw [e1]
      exact pack_out r hr
    · simp at hq
  | input part B => exact pack_out q hq
  | both | one =>
    rw [Grp.insSem] at hq
    split_ifs at hq
    · rw [List.mem_singleton.1 hq]
    · simp at hq
  | role j tt slots keys =>
    rw [Grp.insSem] at hq
    split at hq
    · unfold roleSem at hq
      split_ifs at hq
      · obtain ⟨a, -, r, hr, e1, -⟩ := mem_bindW hq
        rw [e1]
        exact putsL_out _ (mem_encT hr)
      · simp at hq
    · simp at hq

variable (A) in
/-- What an instruction guesses: the contents at its keys that have none. -/
def insG (ub : ℕ) : Ins → Tree → List (A × Tree)
  | .block _ _ B, t | .input _ B, t => bindW (gKss A ub B.kR t) (gKss A ub B.kC)
  | .role _ _ _ keys, t => gKss A ub keys t
  | _, t => [(1, t)]

theorem length_gBits (n : ℕ) : ∀ q ∈ gBits A n, q.2.length = n := by
  have := mem_foldL_induct (A := A)
    (f := fun (_ : Unit) (w : List Bool) => [((1 : A), true :: w), (1, false :: w)])
    (Inv := fun m w => w.length = m) (xs := List.replicate n ()) (s := []) (m := 0)
    (fun _ _ s m hs q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp [hs]) rfl
  simpa [gBits] using this

theorem TOk.gKss {ub : ℕ} {kss : List (List (List Bool))} {t : Tree} (h : TOk ub t) :
    ∀ q ∈ gKss A ub kss t, TOk ub q.2 :=
  mem_foldL_induct (Inv := fun _ t => TOk ub t) (m := 0) (fun ks _ s _ hs q hq =>
    mem_foldL_induct (Inv := fun _ t => TOk ub t) (m := 0) (fun k _ s _ hs q hq => by
      unfold gK at hq
      split_ifs at hq
      · obtain ⟨a, ha, r, hr, e1, -⟩ := mem_bindW hq
        rw [e1, List.mem_singleton.1 hr]
        exact hs.tset k a.2 (length_gBits ub a ha).le
      · rw [List.mem_singleton.1 hq]
        exact hs) hs q hq) h

theorem TOk.insG {ub : ℕ} {i : Ins} {t : Tree} (h : TOk ub t) :
    ∀ q ∈ insG A ub i t, TOk ub q.2 := by
  intro q hq
  cases i with
  | block _ _ B | input _ B =>
    obtain ⟨a, ha, r, hr, e1, -⟩ := mem_bindW hq
    rw [e1]
    exact (h.gKss a ha).gKss r hr
  | role => exact h.gKss q hq
  | both | one =>
    rw [List.mem_singleton.1 hq]
    exact h

/-- The state of GROUP. -/
def encG (T ub : ℕ) (t : Tree) : Tree := .cons (num T) (.cons (num ub) t)

/-- The programs of all roles. -/
theorem ex_kinds : ∃ (Fs : List Fm) (κ : ℕ), ∀ (j : ℕ) (z : Σ L : G.Law A, L.Ro), kinds[j]? = some z →
    ∃ F, Fs[j]? = some F ∧ ∀ (ub tt : ℕ) (slots keys : List (List (List Bool))) (t : Tree), TOk ub t →
      slots.length = (slList z.1 z.2).length →
      Does θ F (.cons (num ub) (.cons t (.cons (num tt) (.cons (keysT slots) (keysT keys)))))
        (roleSem θ z.1 z.2 ub (fun k => (tget k t).path) tt slots keys t)
        (κ * (tt * (ub + 1) + putCost ub slots + putCost ub keys + 1)) := by
  induction kinds with
  | nil => exact ⟨[], 0, fun j z h => by simp at h⟩
  | cons z₀ kinds ih =>
    obtain ⟨Fs, κ, h⟩ := ih
    obtain ⟨F, κ', h'⟩ := ex_role (θ := θ) z₀.1 z₀.2
    refine ⟨F :: Fs, max κ (2 * κ'), fun j z hj => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      refine ⟨F, rfl, fun ub tt slots keys t ht hs => ?_⟩
      refine (h' ub (fun k => (tget k t).path) tt slots keys t (fun k => (ht.path k).1) (fun k => (ht.path k).2) hs).mono ?_
      have h1 : (slots.map fun es => (es.map fun k => ub * 62 + k.length * 60 + 330).sum + 240).sum ≤ 2 * putCost ub slots := by
        unfold putCost
        rw [← List.sum_map_mul_left]
        refine List.sum_le_sum fun es _ => ?_
        have : (es.map fun k => ub * 62 + k.length * 60 + 330).sum ≤
            (es.map fun k => ub * 330 + k.length * 60 + 330).sum :=
          List.sum_le_sum fun k _ => by omega
        omega
      change κ' * (_ + _ + putCost ub keys + 1) ≤ _
      refine le_trans ?_ (Nat.mul_le_mul_right _ (le_max_right κ (2 * κ')))
      rw [mul_comm 2 κ', mul_assoc]
      exact Nat.mul_le_mul_left _ (by omega)
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      obtain ⟨F', h1, h2⟩ := h j z hj
      exact ⟨F', by simpa using h1, fun ub tt slots keys t ht hs => (h2 ub tt slots keys t ht hs).mono
        (Nat.mul_le_mul_right _ (le_max_left _ _))⟩

/-- **One instruction.** -/
theorem ex_ins (hc : (sepOf cb).length ≤ c) : ∃ F κ, ∀ (T ub : ℕ) (i : Ins) (t : Tree), InsOk S Q c kinds i → TOk ub t →
    Does θ F (.cons i.tree (encG T ub t)) ((insSem θ mu cb kinds T ub i t).map (Prod.map id (encG T ub)))
      (κ * insCost T ub i) := by
  obtain ⟨Fs, κs, hFs⟩ := ex_sim (θ := θ) mu cb
  obtain ⟨κl, hκl⟩ := exists_simSem_length (θ := θ) mu cb
  obtain ⟨Fp, κp, hFp⟩ := ex_pack (A := A) (θ := θ) (S := S) (sepOf cb) c hc
  obtain ⟨Fi, κi, hFi⟩ := ex_inOuts (θ := θ) (S := S)
  obtain ⟨Fk, κk, hFk⟩ := ex_kinds (θ := θ) kinds
  -- the formulas
  set fBlock : Fm := lett (.cons .id (lett (.cons (.hd (.tl .id)) (.hd (.tl (.hd .id)))) Fs))
    (lett (.cons (.tl .id) (.cons (.hd (.tl (.tl (.hd .id)))) (.cons (.tl (.tl (.tl (.hd .id))))
      (.tl (.tl (.hd (.hd .id))))))) Fp)
  set fInput : Fm := lett (.cons (Fi (.hd (.tl (.hd .id)))) (.cons (.hd (.tl (.tl .id))) (.cons (.tl (.tl (.tl .id)))
      (.tl (.tl (.hd .id)))))) Fp
  set fBoth : Fm := .ite (eqF (getF (.hd (.tl (.hd .id))) (.tl (.tl (.tl .id)))) (getF (.tl (.tl (.hd .id)))
      (.tl (.tl (.tl .id))))) (.tl (.tl (.tl .id))) .fail
  set fOne : Fm := .ite (eqF (getF (.hd (.tl (.hd .id))) (.tl (.tl (.tl .id)))) (.tl (.tl (.hd .id))))
      (.tl (.tl (.tl .id))) .fail
  set fs : List Fm := fBlock :: fInput :: fBoth :: fOne :: Fk.map fun G =>
    lett (.cons (.hd (.tl (.tl .id))) (.cons (.tl (.tl (.tl .id))) (.tl (.hd .id)))) G with hfs
  set sw : ℕ := (kinds.length + 5) * (kinds.length + 10)
  refine ⟨.cons (.hd (.tl .id)) (.cons (.hd (.tl (.tl .id))) (switchF (.hd (.hd .id)) fs)),
    κs + κp * (κl + 2) + κi * 10 + κk + sw + 2000, fun T ub i t hi ht => ?_⟩
  set x : Tree := .cons i.tree (encG T ub t) with hx
  have gT : Gives θ (.hd (.tl .id)) x (num T) 3 := (Gives.id _).tl.hd
  have gU : Gives θ (.hd (.tl (.tl .id))) x (num ub) 4 := (Gives.id _).tl.tl.hd
  have gt : Gives θ (.tl (.tl (.tl .id))) x t 4 := (Gives.id _).tl.tl.tl
  have gpos : 1 ≤ insCost T ub i := by
    cases i <;> simp only [insCost, bodyCost] <;> omega
  -- it is enough to make the trie
  suffices h : Does θ (switchF (.hd (.hd .id)) fs) x (insSem θ mu cb kinds T ub i t)
      ((κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900) * insCost T ub i) by
    refine ((Does.cons gT (Does.cons gU h)).replace ?_).mono ?_
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, one_mul]
      rfl
    · linarith
  -- every case ends with this bound, split by the summands of the constant
  set K := κs + κp * (κl + 2) + κi * 10 + κk + sw + 1900 with hK
  have hKN (N : ℕ) : K * N = κs * N + κp * ((κl + 2) * N) + κi * 10 * N + κk * N + sw * N + 1900 * N := by
    rw [hK]
    ring
  have hsz (k : List Bool) : (tget k t).size ≤ 4 * ub + 1 := by
    obtain ⟨a1, a2⟩ := ht.path k
    rw [a1]
    exact (size_ofBits _).trans (by omega)
  cases i with
  | block q q' B =>
    obtain ⟨hq, hq'⟩ := hi
    have g0 : Gives θ (.hd (.hd .id)) x (num 0) 3 := (Gives.id _).hd.hd
    have e1 : Gives θ (.cons (.hd (.tl .id)) (.hd (.tl (.hd .id)))) x (.cons (num T) (.cons (num q) (num q'))) 8 :=
      (Gives.cons gT (Gives.id _).hd.tl.hd).mono (by omega)
    have e2 := Does.of_gives e1 (hFs T ⟨q, hq⟩ ⟨q', hq'⟩)
    have e3 := Does.letkT (G := lett (.cons (.tl .id) (.cons (.hd (.tl (.tl (.hd .id)))) (.cons (.tl (.tl (.tl (.hd .id))))
        (.tl (.tl (.hd (.hd .id))))))) Fp) (f := fun o => packSem A (sepOf cb) ub B o t)
      (d := 30 + κp * (κl * T + flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1) + 2) e2 (by
        intro b hb
        obtain ⟨h1, h2⟩ := hκl T ⟨q, hq⟩ ⟨q', hq'⟩ b hb
        have e4 : Gives θ (.cons (.tl .id) (.cons (.hd (.tl (.tl (.hd .id)))) (.cons (.tl (.tl (.tl (.hd .id))))
            (.tl (.tl (.hd (.hd .id))))))) (.cons x (encO b.2)) (.cons (encO b.2) (.cons (num ub) (.cons t B.tree))) 30 :=
          (Gives.cons (Gives.id _).tl (Gives.cons (Gives.id _).hd.tl.tl.hd (Gives.cons (Gives.id _).hd.tl.tl.tl
            (Gives.id _).hd.hd.tl.tl))).mono (by omega)
        exact Does.of_gives e4 (hFp ub B b.2 t (κl * T) h1 h2))
    have e5 := switchF_does (θ := θ) g0 (fs := fs) (f := fBlock) rfl e3
    refine (e5.replace ?_).mono ?_
    · rw [insSem, dif_pos ⟨hq, hq'⟩]
    · simp only [insCost, bodyCost]
      set N := flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1
      have h1 : κp * (κl * T + flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1) ≤
          κp * ((κl + 2) * (T + N)) := by
        refine Nat.mul_le_mul_left _ ?_
        have : (κl + 2) * (T + N) = κl * T + κl * N + 2 * T + 2 * N := by ring
        rw [this]
        omega
      have h2 : κs * (T + 1) ≤ κs * (T + N) := Nat.mul_le_mul_left _ (by omega)
      have h3 := hKN (T + N)
      have h4 : 1 ≤ T + N := by omega
      omega
  | input part B =>
    have g0 : Gives θ (.hd (.hd .id)) x (num 1) 3 := (Gives.id _).hd.hd
    have e1 := hFi (.hd (.tl (.hd .id))) x part 4 (Gives.id _).hd.tl.hd
    have e2 := Gives.cons e1 (Gives.cons gU (Gives.cons gt (Gives.id (θ := θ) x).hd.tl.tl))
    have e3 := hFp ub B (inOuts part) t part.length (fun j => by
        unfold inOuts
        split_ifs
        · exact le_rfl
        · simp) (fun j a ha => by
        unfold inOuts at ha
        split_ifs at ha
        · exact hi a ha
        · simp at ha)
    have e4 := Does.of_gives e2 e3
    have e5 := switchF_does (θ := θ) g0 (fs := fs) (f := fInput) rfl e4
    refine e5.mono ?_
    simp only [insCost, bodyCost]
    set N := flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1 with hN
    have h1 : κp * (part.length + flen B.flags + B.kR.length + putCost ub B.kR + putCost ub B.kC + 1) ≤
        κp * ((κl + 2) * (part.length + N)) := by
      refine Nat.mul_le_mul_left _ ?_
      have : (κl + 2) * (part.length + N) = κl * (part.length + N) + 2 * part.length + 2 * N := by ring
      rw [this]
      omega
    have h3 := hKN (part.length + N)
    have h4 : 1 ≤ part.length + N := by omega
    have h5 : κi * (4 + 1) ≤ κi * 10 * (part.length + N) := by nlinarith
    omega
  | both k k' =>
    have g0 : Gives θ (.hd (.hd .id)) x (num 2) 3 := (Gives.id _).hd.hd
    have e1 := getF_gives (θ := θ) (pf := .hd (.tl (.hd .id))) (p := ofBits k) (Gives.id _).hd.tl.hd gt
    have e2 := getF_gives (θ := θ) (pf := .tl (.tl (.hd .id))) (p := ofBits k') (Gives.id _).hd.tl.tl gt
    have e3 := eqF_gives e1 e2
    rw [path_ofBits, path_ofBits, len_ofBits, len_ofBits] at e3
    have h1 := hsz k
    have h2 : Does θ fBoth x (insSem θ mu cb kinds T ub (.both k k') t) (300 * insCost T ub (.both k k')) := by
      simp only [insSem, insCost]
      by_cases h : tget k t = tget k' t
      · rw [if_pos h]
        have e4 : bit (decide (tget k t = tget k' t)) ≠ .nil := by simp [h, bit, one]
        exact (Does.ite_true e3 e4 gt).mono (by omega)
      · rw [if_neg h]
        have e4 : bit (decide (tget k t = tget k' t)) = .nil := by simp [h, bit]
        rw [e4] at e3
        exact (Does.ite_false e3 (Does.fail _)).mono (by omega)
    have e5 := switchF_does (θ := θ) g0 (fs := fs) (f := fBoth) rfl h2
    refine e5.mono ?_
    have h3 := hKN (insCost T ub (.both k k'))
    omega
  | one k w =>
    have g0 : Gives θ (.hd (.hd .id)) x (num 3) 3 := (Gives.id _).hd.hd
    have e1 := getF_gives (θ := θ) (pf := .hd (.tl (.hd .id))) (p := ofBits k) (Gives.id _).hd.tl.hd gt
    have e3 := eqF_gives e1 (Gives.id (θ := θ) x).hd.tl.tl
    rw [path_ofBits, len_ofBits] at e3
    have h1 := hsz k
    have h2 : Does θ fOne x (insSem θ mu cb kinds T ub (.one k w) t) (300 * insCost T ub (.one k w)) := by
      simp only [insSem, insCost]
      by_cases h : tget k t = ofBits w
      · rw [if_pos h]
        have e4 : bit (decide (tget k t = x.hd.tl.tl)) ≠ .nil := by
          have : tget k t = x.hd.tl.tl := h
          simp [this, bit, one]
        exact (Does.ite_true e3 e4 gt).mono (by omega)
      · rw [if_neg h]
        have e4 : bit (decide (tget k t = x.hd.tl.tl)) = .nil := by
          have : ¬ tget k t = x.hd.tl.tl := h
          simp [this, bit]
        rw [e4] at e3
        exact (Does.ite_false e3 (Does.fail _)).mono (by omega)
    have e5 := switchF_does (θ := θ) g0 (fs := fs) (f := fOne) rfl h2
    refine e5.mono ?_
    have h3 := hKN (insCost T ub (.one k w))
    omega
  | role j tt slots keys =>
    obtain ⟨z, hz, hsl⟩ := hi
    obtain ⟨G, hG, hG'⟩ := hFk j z hz
    have hj : j < kinds.length := by
      by_contra h
      rw [List.getElem?_eq_none (not_lt.1 h)] at hz
      simp at hz
    have g0 : Gives θ (.hd (.hd .id)) x (num (4 + j)) 3 := (Gives.id _).hd.hd
    have e1 := Gives.cons gU (Gives.cons gt (Gives.id (θ := θ) x).hd.tl)
    have e2 := Does.of_gives e1 (hG' ub tt slots keys t ht hsl)
    have hf : fs[4 + j]? = some (lett (.cons (.hd (.tl (.tl .id))) (.cons (.tl (.tl (.tl .id))) (.tl (.hd .id)))) G) := by
      rw [hfs, add_comm]
      simp [hG]
    have e5 := switchF_does (θ := θ) g0 hf e2
    refine (e5.replace ?_).mono ?_
    · rw [insSem, hz]
    · simp only [insCost]
      set N := tt * (ub + 1) + putCost ub slots + putCost ub keys + 1
      have h1 : (4 + j + 1) * (3 + (4 + j) + 1) ≤ sw * N := by
        have h2 : (4 + j + 1) * (3 + (4 + j) + 1) ≤ sw := Nat.mul_le_mul (by omega) (by omega)
        have h3 : 1 ≤ N := by omega
        nlinarith
      have h3 := hKN N
      have h4 : 1 ≤ N := by omega
      omega

/-- The guessing program of one instruction: argument (instruction, (T, (yardstick, trie))). -/
def insGF : Fm := .cons (.hd (.tl .id)) (.ite (.tl (.hd (.hd .id)))
  (.ite (.tl (.tl (.tl (.hd (.hd .id)))))
    (gKssF (.tl (.tl .id)) (.tl (.tl (.tl (.hd .id))))) (.tl (.tl .id)))
  (lett (.cons .id (gKssF (.tl (.tl .id)) (.hd (.tl (.tl (.tl (.hd .id)))))))
    (gKssF (.tl .id) (.tl (.tl (.tl (.tl (.hd (.hd .id)))))))))

theorem insGF_does (T ub : ℕ) (i : Ins) (t : Tree) :
    Does θ insGF (.cons i.tree (encG T ub t)) ((insG A ub i t).map (Prod.map id (encG T ub)))
      (2 * insCost T ub i + 100) := by
  refine ((Does.cons (Gives.id _).tl.hd
    (?_ : Does θ _ _ ((insG A ub i t).map (Prod.map id fun t => .cons (num ub) t))
      (2 * insCost T ub i + 90))).replace ?_).mono (by omega)
  · cases i with
    | block _ _ B | input _ B =>
      refine (Does.ite_false (Gives.id _).hd.hd.tl ((Does.letkT
        (f := fun t1 => (gKss A ub B.kC t1).map (Prod.map id fun t => .cons (num ub) t))
        (gKssF_does (θ := θ) ub B.kR t (Gives.id _).tl.tl (Gives.id _).hd.tl.tl.tl.hd)
        fun b _ => gKssF_does ub B.kC b.2 (Gives.id _).tl (Gives.id _).hd.hd.tl.tl.tl.tl).replace
        (bindW_map _ _ _))).mono ?_
      simp only [insCost, bodyCost]
      omega
    | both | one =>
      exact (Does.ite_true (Gives.id _).hd.hd.tl (by simp [Ins.tree, num])
        (Does.ite_false (Gives.id _).hd.hd.tl.tl.tl (Gives.id _).tl.tl)).mono (by omega)
    | role j tt slots keys =>
      refine (Does.ite_true (Gives.id _).hd.hd.tl (by simp [Ins.tree, Nat.add_comm 4 j, num])
        (Does.ite_true (Gives.id _).hd.hd.tl.tl.tl (by simp [Ins.tree, Nat.add_comm 4 j, num])
          (gKssF_does (A := A) ub keys t (Gives.id _).tl.tl (Gives.id _).hd.tl.tl.tl))).mono ?_
      simp only [insCost]
      omega
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, one_mul]
    rfl

variable (θ) in
/-- What a script does with a trie. -/
noncomputable def scriptSem (T ub : ℕ) (l : List Ins) (t : Tree) : List (A × Tree) :=
  foldL (insSem θ mu cb kinds T ub) l t

/-- **The program GROUP**: it guesses the contents at all keys, then every instruction compares. -/
theorem ex_group (hc : (sepOf cb).length ≤ c) : ∃ F κ, ∀ (bT bub : List Bool) (l : List Ins),
    (∀ i ∈ l, InsOk S Q c kinds i) →
    Does θ F (scriptT bT bub l)
      ((bindW (foldL (insG A (bval bub)) l .nil)
          (scriptSem θ mu cb kinds (bval bT) (bval bub) l)).map
        (Prod.map id (encG (bval bT) (bval bub))))
      (κ * ((bT.length + 1) * (bval bT + 1) + (bub.length + 1) * (bval bub + 1) +
        (l.map (insCost (bval bT) (bval bub))).sum + l.length)) := by
  obtain ⟨F, κ, hF⟩ := ex_ins (θ := θ) mu cb kinds hc
  refine ⟨lett
    (.cons .id (foldF insGF
      (.cons (unF (.hd (.hd .id))) (.cons (unF (.tl (.hd .id))) (.quote .nil))) (.tl .id)))
    (foldF F (.tl .id) (.tl (.hd .id))), κ + 500, fun bT bub l hl => ?_⟩
  have g1 : Gives θ (.hd (.hd .id)) (scriptT bT bub l) (ofBits bT) 3 := (Gives.id _).hd.hd
  have g2 : Gives θ (.tl (.hd .id)) (scriptT bT bub l) (ofBits bub) 3 := (Gives.id _).hd.tl
  have h0 := Gives.cons (unF_gives g1) (Gives.cons (unF_gives g2) (Gives.quote .nil (scriptT bT bub l)))
  have h1 := foldT (θ := θ) (enc := encG (bval bT) (bval bub)) (s₀ := .nil) (f := insG A (bval bub))
    (Inv := fun _ _ => True) (d := fun i => 2 * insCost (bval bT) (bval bub) i + 100) (l := .tl .id)
    (x := scriptT bT bub l) h0 (Gives.id _).tl
    (fun i _ t _ _ => ⟨insGF_does _ _ i t, fun _ _ => trivial⟩) trivial
  have hok : ∀ b ∈ foldL (insG A (bval bub)) l .nil, TOk (bval bub) b.2 := by
    have := mem_foldL_induct (f := insG A (bval bub)) (Inv := fun _ t => TOk (bval bub) t)
      (xs := l) (m := 0) (fun i _ s _ hs q hq => hs.insG q hq) (tOk_nil _)
    exact this
  have h2 := Does.letkT (G := foldF F (.tl .id) (.tl (.hd .id)))
    (f := fun t => (scriptSem θ mu cb kinds (bval bT) (bval bub) l t).map
      (Prod.map id (encG (bval bT) (bval bub))))
    (d := 2 + 3 + (l.map fun i => κ * insCost (bval bT) (bval bub) i + 0 + 30).sum + 20) h1
    (fun b hb =>
      foldT (θ := θ) (enc := encG (bval bT) (bval bub)) (s₀ := b.2)
        (f := insSem θ mu cb kinds (bval bT) (bval bub))
        (Inv := fun _ t => TOk (bval bub) t) (d := fun i => κ * insCost (bval bT) (bval bub) i + 0)
        (Gives.id _).tl (Gives.id _).hd.tl
        (fun i _ t hi ht => ⟨hF _ _ i t (hl i hi) ht, fun q hq => insSem_out mu cb kinds q hq ▸ ht⟩)
        (hok b hb))
  rw [bindW_map] at h2
  refine h2.mono ?_
  have hs : ∀ (a b : ℕ) (l : List Ins),
      (l.map fun i => a * insCost (bval bT) (bval bub) i + b + 30).sum =
        a * (l.map (insCost (bval bT) (bval bub))).sum + (b + 30) * l.length := by
    intro a b l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      ring
  rw [hs, hs κ 0 l]
  set P := (bT.length + 1) * (bval bT + 1) with hP
  set R := (bub.length + 1) * (bval bub + 1) with hR
  set Sm := (l.map (insCost (bval bT) (bval bub))).sum
  have p1 : bT.length * (bval bT * 62 + 130) ≤ 130 * P := by rw [hP]; nlinarith
  have p2 : bub.length * (bval bub * 62 + 130) ≤ 130 * R := by rw [hR]; nlinarith
  have p3 : 1 ≤ P := Nat.succ_le_of_lt (by positivity)
  have p4 : (κ + 500) * (P + R + Sm + l.length) =
      κ * (P + R + l.length) + κ * Sm + 500 * (P + R + Sm + l.length) := by ring
  omega

end group

end Nc.Grp
