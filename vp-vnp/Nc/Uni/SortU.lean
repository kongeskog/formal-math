/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.Alpha

/-!
# The sorting loop
-/

set_option linter.unusedSectionVars false

namespace Nc.Uni

open Finset

variable {A : Type*} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K]

/-- The list tape, read. -/
abbrev lsT : Zc K := .tp .ls true
/-- The list tape, written. -/
abbrev lsF : Zc K := .tp .ls false

/-- A record on the list: flag, letters and mark, end. -/
def rw' (f : Bool) (w : List (Option (Bl K))) : List (Sy M K) := .flag f :: (w.map ol ++ [.dot])

/-- Letters other than the end of a block. -/
abbrev NB (M K : Type) := {γ : Sy M K // γ ≠ .bar}

/-- Rounds of the distribution: flag, first letter, the others. -/
abbrev Dr (K : Type) := Bool × Bl K × List (Option (Bl K))

/-- Emissions of a round of the distribution. -/
def emDr (d : Dr K) : Zc K → List (Sy M K) := fun z =>
  on {lsT} (rw' d.1 (some d.2.1 :: d.2.2)) z ++ on {.tp (.bk d.2.1) false} (rw' d.1 (d.2.2 ++ [some d.2.1])) z

-- What `on` means and how a record ends: the tape cases of the `Runs` proofs below.
attribute [local simp] on ol

theorem runs_dr : Runs (emDr : Dr K → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h := Runs.sum (F := A) fun b : Bl K =>
    (((Runs.pick (F := A) (Z := Zc K) (fun f : Bool => on {lsT, .tp (.bk b) false} [(Sy.flag f : Sy M K)]) (fun _ => 1)).mul
    (Runs.const (F := A) (on {lsT} [(be b : Sy M K)]))).mul
    (Runs.wordstar (F := A) {lsT, .tp (.bk b) false} ⟨lsT, by simp⟩ (ol : Option (Bl K) → Sy M K))).mul
    (Runs.const (F := A) fun z : Zc K => on {lsT} [(Sy.dot : Sy M K)] z ++ on {.tp (.bk b) false} [be b, Sy.dot] z)
  refine h.congr ⟨fun d => ⟨d.2.1, (((d.1, ()), d.2.2), ())⟩, fun y => (y.2.1.1.1, y.1, y.2.1.2), fun d => rfl,
    fun y => rfl⟩ (fun d z => ?_) fun d => by simp
  obtain ⟨f, b, w⟩ := d
  simp only [Equiv.coe_fn_mk, emDr, rw']
  by_cases h1 : z = lsT
  · subst h1
    simp
  · by_cases h2 : z = .tp (.bk b) false
    · subst h2
      simp
    · simp [h1, h2]

/-- The channels where a pass of the distribution ends a block. -/
def barSet : Finset (Zc K) := insert lsT (univ.image fun b : Bl K => (.tp (.bk b) false : Zc K))

/-- Runs of a pass. -/
abbrev Ps (M K : Type) := List (Dr K) × (Bl K → List (NB M K))

/-- The letters of records, in some order. -/
noncomputable def bsl (K : Type) [Fintype K] [DecidableEq K] : List (Bl K) := List.ofFn (Fintype.equivFin (Bl K)).symm

theorem mem_bsl (b : Bl K) : b ∈ bsl K := by
  rw [bsl, List.mem_ofFn]
  exact ⟨Fintype.equivFin (Bl K) b, by simp⟩

theorem bsl_nodup : (bsl K).Nodup := by
  rw [bsl, List.nodup_ofFn]
  exact Equiv.injective _

/-- Emissions of the collection. -/
noncomputable def emCo (m : Bl K → List (NB M K)) : Zc K → List (Sy M K) := fun z =>
  (List.ofFn fun i => on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF}
      ((m ((Fintype.equivFin (Bl K)).symm i)).map Subtype.val) z ++
    on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true} [Sy.bar] z).flatten ++ on {lsF} [Sy.bar] z

theorem runs_co : Runs (emCo : (Bl K → List (NB M K)) → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h0 : ∀ i : Fin (Fintype.card (Bl K)), Runs
      (fun (w : List (NB M K)) (z : Zc K) => on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF}
        (w.map Subtype.val) z ++ on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true} [Sy.bar] z)
      (fun _ => (1 : A)) := by
    intro i
    have h1 := (Runs.wordstar (Z := Zc K) {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF}
      ⟨lsF, by simp⟩ (Subtype.val : NB M K → Sy M K)).mul
      (Runs.const (F := A) (Z := Zc K) (on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true} [(Sy.bar : Sy M K)]))
    exact h1.congr ⟨fun w => (w, ()), Prod.fst, fun w => rfl, fun y => rfl⟩ (fun w z => rfl) fun w => by simp
  have h := (Runs.pi h0).mul (Runs.const (Z := Zc K) (on {lsF} [(Sy.bar : Sy M K)]))
  refine h.congr ⟨fun m => ((fun i => m ((Fintype.equivFin (Bl K)).symm i)), ()),
    fun y b => y.1 (Fintype.equivFin (Bl K) b), fun m => by simp, fun y => by simp⟩ (fun m z => rfl) fun m => ?_
  simp

/-- Emissions of a pass. -/
noncomputable def emPs (p : Ps M K) : Zc K → List (Sy M K) := fun z =>
  (p.1.flatMap fun d => emDr d z) ++ (on barSet [Sy.bar] z ++ emCo p.2 z)

theorem emDr_ne (d : Dr K) : ∃ z, (emDr d : Zc K → List (Sy M K)) z ≠ [] := ⟨lsT, by simp [emDr, rw']⟩

theorem runs_ps : Runs (emPs : Ps M K → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h := ((runs_dr (A := A) (M := M) (K := K)).kstar fun d => emDr_ne d).mul
    ((Runs.const (Z := Zc K) (on barSet [(Sy.bar : Sy M K)])).mul (runs_co))
  refine h.congr ⟨fun p => (p.1, (), p.2), fun y => (y.1, y.2.2), fun p => rfl, fun y => rfl⟩ (fun p z => rfl)
    fun p => ?_
  simp

/-- Emissions of the last reading: the marks are in front and are dropped. -/
def emFi (l : List (Bool × List (Bl K))) : Zc K → List (Sy M K) := fun z =>
  (l.flatMap fun d => on {lsT} (rw' d.1 (none :: d.2.map some)) z ++
    on {.tp (.cm false) false, .tp (.cm true) false} (rw' d.1 (d.2.map some)) z) ++ on {lsT} [Sy.bar] z

theorem runs_fi : Runs (emFi : List (Bool × List (Bl K)) → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h1 := (((Runs.pick (F := A) (Z := Zc K)
      (fun f : Bool => on {lsT, .tp (.cm false) false, .tp (.cm true) false} [(Sy.flag f : Sy M K)]) (fun _ => 1)).mul
    (Runs.const (F := A) (on {lsT} [(Sy.mark : Sy M K)]))).mul
    (Runs.wordstar (F := A) {lsT, .tp (.cm false) false, .tp (.cm true) false} ⟨lsT, by simp⟩ (be : Bl K → Sy M K))).mul
    (Runs.const (F := A) (on {lsT, .tp (.cm false) false, .tp (.cm true) false} [(Sy.dot : Sy M K)]))
  have h2 := h1.congr (em' := fun (d : Bool × List (Bl K)) z => on {lsT} (rw' d.1 (none :: d.2.map some)) z ++
    on {.tp (.cm false) false, .tp (.cm true) false} (rw' d.1 (d.2.map some)) z) (wt' := fun _ => 1)
    ⟨fun d => (((d.1, ()), d.2), ()), fun y => (y.1.1.1, y.1.2), fun d => rfl, fun y => rfl⟩ (fun d z => by
      obtain ⟨f, w⟩ := d
      have hw : (w.map some).map (ol : Option (Bl K) → Sy M K) = w.map be := by
        rw [List.map_map]; rfl
      simp only [Equiv.coe_fn_mk, rw', List.map_cons, hw]
      by_cases h1 : z = lsT
      · subst h1
        simp
      · by_cases h2 : z = .tp (.cm false) false
        · subst h2
          simp
        · by_cases h3 : z = .tp (.cm true) false
          · subst h3
            simp
          · simp [h1, h2, h3]) (fun d => by simp)
  have h3 := (h2.kstar fun d => ⟨lsT, by simp [rw']⟩).mul (Runs.const (Z := Zc K) (on {lsT} [(Sy.bar : Sy M K)]))
  exact h3.congr ⟨fun l => (l, ()), Prod.fst, fun l => rfl, fun y => rfl⟩ (fun l z => rfl) fun l => by simp

end Nc.Uni
