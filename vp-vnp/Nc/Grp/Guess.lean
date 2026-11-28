/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.Pack

/-!
# Guessing the contents

Before it compares, GROUP guesses the content at every key that has none.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

variable (A) in
/-- All lists of `n` bits. -/
def gBits (n : ℕ) : List (A × List Bool) :=
  foldL (fun (_ : Unit) (w : List Bool) => [(1, true :: w), (1, false :: w)])
    (List.replicate n ()) []

variable (A) in
/-- Guess the content at a key that has none. -/
def gK (ub : ℕ) (k : List Bool) (t : Tree) : List (A × Tree) :=
  if tget k t = .nil then bindW (gBits A ub) fun w => [(1, tset k (ofBits w) t)] else [(1, t)]

variable (A) in
/-- Guess the contents at the keys of several lists. -/
def gKss (ub : ℕ) (kss : List (List (List Bool))) (t : Tree) : List (A × Tree) :=
  foldL (fun ks t => foldL (gK A ub) ks t) kss t

/-- Step of the guessing program: argument (key, (yardstick, trie)). -/
def gStep : Fm :=
  .cons (.hd (.tl .id)) (.ite (getF (.hd .id) (.tl (.tl .id))) (.tl (.tl .id))
    (lett
      (.cons .id (foldF (.ite .guess (.cons (.quote one) (.tl .id)) (.cons (.quote .nil) (.tl .id)))
        (.quote .nil) (.hd (.tl .id))))
      (setF (.hd (.hd .id)) (.tl .id) (.tl (.tl (.hd .id))))))

theorem gStep_does (ub : ℕ) (k : List Bool) (t : Tree) :
    Does θ gStep (.cons (ofBits k) (.cons (num ub) t))
      ((gK A ub k t).map (Prod.map id fun t => .cons (num ub) t))
      (ub * 40 + k.length * 90 + 150) := by
  set x : Tree := .cons (ofBits k) (.cons (num ub) t)
  have h1 := getF_gives (θ := θ) (x := x) (pf := .hd .id) (tf := .tl (.tl .id)) (p := ofBits k)
    (t := t) (Gives.id _).hd (Gives.id _).tl.tl
  rw [path_ofBits, len_ofBits] at h1
  have hU : Gives θ (.hd (.tl .id)) x (num ub) 3 := (Gives.id _).tl.hd
  refine ((Does.cons hU
    (?_ : Does θ _ x (gK A ub k t) (ub * 40 + k.length * 90 + 140))).replace ?_).mono (by omega)
  · by_cases hk : tget k t = .nil
    · rw [gK, if_pos hk]
      rw [hk] at h1
      have hy : Gives θ (.hd (.tl .id)) x (listT ((List.replicate ub ()).map fun _ => .nil)) 3 := by
        rw [List.map_replicate, ← num_eq_listT]
        exact hU
      have h2 := foldT (θ := θ) (encE := fun _ : Unit => (.nil : Tree)) (enc := ofBits) (s₀ := [])
        (f := fun _ w => [((1 : A), true :: w), (1, false :: w)]) (Inv := fun _ _ => True)
        (d := fun _ => 6) (Gives.quote .nil x) hy (fun _ _ w _ _ => ⟨by
          have a1 : Gives θ (.cons (.quote one) (.tl .id)) (.cons .nil (ofBits w))
              (ofBits (true :: w)) 4 :=
            Gives.cons (Gives.quote _ _) (Gives.id _).tl
          have a2 : Gives θ (.cons (.quote .nil) (.tl .id)) (.cons .nil (ofBits w))
              (ofBits (false :: w)) 4 :=
            Gives.cons (Gives.quote _ _) (Gives.id _).tl
          exact Does.either a1 a2, fun _ _ => trivial⟩) trivial
      have h3 := Does.letkT (f := fun w => [((1 : A), tset k (ofBits w) t)])
        (d := 60 * k.length + 40) h2 (by
          intro b _
          have := setF_gives (θ := θ) (x := .cons x (ofBits b.2)) (pf := .hd (.hd .id))
            (vf := .tl .id) (tf := .tl (.tl (.hd .id))) (p := ofBits k) (v := ofBits b.2) (t := t)
            (Gives.id _).hd.hd (Gives.id _).tl (Gives.id _).hd.tl.tl
          rw [path_ofBits, len_ofBits] at this
          exact this.mono (by omega))
      refine (Does.ite_false h1 h3).mono ?_
      simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
      omega
    · rw [gK, if_neg hk]
      exact (Does.ite_true h1 hk (Gives.id _).tl.tl).mono (by omega)
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, one_mul]
    rfl

/-- Guess the contents at the keys of several lists: `s` gives (yardstick, trie), `l` the lists. -/
def gKssF (s l : Fm) : Fm := foldF (foldF gStep (.tl .id) (.hd .id)) s l

theorem gKssF_does {s l : Fm} {x : Tree} {cs cl : ℕ} (ub : ℕ) (kss : List (List (List Bool)))
    (t : Tree) (hs : Gives θ s x (.cons (num ub) t) cs) (hl : Gives θ l x (keysT kss) cl) :
    Does θ (gKssF s l) x ((gKss A ub kss t).map (Prod.map id fun t => .cons (num ub) t))
      (cs + cl + 2 * putCost ub kss + 20) := by
  refine (foldT (θ := θ) (encE := fun ks : List (List Bool) => listT (ks.map ofBits))
    (enc := fun t => .cons (num ub) t) (f := fun ks t => foldL (gK A ub) ks t)
    (Inv := fun _ _ => True)
    (d := fun ks => (ks.map fun k => ub * 40 + k.length * 90 + 150 + 30).sum + 30) hs hl
    (fun ks _ t _ _ => ⟨?_, fun _ _ => trivial⟩) trivial).mono ?_
  · refine (foldT (θ := θ) (encE := ofBits) (enc := fun t => .cons (num ub) t) (f := gK A ub)
      (Inv := fun _ _ => True) (d := fun k => ub * 40 + k.length * 90 + 150)
      (Gives.id _).tl (Gives.id _).hd
      (fun k _ t _ _ => ⟨gStep_does ub k t, fun _ _ => trivial⟩) trivial).mono (by omega)
  · unfold putCost
    rw [← List.sum_map_mul_left]
    refine Nat.add_le_add_right (Nat.add_le_add_left (List.sum_le_sum fun ks _ => ?_) _) _
    have : (ks.map fun k => ub * 40 + k.length * 90 + 150 + 30).sum ≤
        2 * (ks.map fun k => ub * 330 + k.length * 60 + 330).sum := by
      rw [← List.sum_map_mul_left]
      exact List.sum_le_sum fun k _ => by omega
    omega

end Nc.Grp
