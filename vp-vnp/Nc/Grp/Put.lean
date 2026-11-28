/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.PutDef
import Nc.Grp.Seg

/-!
# Comparing units with the stored contents: programs
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- Results without weights. -/
abbrev encT (l : List Tree) : List (A × Tree) := l.map fun t => ((1 : A), t)

theorem reverse_gives {l : Fm} {x : Tree} {c : ℕ} {w : List Bool} (h : Gives θ l x (ofBits w) c) (v : List Bool) :
    Gives θ (foldF .id (.quote (ofBits v)) l) x (ofBits (w.reverse ++ v)) (c + w.length * 31 + 21) := by
  rw [← listT_ofBits w] at h
  have := rev_gives (Gives.quote (θ := θ) (listT (v.map bit)) x) h
  rw [← List.map_reverse, ← List.map_append, List.length_map, listT_ofBits, listT_ofBits] at this
  exact this.mono (by omega)

/-- Take the bits of a unit: argument (rest, accumulator), yardstick `num ub`. -/
def unitStep : Fm := .cons (.tl (.hd (.tl .id))) (.cons (.hd (.hd (.tl .id))) (.tl (.tl .id)))

theorem replicate_append_cons (n : ℕ) (acc : List Bool) :
    List.replicate n false ++ false :: acc = false :: (List.replicate n false ++ acc) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem foldl_unit (ub : ℕ) (r acc : List Bool) :
    (List.replicate ub ()).foldl (fun (s : List Bool × List Bool) _ => (s.1.tail, s.1.headD false :: s.2)) (r, acc) =
      (r.drop ub, (padTake ub r).reverse ++ acc) := by
  induction ub generalizing r acc with
  | zero => simp [padTake]
  | succ ub ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    cases r with
    | nil => simp [padTake, List.replicate_succ, replicate_append_cons]
    | cons b r => simp [padTake]

theorem unit_gives {s y : Fm} {x : Tree} {cs cy ub : ℕ} {r : List Bool} (hs : Gives θ s x (ofBits r) cs)
    (hy : Gives θ y x (num ub) cy) :
    Gives θ (foldF unitStep (.cons s (.quote .nil)) y) x (.cons (ofBits (r.drop ub)) (ofBits (padTake ub r).reverse))
      (cs + cy + ub * 50 + 40) := by
  have h0 : Gives θ (.cons s (.quote .nil)) x (.cons (ofBits r) (ofBits [])) (cs + 1 + 1) :=
    Gives.cons hs (Gives.quote _ _)
  have hy' : Gives θ y x (listT ((List.replicate ub ()).map fun _ => .nil)) cy := by
    rw [List.map_replicate, ← num_eq_listT]
    exact hy
  have := foldTG (θ := θ) (encE := fun _ : Unit => (.nil : Tree))
    (enc := fun s : List Bool × List Bool => .cons (ofBits s.1) (ofBits s.2)) (s₀ := (r, []))
    (g := fun _ s => (s.1.tail, s.1.headD false :: s.2)) (Inv := fun _ _ => True) (d := fun _ => 20)
    h0 hy' (fun _ _ s _ _ => ⟨by
      have h1 : Gives θ (.tl (.hd (.tl .id))) (.cons .nil (.cons (ofBits s.1) (ofBits s.2))) (ofBits s.1.tail) 4 := by
        rw [← ofBits_tl]
        exact (Gives.id _).tl.hd.tl
      have h2 : Gives θ (.hd (.hd (.tl .id))) (.cons .nil (.cons (ofBits s.1) (ofBits s.2))) (bit (s.1.headD false)) 4 := by
        rw [← ofBits_hd]
        exact (Gives.id _).tl.hd.hd
      exact (Gives.cons h1 (Gives.cons h2 (Gives.id _).tl.tl)).mono (by omega), trivial⟩) trivial
  rw [foldl_unit, List.append_nil] at this
  refine this.mono ?_
  simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
  omega

/-- Step of the comparing program: argument (key, (yardstick, (rest, trie))). -/
def putStep : Fm := .ite (.hd (.tl (.tl .id)))
  (lett (.cons .id (foldF unitStep (.cons (.hd (.tl (.tl .id))) (.quote .nil)) (.hd (.tl .id))))
    (.ite (eqF (foldF .id (.quote (ofBits [])) (.tl (.tl .id))) (getF (.hd (.hd .id)) (.tl (.tl (.tl
        (.hd .id))))))
      (.cons (.hd (.tl (.hd .id))) (.cons (.hd (.tl .id)) (.tl (.tl (.tl (.hd .id)))))) .fail))
  .fail

variable (A) in
/-- One key. -/
def putOne (ub : ℕ) (k : List Bool) (s : List Bool × Tree) : List (A × (List Bool × Tree)) :=
  if s.1 ≠ [] ∧ ofBits (padTake ub s.1) = tget k s.2 then [(1, (s.1.drop ub, s.2))] else []

theorem length_padTake (ub : ℕ) (r : List Bool) : (padTake ub r).length = ub := by
  simp only [padTake, List.length_append, List.length_take, List.length_replicate]
  omega

theorem putStep_does (ub : ℕ) (k : List Bool) (s : List Bool × Tree) :
    Does θ putStep (.cons (ofBits k) (.cons (num ub) (.cons (ofBits s.1) s.2)))
      ((putOne A ub k s).map (Prod.map id fun s => .cons (num ub) (.cons (ofBits s.1) s.2)))
      (ub * 330 + k.length * 60 + 300) := by
  obtain ⟨r, t⟩ := s
  cases r with
  | nil =>
    refine (Does.ite_false (Gives.id _).tl.tl.hd ?_).mono (c := 4 + 0 + 1) (by omega)
    simpa [putOne] using Does.fail (θ := θ) (.cons (ofBits k) (.cons (num ub) (.cons (ofBits []) t)))
  | cons b r =>
    set x : Tree := .cons (ofBits k) (.cons (num ub) (.cons (ofBits (b :: r)) t))
    have h1 := unit_gives (θ := θ) (x := x) (r := b :: r)
      (s := .hd (.tl (.tl .id))) (y := .hd (.tl .id)) (Gives.id _).tl.tl.hd (Gives.id _).tl.hd
    set x' : Tree := .cons x (.cons (ofBits ((b :: r).drop ub)) (ofBits (padTake ub (b ::
        r)).reverse))
    have h2 := reverse_gives (θ := θ) (x := x') (l := .tl (.tl .id))
      (w := (padTake ub (b :: r)).reverse) (Gives.id _).tl.tl []
    rw [List.reverse_reverse, List.append_nil] at h2
    have h3 := getF_gives (θ := θ) (x := x') (pf := .hd (.hd .id)) (tf := .tl (.tl (.tl (.hd .id))))
        (p := ofBits k)
      (t := t) (Gives.id _).hd.hd (Gives.id _).hd.tl.tl.tl
    rw [path_ofBits, len_ofBits] at h3
    have h4 := eqF_gives h2 h3
    have hsz := size_ofBits (padTake ub (b :: r))
    rw [List.length_reverse, length_padTake] at h4
    rw [length_padTake] at hsz
    have h5 : Gives θ (.cons (.hd (.tl (.hd .id))) (.cons (.hd (.tl .id)) (.tl (.tl (.tl (.hd
        .id)))))) x'
        (.cons (num ub) (.cons (ofBits ((b :: r).drop ub)) t)) 14 :=
      (Gives.cons (Gives.id _).hd.tl.hd (Gives.cons (Gives.id _).tl.hd (Gives.id
          _).hd.tl.tl.tl)).mono (by omega)
    by_cases he : ofBits (padTake ub (b :: r)) = tget k t
    · have h6 := Does.ite_true (H := .fail) h4 (by simp [he, bit, one]) h5
      have h7 := Does.letk h1 (R := fun _ => [((1 : A), .cons (num ub) (.cons (ofBits ((b :: r).drop
          ub)) t))])
        (fun q hq => by rw [List.mem_singleton.1 hq]; exact h6)
      refine ((Does.ite_true (Gives.id _).tl.tl.hd (by show ofBits (b :: r) ≠ .nil; simp [ofBits])
          h7).replace ?_).mono
        (by omega)
      simp [putOne, he, bindW]
    · have hb : bit (decide (ofBits (padTake ub (b :: r)) = tget k t)) = .nil := by simp [he, bit]
      rw [hb] at h4
      have h6 := Does.ite_false (G := .cons (.hd (.tl (.hd .id))) (.cons (.hd (.tl .id)) (.tl (.tl
          (.tl (.hd .id))))))
        h4 (Does.fail (θ := θ) x')
      have h7 := Does.letk h1 (R := fun _ => ([] : List (A × Tree))) (fun q hq => by
        rw [List.mem_singleton.1 hq]; exact h6)
      refine ((Does.ite_true (Gives.id _).tl.tl.hd (by show ofBits (b :: r) ≠ .nil; simp [ofBits])
          h7).replace ?_).mono
        (by omega)
      simp [putOne, he, bindW]

/-- Compare the units of a string: argument (yardstick, (keys, (rest, trie))). -/
def putF : Fm := lett (foldF putStep (.cons (.hd .id) (.tl (.tl .id))) (.hd (.tl .id)))
  (.ite (.hd (.tl .id)) .fail (.tl (.tl .id)))

theorem bind_putOne (ub : ℕ) (keys : List (List Bool)) (r : List Bool) (t : Tree) :
    bindW (foldL (putOne A ub) keys (r, t)) (fun s => if s.1 = [] then [((1 : A), s.2)] else []) =
      encT (putL ub keys r t) := by
  induction keys generalizing r with
  | nil =>
    rw [foldL, bindW_single, putL]
    by_cases h : r = [] <;> simp [h]
  | cons k ks ih =>
    rw [foldL, putOne, putL]
    split_ifs
    · rw [bindW_single]
      exact ih _
    · rfl

theorem putF_does (ub : ℕ) (keys : List (List Bool)) (r : List Bool) (t : Tree) :
    Does θ putF (.cons (num ub) (.cons (listT (keys.map ofBits)) (.cons (ofBits r) t)))
      (encT (putL ub keys r t)) ((keys.map fun k => ub * 330 + k.length * 60 + 330).sum + 100) := by
  have h1 := foldT (θ := θ)
    (enc := fun s : List Bool × Tree => .cons (num ub) (.cons (ofBits s.1) s.2)) (s₀ := (r, t)) (f := putOne A ub)
    (Inv := fun _ _ => True) (d := fun k => ub * 330 + k.length * 60 + 300)
    (s := .cons (.hd .id) (.tl (.tl .id))) (l := .hd (.tl .id))
    (x := .cons (num ub) (.cons (listT (keys.map ofBits)) (.cons (ofBits r) t)))
    (Gives.cons (Gives.id _).hd (Gives.id _).tl.tl) (Gives.id _).tl.hd
    (fun k _ s _ _ => ⟨putStep_does ub k s, fun _ _ => trivial⟩) trivial
  have h2 := Does.lettT (G := .ite (.hd (.tl .id)) .fail (.tl (.tl .id)))
    (f := fun s => if s.1 = [] then [((1 : A), s.2)] else []) (d := 20) h1 (by
      rintro ⟨a, r, t⟩ -
      cases r with
      | nil => exact (Does.ite_false (Gives.id _).tl.hd (Gives.id _).tl.tl).mono (by omega)
      | cons b r => exact (Does.ite_true (Gives.id _).tl.hd (by simp [ofBits]) (Does.fail _)).mono (by omega))
  rw [bind_putOne] at h2
  refine h2.mono ?_
  linarith

/-- Step for several strings: argument (keys, (yardstick, (strings, trie))). -/
def putsStep : Fm := .cons (.hd (.tl .id)) (.cons (.tl (.hd (.tl (.tl .id))))
  (lett (.cons (.hd (.tl .id)) (.cons (.hd .id) (.cons (.hd (.hd (.tl (.tl .id)))) (.tl (.tl (.tl .id)))))) putF))

/-- Write several strings: argument (yardstick, (lists of keys, (strings, trie))). -/
def putsF : Fm := lett (foldF putsStep (.cons (.hd .id) (.tl (.tl .id))) (.hd (.tl .id))) (.tl (.tl .id))

theorem bind_puts (ub : ℕ) (kss : List (List (List Bool))) (strs : List (List Bool)) (t : Tree) :
    bindW (foldL (fun ks (s : List (List Bool) × Tree) => (putL ub ks (s.1.headD []) s.2).map fun t =>
      ((1 : A), (s.1.tail, t))) kss (strs, t)) (fun s => [((1 : A), s.2)]) = encT (putsL ub kss strs t) := by
  induction kss generalizing strs t with
  | nil => rw [foldL, bindW_single, putsL]; rfl
  | cons ks kss ih =>
    rw [foldL, putsL, bindW_assoc, bindW_pure]
    show _ = List.map _ (List.flatMap _ _)
    rw [List.map_flatMap]
    exact List.flatMap_congr fun t _ => ih _ _

theorem putsF_does (ub : ℕ) (kss : List (List (List Bool))) (strs : List (List Bool)) (t : Tree) :
    Does θ putsF (.cons (num ub) (.cons (listT (kss.map fun ks => listT (ks.map ofBits)))
        (.cons (listT (strs.map ofBits)) t))) (encT (putsL ub kss strs t))
      ((kss.map fun ks => (ks.map fun k => ub * 330 + k.length * 60 + 330).sum + 200).sum + 100) :=
          by
  have h1 := foldT (θ := θ) (encE := fun ks : List (List Bool) => listT (ks.map ofBits))
    (enc := fun s : List (List Bool) × Tree => .cons (num ub) (.cons (listT (s.1.map ofBits)) s.2)) (s₀ := (strs, t))
    (f := fun ks (s : List (List Bool) × Tree) => (putL ub ks (s.1.headD []) s.2).map fun t =>
      ((1 : A), (s.1.tail, t))) (Inv := fun _ _ => True)
    (d := fun ks => (ks.map fun k => ub * 330 + k.length * 60 + 330).sum + 160)
    (s := .cons (.hd .id) (.tl (.tl .id))) (l := .hd (.tl .id))
    (x := .cons (num ub) (.cons (listT (kss.map fun ks => listT (ks.map ofBits))) (.cons (listT (strs.map ofBits)) t)))
    (Gives.cons (Gives.id _).hd (Gives.id _).tl.tl) (Gives.id _).tl.hd
    (fun ks _ s _ _ => ⟨by
      have e1 : Gives θ (.cons (.hd (.tl .id)) (.cons (.hd .id) (.cons (.hd (.hd (.tl (.tl .id)))) (.tl (.tl (.tl .id))))))
          (.cons (listT (ks.map ofBits)) (.cons (num ub) (.cons (listT (s.1.map ofBits)) s.2)))
          (.cons (num ub) (.cons (listT (ks.map ofBits)) (.cons (ofBits (s.1.headD [])) s.2))) 30 := by
        refine (Gives.cons (Gives.id _).tl.hd (Gives.cons (Gives.id _).hd (Gives.cons (o := ofBits (s.1.headD []))
          (c := 6) ?_ (Gives.id _).tl.tl.tl))).mono (by omega)
        rw [← listB_hd]
        exact ((Gives.id _).tl.tl.hd.hd).mono (by omega)
      have e2 : Gives θ (.tl (.hd (.tl (.tl .id))))
          (.cons (listT (ks.map ofBits)) (.cons (num ub) (.cons (listT (s.1.map ofBits)) s.2)))
          (listT (s.1.tail.map ofBits)) 6 := by
        rw [← listB_tl]
        exact ((Gives.id _).tl.tl.hd.tl).mono (by omega)
      have e3 := Does.of_gives e1 (putF_does (θ := θ) ub ks (s.1.headD []) s.2)
      have e4 := Does.cons (Gives.id (θ := θ) (.cons (listT (ks.map ofBits))
        (.cons (num ub) (.cons (listT (s.1.map ofBits)) s.2)))).tl.hd (Does.cons e2 e3)
      refine (e4.replace ?_).mono (by omega)
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, one_mul]
      rfl, fun _ _ => trivial⟩) trivial
  have h2 := Does.lettT (G := .tl (.tl .id)) (f := fun s : List (List Bool) × Tree => [((1 : A), s.2)]) (d := 3) h1
    (fun b _ => by exact (Gives.id _).tl.tl)
  rw [bind_puts] at h2
  refine h2.mono ?_
  have : ∀ l : List (List (List Bool)), (l.map fun ks => (ks.map fun k => ub * 330 + k.length * 60 +
      330).sum + 160 + 30).sum ≤
      (l.map fun ks => (ks.map fun k => ub * 330 + k.length * 60 + 330).sum + 200).sum := by
    intro l
    exact List.sum_le_sum fun ks _ => by omega
  have := this kss
  omega

end Nc.Grp
