/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Util

/-!
# Values of formulas with named constants

`KV θ κ S F x w c`: all runs of the formula `F` at `x` stop; for the accepting ones the cost and the
size of the value are at most `c` together, and their values name constants in `S`; with the
constants `κ` the sum of their weights is `w`. At the end, a round of the approximate route
(`stepA`) and the program `LP` that applies a program to all pieces.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]


/-- The value of a formula. -/
def KV (θ : List Bool → A) (κ : List Bool → R) (S : Set (List Bool)) (F : Fm) (x : Tree) (w : R) (c : ℕ) : Prop :=
  ∃ l, Ev θ F x l ∧ (∀ r ∈ l, r.cost + r.out.size ≤ c ∧ ∀ p ∈ names r.out, p ∈ S) ∧ val κ l = w

/-- The weight of a run after another one whose value it keeps: the first weight times the second.
-/
theorem wt_seq (κ : List Bool → R) (r s : Run A) : wt κ ((r.seq s).tick s.out)
    = algebraMap A R r.th * wt κ s := by
  simp [wt, Run.seq, Run.tick, mul_assoc]

namespace KV

variable {κ : List Bool → R} {S : Set (List Bool)} {F G H : Fm} {x : Tree} {w w' : R} {c d : ℕ}

theorem mono (h : KV θ κ S F x w c) (hc : c ≤ d) : KV θ κ S F x w d := by
  obtain ⟨l, h1, h2, h3⟩ := h
  exact ⟨l, h1, fun r hr => ⟨(h2 r hr).1.trans hc, (h2 r hr).2⟩, h3⟩

theorem congr (h : KV θ κ S F x w c) (hw : w = w') : KV θ κ S F x w' c := hw ▸ h

theorem hl (h : KV θ κ S F x w c) : Hl θ F x := by
  obtain ⟨l, h1, -⟩ := h
  exact h1.hl

theorem evl (h : KV θ κ S F x w c) : (∀ r ∈ NS1.evl θ F x,
    r.cost + r.out.size ≤ c ∧ ∀ p ∈ names r.out, p ∈ S) ∧
    val κ (NS1.evl θ F x) = w := by
  obtain ⟨l, h1, h2, h3⟩ := h
  rw [h1.evl]
  exact ⟨h2, h3⟩

theorem fail (x : Tree) : KV θ κ S .fail x 0 0 := ⟨[], .fail x, by simp, by simp [val]⟩

/-- Weights of `A` that add up to 1 still add up to 1 in `R`. -/
theorem sum_th {l : List (Run A)} (h : (l.map Run.th).sum = 1) : (l.map fun r => algebraMap A R r.th).sum = 1 := by
  have := congrArg (algebraMap A R) h
  rwa [map_list_sum, List.map_map, map_one] at this

/-- A deterministic value: its weight is the product of the constants it names. -/
theorem gives {o : Tree} (h : Gives θ F x o c) (ho : ∀ p ∈ names o, p ∈ S) :
    KV θ κ S F x ((names o).map κ).prod (c + o.size) := by
  obtain ⟨l, e1, e2, e3⟩ := h.runs
  refine ⟨l, e1, fun r hr => ?_, ?_⟩
  · obtain ⟨a2, a3⟩ := e2 r hr
    rw [a3]
    exact ⟨by omega, ho⟩
  · rw [val, ← one_mul ((names o).map κ).prod, ← sum_th e3, ← List.sum_map_mul_right]
    exact congrArg List.sum (List.map_congr_left fun r hr => by simp [wt, (e2 r hr).2])

/-- A leaf of names: the value is the constant with the name that `F` gives. -/
theorem leaf {o : Tree} (h : Gives θ F x o c) (ho : o.path ∈ S) : KV θ κ S (leaf F) x (κ o.path)
    (c + o.size + 6) := by
  obtain ⟨l, e1, e2, e3⟩ := h.runs
  refine ⟨_, Ev.cons e1 (.quote _ x), ?_, ?_⟩
  · simp only [List.mem_flatMap, List.mem_map, List.mem_singleton]
    rintro u ⟨r, hr, _, rfl, rfl⟩
    obtain ⟨a2, a3⟩ := e2 r hr
    simp only [Run.seq, Run.tick, Run.det, Tree.size, a3, names, List.mem_singleton]
    exact ⟨by omega, fun p hp => hp ▸ ho⟩
  · rw [val, sum_flatMap_map, ← one_mul (κ o.path), ← sum_th e3, ← List.sum_map_mul_right]
    exact congrArg List.sum (List.map_congr_left fun r hr => by
      simp [wt, Run.seq, Run.tick, Run.det, (e2 r hr).2, names])

/-- A node of names: the value is the product of the two values. -/
theorem node (hF : KV θ κ S F x w c) (hG : KV θ κ S G x w' d) : KV θ κ S (node F G) x
    (w * w') (c + d + 6) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  refine ⟨_, Ev.cons (Ev.cons e1 f1) (.quote _ x), ?_, ?_⟩
  · simp only [List.mem_flatMap, List.mem_map, List.mem_singleton]
    rintro u ⟨_, ⟨r, hr, s, hs, rfl⟩, _, rfl, rfl⟩
    obtain ⟨a1, a2⟩ := e2 r hr
    obtain ⟨b1, b2⟩ := f2 s hs
    simp only [Run.seq, Run.tick, Run.det, Tree.size, names, List.mem_append]
    exact ⟨by omega, fun p hp => hp.elim (a2 p) (b2 p)⟩
  · rw [← e3, ← f3, val, val, val, sum_flatMap_map, sum_flatMap_map, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
    rw [List.map_map, ← List.sum_map_mul_left]
    exact congrArg List.sum (List.map_congr_left fun s _ => by
      simp [wt, Run.seq, Run.tick, Run.det, names, mul_assoc, mul_left_comm])

/-- An `ite` whose test gives `o` costs the test plus the branch `K`, where `K` is the then-branch
when `o ≠ nil` and the else-branch when `o = nil`. -/
theorem ite_of {o : Tree} {K : Fm} (hF : Gives θ F x o c) (hK : KV θ κ S K x w d) (hG : o ≠ .nil → K = G)
    (hH : o = .nil → K = H) : KV θ κ S (.ite F G H) x w (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF.runs
  obtain ⟨l', f1, f2, f3⟩ := hK
  refine ⟨_, Ev.ite (L := fun _ => l') e1 (fun r hr h => hG ((e2 r hr).2 ▸ h) ▸ f1)
    (fun r hr h => hH ((e2 r hr).2.symm.trans h) ▸ f1), ?_, ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a2, -⟩ := e2 r hr
    obtain ⟨b1, b2⟩ := f2 s hs
    simp only [Run.seq, Run.tick]
    exact ⟨by omega, b2⟩
  · rw [val, sum_flatMap_map, ← one_mul w, ← sum_th e3, ← List.sum_map_mul_right]
    exact congrArg List.sum (List.map_congr_left fun r _ => by
      rw [← f3, val, List.map_map, ← List.sum_map_mul_left]
      exact congrArg List.sum (List.map_congr_left fun s _ => wt_seq κ r s))

theorem ite_true {o : Tree} (hF : Gives θ F x o c) (ho : o ≠ .nil) (hG : KV θ κ S G x w d) :
    KV θ κ S (.ite F G H) x w (c + d + 1) := ite_of hF hG (fun _ => rfl) (absurd · ho)

theorem ite_false (hF : Gives θ F x .nil c) (hH : KV θ κ S H x w d) : KV θ κ S (.ite F G H) x w (c + d + 1) :=
  ite_of hF hH (absurd rfl) fun _ => rfl

theorem either (hG : KV θ κ S G x w c) (hH : KV θ κ S H x w' d) :
    KV θ κ S (.ite .guess G H) x (w + w') (max c d + 2) := by
  obtain ⟨l, e1, e2, e3⟩ := hG
  obtain ⟨l', f1, f2, f3⟩ := hH
  refine ⟨_, Ev.ite (L := fun r => if r.out = .nil then l' else l) (Ev.guess x) (fun r _ h => by rw [if_neg h]; exact e1)
    (fun r _ h => by rw [if_pos h]; exact f1), ?_, ?_⟩
  · intro u hu
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, List.mem_map, Run.det, Tree.one,
      if_true, reduceCtorEq, if_false] at hu
    rcases hu with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · simp only [Run.seq, Run.tick]
      exact ⟨by have := (f2 s hs).1; omega, (f2 s hs).2⟩
    · simp only [Run.seq, Run.tick]
      exact ⟨by have := (e2 s hs).1; omega, (e2 s hs).2⟩
  · rw [← e3, ← f3, val, val, val, add_comm]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.sum_append, List.map_map,
      Run.det, Tree.one, if_true, reduceCtorEq, if_false]
    congr 2 <;> exact List.map_congr_left fun t _ => by simp [wt, Run.seq, Run.tick]

/-- A plain computation, then a value. -/
theorem app {p : Tree} {Q : List (A × Tree)} {ω : Tree → R} (hF : Does θ F x Q c)
    (hG : ∀ q ∈ Q, KV θ κ S (Fm.ofTree p) q.2 (ω q.2) d) :
    KV θ κ S (NS1.app p F) x (Q.map fun q => algebraMap A R q.1 * ω q.2).sum (c + d + 2) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  have hG' : ∀ s ∈ l, KV θ κ S (Fm.ofTree p) s.out (ω s.out) d := by
    intro s hs
    obtain ⟨-, q, hq, h⟩ := e2 s hs
    rw [← h]
    exact hG q hq
  refine ⟨_, Ev.app e1 fun s hs => (hG' s hs).hl, ?_, ?_⟩
  · intro u hu
    obtain ⟨s, hs, t, ht, h1, h3, -⟩ := mem_app hu
    obtain ⟨a2, -⟩ := e2 s hs
    obtain ⟨b1, b2⟩ := (hG' s hs).evl.1 t ht
    rw [h3]
    exact ⟨by omega, b2⟩
  · rw [val, sum_flatMap_map]
    have h1 : ∀ s ∈ l, (((NS1.evl θ (Fm.ofTree p) s.out).map fun t => ((Run.det 1 p).seq s).seq t |>.tick t.out).map
        (wt κ)).sum = algebraMap A R s.th * ω s.out := by
      intro s hs
      rw [← (hG' s hs).evl.2, val, List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp [wt, Run.seq, Run.tick, Run.det, mul_assoc]
    rw [List.map_congr_left h1]
    -- functions with values in `R`: compare the sums of the weights value by value
    have h2 : (l.map fun s => Finsupp.single s.out s.th).sum = (Q.map fun q => Finsupp.single q.2 q.1).sum := by
      classical
      refine Finsupp.ext fun o => ?_
      have := e3 fun t => if t = o then 1 else 0
      show Finsupp.applyAddHom o _ = Finsupp.applyAddHom o _
      rw [map_list_sum, map_list_sum]
      simpa [wsum, Function.comp_def, Finsupp.single_apply] using this
    have h3 := congrArg (Finsupp.liftAddHom fun o =>
      (AddMonoidHom.mulRight (ω o)).comp (algebraMap A R).toAddMonoidHom) h2
    simpa [map_list_sum, Function.comp_def] using h3

theorem lett {Q : List (A × Tree)} {ω : Tree → R} (hF : Does θ F x Q c)
    (hG : ∀ q ∈ Q, KV θ κ S G q.2 (ω q.2) d) :
    KV θ κ S (NS1.lett F G) x (Q.map fun q => algebraMap A R q.1 * ω q.2).sum (c + d + 2) :=
  app (p := G.code) hF (by rw [Fm.ofTree_code]; exact hG)

theorem app_gives {p o : Tree} (hF : Gives θ F x o c) (hG : KV θ κ S (Fm.ofTree p) o w d) :
    KV θ κ S (NS1.app p F) x w (c + d + 2) :=
  (app (Q := [(1, o)]) (ω := fun _ => w) hF (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hG)).congr (by simp)

/-- Apply a program that is the value of a formula. -/
theorem run {p y : Tree} {e : ℕ} (hF : Gives θ F x p c) (hG : Gives θ G x y d)
    (h : KV θ κ S (Fm.ofTree p) y w e) : KV θ κ S (.run F G) x w (c + d + e + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF.runs
  obtain ⟨l', f1, f2, f3⟩ := hG.runs
  refine ⟨_, Ev.run' e1 f1 fun r hr s hs => by rw [(e2 r hr).2, (f2 s hs).2]; exact h.hl, ?_, ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, t, ht, rfl⟩ := hu
    obtain ⟨a2, a3⟩ := e2 r hr
    obtain ⟨b2, b3⟩ := f2 s hs
    rw [a3, b3] at ht
    obtain ⟨c1, c2⟩ := h.evl.1 t ht
    simp only [Run.seq, Run.tick]
    exact ⟨by omega, c2⟩
  · rw [val, sum_flatMap_map, ← one_mul w, ← sum_th e3, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun r hr => ?_)
    rw [sum_flatMap_map, ← one_mul w, ← sum_th f3, ← List.sum_map_mul_right,
        ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun s hs => ?_)
    rw [(e2 r hr).2, (f2 s hs).2, List.map_map, ← h.evl.2, val, ← List.sum_map_mul_left,
      ← List.sum_map_mul_left]
    exact congrArg List.sum (List.map_congr_left
        fun t _ => by simp [wt, Run.seq, Run.tick, mul_assoc])

/-- A computation, then a value at each of its runs. -/
theorem app_ev {p : Tree} {l : List (Run A)} {ω : Run A → R} (he : Ev θ F x l)
    (hc : ∀ s ∈ l, s.cost ≤ c)
    (hG : ∀ s ∈ l, KV θ κ S (Fm.ofTree p) s.out (ω s) d) :
    KV θ κ S (NS1.app p F) x (l.map fun s => algebraMap A R s.th * ω s).sum (c + d + 2) := by
  refine ⟨_, Ev.app he fun s hs => (hG s hs).hl, ?_, ?_⟩
  · intro u hu
    obtain ⟨s, hs, t, ht, h1, h3, -⟩ := mem_app hu
    obtain ⟨b1, b2⟩ := (hG s hs).evl.1 t ht
    have := hc s hs
    rw [h3]
    exact ⟨by omega, b2⟩
  · rw [val, sum_flatMap_map]
    refine congrArg List.sum (List.map_congr_left fun s hs => ?_)
    rw [← (hG s hs).evl.2, val, List.map_map, ← List.sum_map_mul_left]
    exact congrArg List.sum (List.map_congr_left
        fun t _ => by simp [wt, Run.seq, Run.tick, Run.det, mul_assoc])

end KV

/-- The value of `LP D` is the product of the values of `D` on the trees of the list. -/
theorem LP_kv {D : Tree} {T : ℕ} {κ : List Bool → R} {S : Set (List Bool)}
    {ω : Tree → R} (ys : Tree)
    (h : ∀ y ∈ ys.toList, KV θ κ S (Fm.ofTree D) y (ω y) T) :
    KV θ κ S (LP D) (.cons (LP D).code ys) (ys.toList.map ω).prod ((T + 30)
        * ys.toList.length + 10) := by
  induction ys with
  | nil => exact ((KV.ite_false (Gives.id _).tl (KV.gives (Gives.quote .nil _)
      (by simp [names]))).mono
      (by simp [Tree.size])).congr (by simp [names, toList])
  | cons a ys _ ih =>
    have e := KV.ite_true (H := .quote .nil) (Gives.id (θ := θ)
        (.cons (LP D).code (.cons a ys))).tl (by simp)
      (KV.node (KV.run (Gives.quote D _) (Gives.id _).tl.hd (h a List.mem_cons_self))
        (KV.run (Gives.id _).hd (Gives.cons (Gives.id _).hd (Gives.id _).tl.tl)
          (by
            simp only [hd_cons, tl_cons, Fm.ofTree_code]
            exact ih fun y hy => h y (List.mem_cons_of_mem _ hy))))
    refine (e.mono ?_).congr (by simp [toList])
    simp only [toList, List.length_cons]
    nlinarith

/-- Form the plain instance; the argument is (`z`, (budgets, names)) and `fp` gives the program. -/
def ZE (fp : Fm) : Fm := .cons (.quote WN.code) (.cons fp (.cons (.hd .id) (.hd (.tl .id))))

/-- Guess with `g`, apply `B` to (argument, guess), and join the names of the guess with those of
the value. -/
def guessF (g B : Fm) : Fm := lett (.cons .id g) (node (.tl (.tl .id)) B)

/-- If `g` guesses the data `o q` with names whose constants multiply to `v q`, and `B` has the
value `ω (o q)` at (argument, guess), then the value of `guessF g B` is the sum over the guesses of
`v q * ω (o q)`. -/
theorem guess_kv {β : Type*} {g B : Fm} {z : Tree} {cg d : ℕ} {κ : List Bool → R}
    {S : Set (List Bool)}
    {lg : List (Run A)} {Q : List β} {o : β → Tree} {v : β → R} {ω : Tree → R} (hg : Ev θ g z lg)
    (rg : List.Forall₂ (fun r q => RelT κ (· ∈ S) cg r (o q) (v q)) lg Q)
    (hB : ∀ q ∈ Q, ∀ u : Tree, u.hd = o q → KV θ κ S B (.cons z u) (ω (o q)) d) :
    KV θ κ S (guessF g B) z (Q.map fun q => v q * ω (o q)).sum (2 * cg + d + 13) := by
  have e1 := Ev.cons (Ev.id (θ := θ) z) hg
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at e1
  have e2 := KV.app_ev (κ := κ) (S := S) (c := cg + 2) (d := cg + d + 9)
    (p := (node (.tl (.tl .id)) B).code)
    (ω := fun u => ((names u.out.tl.tl).map κ).prod * ω u.out.tl.hd) e1 ?_ ?_
  · refine (e2.mono (by omega)).congr ?_
    simp only [List.map_map, Function.comp_def, Run.seq, Run.tick, Run.det, one_mul, tl_cons]
    clear e1 e2 hB hg
    induction rg with
    | nil => rfl
    | cons h _ ih =>
      obtain ⟨h1, h2, h3, -⟩ := h
      simp only [List.map_cons, List.sum_cons, h1, h2, h3, map_one, one_mul, ih]
  · intro s hs
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
    obtain ⟨q, -, -, -, -, -, h5⟩ := forall₂_exists rg hs'
    simp only [Run.seq, Run.tick, Run.det]
    omega
  · intro s hs
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
    obtain ⟨q, hq, h1, h2, h3, h4, h5⟩ := forall₂_exists rg hu
    have e := KV.node (KV.gives (κ := κ) (Gives.id _).tl.tl (by simpa using h4)) (hB q hq u.out h2)
    rw [Fm.ofTree_code]
    refine (e.mono ?_).congr ?_
    · have := size_tl_le u.out
      simp only [tl_cons]
      omega
    · simp [Run.seq, Run.tick, Run.det, h2]

/-- A round: guess budgets and names with `g`, form the plain instance of `p`, cut it with `G`,
apply `F` to (`c`, pieces), and join the names that `g` guessed with those of the value. -/
def stepA (F : Fm) (c G p : Tree) (g : Fm) : Fm := guessF g
    (app F.code (.cons (.quote c) (app G (ZE (.quote p)))))

/-- **A round.** If `g` guesses the budgets `q.1` with names whose constants multiply to `q.2`, `G`
cuts the instance of the budgets `q.1` into the pieces `L`, and `F` has the value `ω` at every
piece, then the value of the round is the sum over the guesses of `q.2` times the weighted sum of
`ω` over the pieces. -/
theorem stepA_kv {F g : Fm} {c G p z : Tree} {cg tG tF : ℕ} {κ : List Bool → R}
    {S : Set (List Bool)}
    {lg : List (Run A)} {Q : List (Bt × R)} {L : Tree → List (A × Tree)} {ω : Tree → R}
    (hg : Ev θ g z lg) (rg : List.Forall₂ (RelG κ (· ∈ S) cg) lg Q)
    (hG : ∀ q ∈ Q, Does θ (Fm.ofTree G) (zq p z q.1) (L (zq p z q.1)) tG)
    (hF : ∀ q ∈ Q, ∀ u ∈ L (zq p z q.1), KV θ κ S F (.cons c u.2) (ω u.2) tF) :
    KV θ κ S (stepA F c G p g) z (Q.map fun q =>
      q.2 * ((L (zq p z q.1)).map fun u => algebraMap A R u.1 * ω u.2).sum).sum
          (2 * cg + tG + tF + 30) := by
  have hB : ∀ q ∈ Q, ∀ u : Tree, u.hd = q.1.enc → KV θ κ S (app F.code (.cons (.quote c)
      (app G (ZE (.quote p)))))
      (.cons z u) (((L (.cons WN.code (.cons p (.cons z q.1.enc)))).map
          fun u => algebraMap A R u.1 * ω u.2).sum)
      (tG + tF + 16) := by
    intro q hq u hu
    have hZ : Gives θ (ZE (.quote p)) (.cons z u) (zq p z q.1) 10 := by
      simpa [zq, ZE, hu] using (Gives.quote (θ := θ) WN.code (.cons z u)).cons
        ((Gives.quote p _).cons ((Gives.id _).hd.cons (Gives.id _).tl.hd))
    have hP := Does.app (p := G) (R := fun _ => L (zq p z q.1)) hZ fun v hv => by
      rw [List.mem_singleton] at hv
      subst hv
      exact hG q hq
    simp only [bindW, List.flatMap_cons, List.flatMap_nil, List.append_nil, one_mul,
        Prod.mk.eta, List.map_id'] at hP
    refine ((KV.app (p := F.code) (d := tF) (ω := fun o => ω o.tl)
        (Does.cons (Gives.quote (θ := θ) c (.cons z u)) hP)
      fun v hv => ?_).mono (by omega)).congr ?_
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map] at hv
      obtain ⟨v, hv, rfl⟩ := hv
      rw [Fm.ofTree_code]
      exact hF q hq v hv
    · simp [zq, Function.comp_def]
  refine (guess_kv (ω := fun e => ((L (.cons WN.code (.cons p (.cons z e)))).map
    fun u => algebraMap A R u.1 * ω u.2).sum) hg rg hB).mono ?_
  omega

end NS1
