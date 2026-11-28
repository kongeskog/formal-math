/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Accel

/-!
# Weighted functions computed by formulas

`Does θ F x Q c`: all runs of the formula `F` at the tree `x` stop, the accepting ones
have cost at most `c`, and for every function of the value their weighted sum is that of the list `Q` of pairs
(weight, value).
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {α β : Type}

/-- Weighted sums over a list of pairs (weight, value). -/
def wsum (Q : List (A × α)) (φ : α → A) : A := (Q.map fun q => q.1 * φ q.2).sum

@[simp] theorem wsum_nil (φ : α → A) : wsum ([] : List (A × α)) φ = 0 := rfl

@[simp] theorem wsum_cons (q : A × α) (Q : List (A × α)) (φ : α → A) :
    wsum (q :: Q) φ = q.1 * φ q.2 + wsum Q φ := by simp [wsum]

theorem wsum_append (Q Q' : List (A × α)) (φ : α → A) : wsum (Q ++ Q') φ = wsum Q φ + wsum Q' φ := by
  simp [wsum]

theorem wsum_congr {Q : List (A × α)} {φ φ' : α → A} (h : ∀ q ∈ Q, φ q.2 = φ' q.2) : wsum Q φ = wsum Q φ' := by
  unfold wsum
  congr 1
  exact List.map_congr_left fun q hq => by rw [h q hq]

/-- First `Q`, then `R` at the value. -/
def bindW (Q : List (A × α)) (R : α → List (A × β)) : List (A × β) :=
  Q.flatMap fun q => (R q.2).map fun p => (q.1 * p.1, p.2)

theorem wsum_bindW (Q : List (A × α)) (R : α → List (A × β)) (φ : β → A) :
    wsum (bindW Q R) φ = wsum Q fun o => wsum (R o) φ := by
  unfold wsum bindW
  rw [sum_flatMap_map]
  congr 1
  refine List.map_congr_left fun q _ => ?_
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, mul_assoc]

theorem mem_bindW {Q : List (A × α)} {R : α → List (A × β)} {p : A × β} (h : p ∈ bindW Q R) :
    ∃ q ∈ Q, ∃ r ∈ R q.2, p.2 = r.2 ∧ p.1 = q.1 * r.1 := by
  unfold bindW at h
  rw [List.mem_flatMap] at h
  obtain ⟨q, hq, h⟩ := h
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
  exact ⟨q, hq, r, hr, rfl, rfl⟩

theorem mem_bindW_of {Q : List (A × α)} {R : α → List (A × β)} {q : A × α} {r : A × β} (hq : q ∈ Q)
    (hr : r ∈ R q.2) : (q.1 * r.1, r.2) ∈ bindW Q R :=
  List.mem_flatMap.2 ⟨q, hq, List.mem_map.2 ⟨r, hr, rfl⟩⟩

/-- The formula computes the weighted list `Q` at `x`. -/
def Does (θ : List Bool → A) (F : Fm) (x : Tree) (Q : List (A × Tree)) (c : ℕ) : Prop :=
  ∃ l, Ev θ F x l ∧ (∀ r ∈ l, r.cost ≤ c ∧ ∃ q ∈ Q, q.2 = r.out) ∧
    ∀ φ : Tree → A, (l.map fun r => r.th * φ r.out).sum = wsum Q φ

/-- The formula has the value `o` at `x`, with weight 1. -/
def Gives (θ : List Bool → A) (F : Fm) (x o : Tree) (c : ℕ) : Prop := Does θ F x [(1, o)] c

/-- The runs of a formula that has the value `o`: they give `o`, and their weights add up to 1. -/
theorem Gives.runs {F : Fm} {x o : Tree} {c : ℕ} (h : Gives θ F x o c) :
    ∃ l, Ev θ F x l ∧ (∀ r ∈ l, r.cost ≤ c ∧ r.out = o) ∧ (l.map Run.th).sum = 1 := by
  obtain ⟨l, e1, e2, e3⟩ := h
  refine ⟨l, e1, fun r hr => ?_, by simpa [wsum] using e3 fun _ => 1⟩
  obtain ⟨a2, q, hq, a3⟩ := e2 r hr
  rw [List.mem_singleton] at hq
  subst hq
  exact ⟨a2, a3.symm⟩

namespace Does

variable {F G H : Fm} {x : Tree} {Q : List (A × Tree)} {c d : ℕ}

theorem mono (h : Does θ F x Q c) (hc : c ≤ d) : Does θ F x Q d := by
  obtain ⟨l, h1, h2, h3⟩ := h
  exact ⟨l, h1, fun r hr => ⟨(h2 r hr).1.trans hc, (h2 r hr).2⟩, h3⟩

/-- Replace the list by an equivalent one. -/
theorem congr {Q' : List (A × Tree)} (h : Does θ F x Q c) (h1 : ∀ q ∈ Q, ∃ q' ∈ Q', q'.2 = q.2)
    (h2 : ∀ φ : Tree → A, wsum Q φ = wsum Q' φ) : Does θ F x Q' c := by
  obtain ⟨l, e1, e2, e3⟩ := h
  refine ⟨l, e1, fun r hr => ⟨(e2 r hr).1, ?_⟩, fun φ => (e3 φ).trans (h2 φ)⟩
  obtain ⟨q, hq, hqr⟩ := (e2 r hr).2
  obtain ⟨q', hq', e⟩ := h1 q hq
  exact ⟨q', hq', e.trans hqr⟩

theorem hl (h : Does θ F x Q c) : Hl θ F x := by
  obtain ⟨l, h1, -⟩ := h
  exact h1.hl

theorem evl (h : Does θ F x Q c) : (∀ r ∈ NS1.evl θ F x, r.cost ≤ c ∧ ∃ q ∈ Q, q.2 = r.out) ∧
    ∀ φ : Tree → A, ((NS1.evl θ F x).map fun r => r.th * φ r.out).sum = wsum Q φ := by
  obtain ⟨l, h1, h2, h3⟩ := h
  rw [h1.evl]
  exact ⟨h2, h3⟩

/-- A computation is a plain sum. -/
theorem plain (h : Does θ F x Q c) : Plain θ c (.cons F.code x) ∧ pv θ (.cons F.code x) = (Q.map Prod.fst).sum := by
  obtain ⟨h1, h2⟩ := h.evl
  refine ⟨⟨?_, fun r hr => ?_⟩, ?_⟩
  · simp only [hd_cons, tl_cons, Fm.ofTree_code]
    exact h.hl
  · simp only [hd_cons, tl_cons, Fm.ofTree_code] at hr
    exact (h1 r hr).1
  · simp only [pv, hd_cons, tl_cons, Fm.ofTree_code, pval]
    have := h2 fun _ => 1
    simpa [wsum] using this

/-- The runs of a formula, with their weights and values. -/
theorem of_ev {l : List (Run A)} (h : Ev θ F x l) (hc : ∀ r ∈ l, r.cost ≤ c) :
    Does θ F x (l.map fun r => (r.th, r.out)) c :=
  ⟨l, h, fun r hr => ⟨hc r hr, _, List.mem_map_of_mem hr, rfl⟩,
      fun φ => by simp [wsum, Function.comp_def]⟩

theorem of_dt {o : Tree} (h : Dt θ F x o c) : Does θ F x [(1, o)] c := by
  refine ⟨_, h, ?_, fun φ => ?_⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨le_rfl, (1, o), List.mem_singleton_self _, rfl⟩
  · simp [Run.det]

/-- Pairs. -/
theorem cons {R : List (A × Tree)} (hF : Does θ F x Q c) (hG : Does θ G x R d) : Does θ (.cons F G) x
    (Q.flatMap fun q => R.map fun r => (q.1 * r.1, .cons q.2 r.2)) (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  refine ⟨_, Ev.cons e1 f1, ?_, fun φ => ?_⟩
  · intro r hr
    simp only [List.mem_flatMap, List.mem_map] at hr
    obtain ⟨r1, h1, r2, h2, rfl⟩ := hr
    obtain ⟨a2, q, hq, a3⟩ := e2 r1 h1
    obtain ⟨b2, p, hp, b3⟩ := f2 r2 h2
    refine ⟨?_, (q.1 * p.1, .cons q.2 p.2), List.mem_flatMap.2 ⟨q, hq,
        List.mem_map.2 ⟨p, hp, rfl⟩⟩, ?_⟩
    · simp only [Run.seq, Run.tick]
      omega
    · simp [Run.tick, a3, b3]
  · rw [sum_flatMap_map]
    have h1 : ∀ r : Run A, ((l'.map fun s => (r.seq s).tick (.cons r.out s.out)).map fun u => u.th * φ u.out).sum =
        r.th * wsum R fun o => φ (.cons r.out o) := by
      intro r
      rw [← f3, List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun s _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick, mul_assoc]
    simp only [h1]
    rw [e3 fun o => wsum R fun o' => φ (.cons o o'), wsum, wsum, sum_flatMap_map]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    rw [wsum, List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, mul_assoc]

/-- Apply the program that is the value of a formula to the values of another one. -/
theorem runW {p : Tree} {R : Tree → List (A × Tree)} {e : ℕ}
    (hF : Gives θ F x p c) (hG : Does θ G x Q d) (h : ∀ q ∈ Q, Does θ (Fm.ofTree p) q.2 (R q.2) e) :
    Does θ (.run F G) x (bindW Q R) (c + d + e + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  have ho : ∀ r ∈ l, r.out = p := by
    intro r hr
    obtain ⟨-, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  have hG' : ∀ s ∈ l', Does θ (Fm.ofTree p) s.out (R s.out) e := by
    intro s hs
    obtain ⟨-, q, hq, h'⟩ := f2 s hs
    rw [← h']
    exact h q hq
  refine ⟨_, Ev.run' e1 f1 fun r hr s hs => by rw [ho r hr]; exact (hG' s hs).hl, ?_, fun φ => ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, t, ht, rfl⟩ := hu
    rw [ho r hr] at ht
    obtain ⟨a2, -⟩ := e2 r hr
    obtain ⟨b2, q, hq, b3⟩ := f2 s hs
    obtain ⟨c2, q', hq', c3⟩ := (hG' s hs).evl.1 t ht
    rw [← b3] at hq'
    refine ⟨?_, (q.1 * q'.1, q'.2), mem_bindW_of hq hq', c3⟩
    simp only [Run.seq, Run.tick]
    omega
  · rw [sum_flatMap_map, wsum_bindW]
    have h1 : ∀ r ∈ l, ((l'.flatMap fun s => (NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
        ((r.seq s).seq t).tick t.out).map fun u => u.th * φ u.out).sum = r.th * wsum Q fun o =>
            wsum (R o) φ := by
      intro r hr
      rw [sum_flatMap_map, ← f3 fun o => wsum (R o) φ, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun s hs => ?_
      rw [ho r hr, List.map_map, ← (hG' s hs).evl.2 φ, ← List.sum_map_mul_left, ←
          List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick]
      ring
    rw [List.map_congr_left h1]
    have := e3 fun _ => wsum Q fun o => wsum (R o) φ
    rw [this]
    simp [wsum]

/-- Apply a fixed program to the value. -/
theorem app {p : Tree} {R : Tree → List (A × Tree)} (hF : Does θ F x Q c)
    (hG : ∀ q ∈ Q, Does θ (Fm.ofTree p) q.2 (R q.2) d) : Does θ (app p F) x (bindW Q R) (c + d + 2)
        :=
  (runW (of_dt (Dt.quote p x)) hF hG).mono (by omega)

/-- `let`. -/
theorem lett {R : Tree → List (A × Tree)} (hF : Does θ F x Q c) (hG : ∀ q ∈ Q, Does θ G q.2 (R q.2) d) :
    Does θ (lett F G) x (bindW Q R) (c + d + 2) :=
  app (p := G.code) hF (by rw [Fm.ofTree_code]; exact hG)

/-- `let`, with the argument kept. -/
theorem letk {R : Tree → List (A × Tree)} (hF : Does θ F x Q c) (hG : ∀ q ∈ Q, Does θ G (.cons x q.2) (R q.2) d) :
    Does θ (NS1.lett (.cons .id F) G) x (bindW Q R) (c + d + 4) := by
  have h1 := (of_dt (Dt.id x)).cons hF
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, one_mul] at h1
  have h2 := h1.lett (G := G) (R := fun o => R o.tl) (d := d) (by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact hG q' hq')
  refine (h2.congr ?_ fun φ => ?_).mono (by omega)
  · intro p hp
    obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hp
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    exact ⟨_, mem_bindW_of hq' hr, h3.symm⟩
  · rw [wsum_bindW, wsum_bindW]
    simp [wsum, Function.comp_def]

/-- Apply a program that is the value of a formula. -/
theorem run {p y : Tree} {R : List (A × Tree)} {e : ℕ} (hF : Gives θ F x p c) (hG : Gives θ G x y d)
    (h : Does θ (Fm.ofTree p) y R e) : Does θ (.run F G) x R (c + d + e + 1) := by
  have := runW (R := fun _ => R) hF hG (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact h)
  simpa [bindW] using this

/-- An `ite` whose test gives `o` costs the test plus the branch `K`: the then-branch when `o ≠ nil`, the
else-branch when `o = nil`. -/
theorem ite_of {o : Tree} {K : Fm} (hF : Gives θ F x o c) (hK : Does θ K x Q d) (hG : o ≠ .nil → K = G)
    (hH : o = .nil → K = H) : Does θ (.ite F G H) x Q (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF.runs
  obtain ⟨l', f1, f2, f3⟩ := hK
  refine ⟨_, Ev.ite (L := fun _ => l') e1 (fun r hr h => hG ((e2 r hr).2 ▸ h) ▸ f1)
    (fun r hr h => hH ((e2 r hr).2.symm.trans h) ▸ f1), ?_, fun φ => ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a2, -⟩ := e2 r hr
    obtain ⟨b2, b3⟩ := f2 s hs
    refine ⟨?_, b3⟩
    simp only [Run.seq, Run.tick]
    omega
  · rw [sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.map fun s => (r.seq s).tick s.out).map fun u => u.th * φ u.out).sum = r.th * wsum Q φ := by
      intro r _
      rw [List.map_map, ← f3 φ, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick, mul_assoc]
    rw [List.map_congr_left h1, List.sum_map_mul_right, e3, one_mul]

theorem ite_true {o : Tree} (hF : Gives θ F x o c) (ho : o ≠ .nil) (hG : Does θ G x Q d) :
    Does θ (.ite F G H) x Q (c + d + 1) := ite_of hF hG (fun _ => rfl) (absurd · ho)

theorem ite_false (hF : Gives θ F x .nil c) (hH : Does θ H x Q d) : Does θ (.ite F G H) x Q (c + d + 1) :=
  ite_of hF hH (absurd rfl) fun _ => rfl

/-- Guess between two formulas. -/
theorem either {R : List (A × Tree)} (hG : Does θ G x Q c) (hH : Does θ H x R d) :
    Does θ (.ite .guess G H) x (Q ++ R) (max c d + 2) := by
  obtain ⟨l, e1, e2, e3⟩ := hG
  obtain ⟨l', f1, f2, f3⟩ := hH
  refine ⟨_, Ev.ite (L := fun r => if r.out = .nil then l' else l) (Ev.guess x) (fun r _ h => by rw [if_neg h]; exact e1)
    (fun r _ h => by rw [if_pos h]; exact f1), ?_, fun φ => ?_⟩
  · intro u hu
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, List.mem_map, Run.det, Tree.one,
      if_true, reduceCtorEq, if_false] at hu
    rcases hu with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · obtain ⟨a2, q, hq, a3⟩ := f2 s hs
      refine ⟨?_, q, List.mem_append_right _ hq, a3⟩
      simp only [Run.seq, Run.tick]
      omega
    · obtain ⟨a2, q, hq, a3⟩ := e2 s hs
      refine ⟨?_, q, List.mem_append_left _ hq, a3⟩
      simp only [Run.seq, Run.tick]
      omega
  · rw [wsum_append, ← e3 φ, ← f3 φ]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.sum_append, List.map_map,
      Run.det, Tree.one, if_true, reduceCtorEq, if_false]
    rw [add_comm]
    congr 2 <;> exact List.map_congr_left fun t _ => by
      simp only [Function.comp_apply, Run.seq, Run.tick, one_mul]

theorem fail (x : Tree) : Does θ .fail x [] 0 := ⟨[], .fail x, by simp, by simp⟩

-- `theta`, `hd` and `tl` below are instances of this lemma.
/-- A step that changes every run of a formula with one value in the same way. -/
theorem step {F' : Fm} {o o' : Tree} {a : A} {g : Run A → Run A} (h : Gives θ F x o c)
    (hE : ∀ l, Ev θ F x l → Ev θ F' x (l.map g))
    (hg : ∀ r, r.out = o → (g r).cost = r.cost + 1 ∧ (g r).th = r.th * a ∧ (g r).out = o') :
    Does θ F' x [(a, o')] (c + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := h.runs
  refine ⟨_, hE l e1, ?_, fun φ => ?_⟩
  · intro u hu
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hu
    obtain ⟨a2, a3⟩ := e2 r hr
    obtain ⟨g2, -, g4⟩ := hg r a3
    exact ⟨by omega, _, List.mem_singleton_self _, g4.symm⟩
  · rw [List.map_map, List.map_congr_left fun r hr => show _ = r.th * (a * φ o') by
      obtain ⟨-, g3, g4⟩ := hg r (e2 r hr).2
      rw [Function.comp_apply, g3, g4, mul_assoc]]
    simp [List.sum_map_mul_right, e3, wsum]

/-- Multiply by a constant of `A`. -/
theorem theta {o : Tree} (h : Gives θ F x o c) : Does θ (.theta F) x [(θ o.path, .nil)] (c + 1) :=
  step h (fun _ => Ev.theta) fun r hr => by simp [hr]

theorem hd {o : Tree} (h : Gives θ F x o c) : Gives θ (.hd F) x o.hd (c + 1) :=
  step h (fun _ => Ev.hd) fun r hr => by simp [Run.tick, hr]

theorem tl {o : Tree} (h : Gives θ F x o c) : Gives θ (.tl F) x o.tl (c + 1) :=
  step h (fun _ => Ev.tl) fun r hr => by simp [Run.tick, hr]

end Does

namespace Gives

variable {F G H : Fm} {x o o' : Tree} {c d : ℕ}

theorem mono (h : Gives θ F x o c) (hc : c ≤ d) : Gives θ F x o d := Does.mono h hc

theorem id (x : Tree) : Gives θ .id x x 1 := Does.of_dt (Dt.id x)

theorem quote (a x : Tree) : Gives θ (.quote a) x a 1 := Does.of_dt (Dt.quote a x)

theorem hd (h : Gives θ F x o c) : Gives θ (.hd F) x o.hd (c + 1) := Does.hd h

theorem tl (h : Gives θ F x o c) : Gives θ (.tl F) x o.tl (c + 1) := Does.tl h

theorem cons (h : Gives θ F x o c) (h' : Gives θ G x o' d) : Gives θ (.cons F G) x (.cons o o') (c + d + 1) := by
  have := Does.cons h h'
  simpa [Gives] using this

theorem app {p : Tree} (h : Gives θ F x o c) (h' : Gives θ (Fm.ofTree p) o o' d) :
    Gives θ (NS1.app p F) x o' (c + d + 2) := by
  have := Does.app (p := p) (R := fun _ => [(1, o')]) h (d := d) (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact h')
  simpa [Gives, bindW] using this

theorem lett (h : Gives θ F x o c) (h' : Gives θ G o o' d) : Gives θ (NS1.lett F G) x o' (c + d + 2) :=
  app (p := G.code) h (by rw [Fm.ofTree_code]; exact h')

theorem letk (h : Gives θ F x o c) (h' : Gives θ G (.cons x o) o' d) :
    Gives θ (NS1.lett (.cons .id F) G) x o' (c + d + 4) :=
  (((id x).cons h).lett h').mono (by omega)

theorem run {p y : Tree} {e : ℕ} (hF : Gives θ F x p c) (hG : Gives θ G x y d) (h : Gives θ (Fm.ofTree p) y o e) :
    Gives θ (.run F G) x o (c + d + e + 1) := Does.run hF hG h

theorem ite_true (hF : Gives θ F x o c) (ho : o ≠ .nil) (hG : Gives θ G x o' d) :
    Gives θ (.ite F G H) x o' (c + d + 1) := Does.ite_true hF ho hG

theorem ite_false (hF : Gives θ F x .nil c) (hH : Gives θ H x o' d) : Gives θ (.ite F G H) x o' (c + d + 1) :=
  Does.ite_false hF hH

/-- A computation, then a deterministic one. -/
theorem after {Q : List (A × Tree)} (h : Does θ F x Q c) {f : Tree → Tree} (h' : ∀ q ∈ Q, Gives θ G q.2 (f q.2) d) :
    Does θ (NS1.lett F G) x (Q.map fun q => (q.1, f q.2)) (c + d + 2) := by
  have := h.lett (R := fun o => [(1, f o)]) h'
  simpa [bindW, flatMap_single] using this

end Gives

/-- The weighted list of a deterministic computation followed by another one. -/
theorem Does.of_gives {F G : Fm} {x o : Tree} {Q : List (A × Tree)} {c d : ℕ} (h : Gives θ F x o c)
    (h' : Does θ G o Q d) : Does θ (NS1.lett F G) x Q (c + d + 2) := by
  have := Does.lett (R := fun _ => Q) h (G := G) (d := d) (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact h')
  simpa [bindW] using this

/-- A program calls itself: its argument is (this program, data). -/
theorem Does.self {B G : Fm} {z y : Tree} {Q : List (A × Tree)} {c d : ℕ}
    (hG : Gives θ G (.cons B.code z) (.cons B.code y) c) (h : Does θ B (.cons B.code y) Q d) :
    Does θ (.run (.hd .id) G) (.cons B.code z) Q (c + d + 3) :=
  (Does.run (Gives.id _).hd hG (by rw [hd_cons, Fm.ofTree_code]; exact h)).mono (by omega)

end NS1
