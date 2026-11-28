/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Comp

/-!
# Lists, equality, tries
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- A list of trees as a tree. -/
def listT : List Tree → Tree
  | [] => .nil
  | x :: xs => .cons x (listT xs)

@[simp] theorem toList_listT (xs : List Tree) : (listT xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [listT, toList, ih]

theorem listT_toList (x : Tree) : listT x.toList = x := by
  induction x with
  | nil => rfl
  | cons a b _ ih => simp [listT, toList, ih]

theorem listT_ofBits (w : List Bool) : listT (w.map bit) = ofBits w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [listT, ofBits, ih]

section Fold

/-- Fold over a list with a state. The argument is (this program, (state, list)); `step` is
applied to (element, state). -/
def foldB (step : Fm) : Fm := .ite (.tl (.tl .id))
  (.run (.hd .id) (.cons (.hd .id) (.cons (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
    (.tl (.tl (.tl .id)))))) (.hd (.tl .id))

/-- Fold: `s` gives the state at the beginning, `l` the list. -/
def foldF (step s l : Fm) : Fm :=
  app (foldB step).code (.cons (.quote (foldB step).code) (.cons s l))

end Fold

end NS1

/-!
## Weighted lists of typed values

Programs of the tree machine whose values are encodings of typed values. Lemmas on the weighted
lists `bindW`, `wsum` of `NS1.Comp`. `Does.appT`, `Does.lettT`, `foldT`: composition and folds with
typed values. The folds over trees after this block, `foldF_does` and `foldF_gives`, are the case
where both encodings are `id`.
-/

namespace Nc.Grp

open NS1 NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {α β γ : Type}

@[simp] theorem wsum_single (a : α) (G : α → A) : wsum [((1 : A), a)] G = G a := by simp [wsum]

theorem wsum_map_mul (c : A) (l : List (A × α)) (G : α → A) :
    wsum (l.map fun r => (c * r.1, r.2)) G = c * wsum l G := by
  induction l with
  | nil => simp
  | cons p l ih => simp only [List.map_cons, wsum_cons, ih]; ring

theorem wsum_map (l : List (A × α)) (e : α → β) (G : β → A) :
    wsum (l.map (Prod.map id e)) G = wsum l fun a => G (e a) := by
  unfold wsum
  rw [List.map_map]
  rfl

theorem bindW_single (a : α) (f : α → List (A × β)) : bindW [((1 : A), a)] f = f a := by
  simp [bindW]

theorem bindW_assoc (l : List (A × α)) (f : α → List (A × β)) (g : β → List (A × γ)) :
    bindW (bindW l f) g = bindW l fun a => bindW (f a) g := by
  simp only [bindW, List.flatMap_assoc, List.flatMap_map, List.map_flatMap, List.map_map,
      Function.comp_def, mul_assoc]

theorem bindW_pure (l : List α) (g : α → β) (f : β → List (A × γ)) :
    bindW (l.map fun t => ((1 : A), g t)) f = l.flatMap fun t => f (g t) := by
  simp only [bindW, List.flatMap_map, one_mul, List.map_id']

theorem bindW_map (l : List (A × α)) (f : α → List (A × β)) (e : β → γ) :
    bindW l (fun a => (f a).map (Prod.map id e)) = (bindW l f).map (Prod.map id e) := by
  simp only [bindW, List.map_flatMap, List.map_map]
  rfl

/-- The weighted sums are determined by the program. -/
theorem _root_.NS1.Does.wsum_unique {F : Fm} {x : Tree} {Q Q' : List (A × Tree)} {c d : ℕ}
    (h : Does θ F x Q c) (h' : Does θ F x Q' d) (φ : Tree → A) : wsum Q φ = wsum Q' φ := by
  rw [← h.evl.2 φ, ← h'.evl.2 φ]

/-- Replace the list. -/
theorem _root_.NS1.Does.replace {F : Fm} {x : Tree} {Q Q' : List (A × Tree)} {c : ℕ}
    (h : Does θ F x Q c) (hQ : Q = Q') : Does θ F x Q' c := hQ ▸ h

section

-- Typed values: the weighted list `l` of values encoded by `enc`, each mapped to `f`.
variable {F G : Fm} {x p : Tree} {l : List (A × β)} {enc : β → Tree} {f : β → List (A × Tree)}
  {c d : ℕ}

/-- A rule for lists of trees with a function `R` on trees gives the rule for typed values. -/
theorem exists_untyped (hG : ∀ b ∈ l, Does θ (Fm.ofTree p) (enc b.2) (f b.2) d) :
    ∃ R : Tree → List (A × Tree),
      (∀ q ∈ l.map (Prod.map id enc), Does θ (Fm.ofTree p) q.2 (R q.2) d) ∧
      ∀ {F : Fm} {x : Tree} {c : ℕ},
        Does θ F x (bindW (l.map (Prod.map id enc)) R) c → Does θ F x (bindW l f) c := by
  classical
  let R : Tree → List (A × Tree) := fun t => if h : ∃ b ∈ l, enc b.2 = t then f h.choose.2 else []
  have hR : ∀ b ∈ l, ∃ b' ∈ l, R (enc b.2) = f b'.2 ∧ enc b'.2 = enc b.2 := by
    intro b hb
    have h : ∃ b' ∈ l, enc b'.2 = enc b.2 := ⟨b, hb, rfl⟩
    exact ⟨h.choose, h.choose_spec.1, dif_pos h, h.choose_spec.2⟩
  refine ⟨R, fun q hq => ?_, fun h1 => h1.congr ?_ fun φ => ?_⟩
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hq
    obtain ⟨b', hb', e1, e2⟩ := hR b hb
    show Does θ (Fm.ofTree p) (enc b.2) (R (enc b.2)) d
    rw [e1, ← e2]
    exact hG b' hb'
  · intro z hz
    obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hz
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hq
    obtain ⟨b', hb', e1, e2⟩ := hR b hb
    have hr' : r ∈ f b'.2 := by rw [← e1]; exact hr
    exact ⟨_, mem_bindW_of hb' hr', h3.symm⟩
  · rw [wsum_bindW, wsum_bindW, wsum_map]
    refine wsum_congr fun b hb => ?_
    obtain ⟨b', hb', e1, e2⟩ := hR b hb
    rw [e1]
    have h5 := hG b' hb'
    rw [e2] at h5
    exact Does.wsum_unique h5 (hG b hb) φ

/-- Apply a fixed program to typed values. -/
theorem _root_.NS1.Does.appT (hF : Does θ F x (l.map (Prod.map id enc)) c)
    (hG : ∀ b ∈ l, Does θ (Fm.ofTree p) (enc b.2) (f b.2) d) :
    Does θ (app p F) x (bindW l f) (c + d + 2) := by
  obtain ⟨R, h1, h2⟩ := exists_untyped hG
  exact h2 (Does.app hF h1)

/-- `let` with typed values. -/
theorem _root_.NS1.Does.lettT (hF : Does θ F x (l.map (Prod.map id enc)) c)
    (hG : ∀ b ∈ l, Does θ G (enc b.2) (f b.2) d) :
    Does θ (lett F G) x (bindW l f) (c + d + 2) :=
  Does.appT (p := G.code) hF (by rw [Fm.ofTree_code]; exact hG)

/-- The first of two formulas has the empty value: go on with the second one. -/
theorem _root_.NS1.Does.ite_nil {H : Fm} {a : A} {Q : List (A × Tree)}
    (hF : Does θ F x [(a, .nil)] c) (hH : Does θ H x Q d) :
    Does θ (.ite F G H) x (Q.map fun r => (a * r.1, r.2)) (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hH
  have hout : ∀ r ∈ l, r.out = .nil := by
    intro r hr
    obtain ⟨-, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.ite (L := fun _ => l') e1 (fun r hr h => absurd (hout r hr) h) (fun r _ _ => f1),
      ?_, fun φ => ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a2, -⟩ := e2 r hr
    obtain ⟨b2, q, hq, b3⟩ := f2 s hs
    refine ⟨?_, (a * q.1, q.2), List.mem_map.2 ⟨q, hq, rfl⟩, b3⟩
    simp only [Run.seq, Run.tick]
    omega
  · rw [sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.map fun s => (r.seq s).tick s.out).map fun u => u.th * φ u.out).sum =
        r.th * wsum Q φ := by
      intro r _
      rw [List.map_map, ← f3 φ, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick, mul_assoc]
    rw [List.map_congr_left h1]
    have := e3 fun _ => wsum Q φ
    rw [this]
    simp only [wsum_cons, wsum_nil, add_zero]
    exact (wsum_map_mul a Q φ).symm

/-- Apply a program that is a value to typed values. -/
theorem _root_.NS1.Does.runT {e : ℕ} (hF : Gives θ F x p c)
    (hG : Does θ G x (l.map (Prod.map id enc)) d)
    (h : ∀ b ∈ l, Does θ (Fm.ofTree p) (enc b.2) (f b.2) e) :
    Does θ (.run F G) x (bindW l f) (c + d + e + 1) := by
  obtain ⟨R, h1, h2⟩ := exists_untyped h
  exact h2 (Does.runW hF hG h1)

/-- `let`, with the argument kept, typed values. -/
theorem _root_.NS1.Does.letkT (hF : Does θ F x (l.map (Prod.map id enc)) c)
    (hG : ∀ b ∈ l, Does θ G (.cons x (enc b.2)) (f b.2) d) :
    Does θ (lett (.cons .id F) G) x (bindW l f) (c + d + 4) := by
  have h1 : Does θ (.cons .id F) x (l.map (Prod.map id fun b => .cons x (enc b))) (1 + c + 1) := by
    refine (Does.cons (Gives.id (θ := θ) x) hF).replace ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, one_mul]
    rfl
  exact (Does.lettT h1 hG).mono (by omega)

end

/-- `let` with typed values and typed results. -/
theorem _root_.NS1.Does.lettE {F G : Fm} {x : Tree} {l : List (A × β)} {enc : β → Tree}
    {enc' : γ → Tree} {f : β → List (A × γ)} {c d : ℕ}
    (hF : Does θ F x (l.map (Prod.map id enc)) c)
    (hG : ∀ b ∈ l, Does θ G (enc b.2) ((f b.2).map (Prod.map id enc')) d) :
    Does θ (lett F G) x ((bindW l f).map (Prod.map id enc')) (c + d + 2) := by
  rw [← bindW_map]
  exact Does.lettT hF hG

section Fold

variable {ε : Type}

/-- The weighted list of a fold. -/
def foldL (f : ε → β → List (A × β)) : List ε → β → List (A × β)
  | [], s => [(1, s)]
  | x :: xs, s => bindW (f x s) (foldL f xs)

theorem foldB_doesT {step : Fm} {encE : ε → Tree} {enc : β → Tree} {f : ε → β → List (A × β)}
    {Inv : List ε → β → Prop} {d : ε → ℕ} {xs : List ε} (h : ∀ x ys s, x ∈ xs → Inv (x :: ys) s →
      Does θ step (.cons (encE x) (enc s)) ((f x s).map (Prod.map id enc)) (d x) ∧
        ∀ q ∈ f x s, Inv ys q.2)
    {s : β} (hs : Inv xs s) :
    Does θ (foldB step) (.cons (foldB step).code (.cons (enc s) (listT (xs.map encE))))
      ((foldL f xs s).map (Prod.map id enc)) ((xs.map fun x => d x + 30).sum + 10) := by
  induction xs generalizing s with
  | nil => exact (Does.ite_false (Gives.id _).tl.tl (Gives.id _).tl.hd).mono (by simp)
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := h x xs s List.mem_cons_self hs
    rw [List.map_cons]
    have e1 : Does θ (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
        (.cons (foldB step).code (.cons (enc s) (listT (encE x :: xs.map encE))))
        ((f x s).map (Prod.map id enc)) (8 + d x + 2) :=
      Does.of_gives (Gives.cons (Gives.id _).tl.tl.hd (Gives.id _).tl.hd) h1
    have e2 := Does.cons (Gives.id (θ := θ)
        (.cons (foldB step).code (.cons (enc s) (listT (encE x :: xs.map encE))))).hd
      (Does.cons e1 (Gives.id
        (.cons (foldB step).code (.cons (enc s) (listT (encE x :: xs.map encE))))).tl.tl.tl)
    have e3 : Does θ
        (.cons (.hd .id) (.cons (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
          (.tl (.tl (.tl .id)))))
        (.cons (foldB step).code (.cons (enc s) (listT (encE x :: xs.map encE))))
        ((f x s).map (Prod.map id fun s' =>
          .cons (foldB step).code (.cons (enc s') (listT (xs.map encE)))))
        (8 + d x + 2 + 8) := by
      refine (e2.replace ?_).mono (by omega)
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil,
        one_mul, mul_one, List.map_map, flatMap_single]
      rfl
    -- apply the program to the new state
    have hR : ∀ b ∈ f x s, Does θ (Fm.ofTree (foldB step).code)
        (.cons (foldB step).code (.cons (enc b.2) (listT (xs.map encE))))
        ((foldL f xs b.2).map (Prod.map id enc)) ((xs.map fun x => d x + 30).sum + 10) := by
      intro b hb
      rw [Fm.ofTree_code]
      exact ih (fun y ys s hy => h y ys s (List.mem_cons_of_mem _ hy)) (h2 b hb)
    have e4 := Does.runT (f := fun s' => (foldL f xs s').map (Prod.map id enc))
      (Gives.id (θ := θ)
        (.cons (foldB step).code (.cons (enc s) (listT (encE x :: xs.map encE))))).hd e3 hR
    rw [bindW_map] at e4
    refine (Does.ite_true (Gives.id _).tl.tl (by simp [listT]) e4).mono ?_
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A fold with a typed state. -/
theorem foldT {step s l : Fm} {x : Tree} {encE : ε → Tree} {enc : β → Tree}
    {f : ε → β → List (A × β)} {Inv : List ε → β → Prop} {d : ε → ℕ} {xs : List ε} {cs cl : ℕ}
    {s₀ : β} (hs : Gives θ s x (enc s₀) cs)
    (hl : Gives θ l x (listT (xs.map encE)) cl) (h : ∀ x ys s, x ∈ xs → Inv (x :: ys) s →
      Does θ step (.cons (encE x) (enc s)) ((f x s).map (Prod.map id enc)) (d x) ∧
        ∀ q ∈ f x s, Inv ys q.2)
    (h0 : Inv xs s₀) : Does θ (foldF step s l) x ((foldL f xs s₀).map (Prod.map id enc))
      (cs + cl + (xs.map fun x => d x + 30).sum + 20) := by
  exact (Does.of_gives (Gives.cons (Gives.quote _ _) (Gives.cons hs hl)) (foldB_doesT h h0)).mono
      (by omega)

theorem foldL_det (g : ε → β → β) (xs : List ε) (s : β) :
    foldL (A := A) (fun x s => [(1, g x s)]) xs s = [(1, xs.foldl (fun s x => g x s) s)] := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rw [foldL, bindW_single, ih]; rfl

/-- A deterministic fold with a typed state. -/
theorem foldTG {step s l : Fm} {x : Tree} {encE : ε → Tree} {enc : β → Tree} {g : ε → β → β}
    {Inv : List ε → β → Prop} {d : ε → ℕ} {xs : List ε} {cs cl : ℕ} {s₀ : β}
    (hs : Gives θ s x (enc s₀) cs)
    (hl : Gives θ l x (listT (xs.map encE)) cl) (h : ∀ x ys s, x ∈ xs → Inv (x :: ys) s →
      Gives θ step (.cons (encE x) (enc s)) (enc (g x s)) (d x) ∧ Inv ys (g x s)) (h0 : Inv xs s₀) :
    Gives θ (foldF step s l) x (enc (xs.foldl (fun s x => g x s) s₀))
      (cs + cl + (xs.map fun x => d x + 30).sum + 20) := by
  have := foldT (θ := θ) (f := fun x s => [((1 : A), g x s)]) (enc := enc) hs hl
      (fun x ys s hx hs => by
    obtain ⟨h1, h2⟩ := h x ys s hx hs
    refine ⟨h1, fun q hq => ?_⟩
    rw [List.mem_singleton] at hq
    subst hq
    exact h2) h0
  rw [foldL_det] at this
  exact this

end Fold

end Nc.Grp

namespace NS1

open _root_.NS1.Tree Nc.Grp

variable {A : Type} [CommRing A] {θ : List Bool → A}

section Fold

section

-- A fold of `step` over the list `xs` given by `l`, from the state `σ` given by `s` at the argument `x`, with an
-- invariant `Inv` and the cost `d` of a step.
variable {step s l : Fm} {x σ : Tree} {cs cl : ℕ} {Inv : List Tree → Tree → Prop} {d : Tree → ℕ} {xs : List Tree}

theorem foldF_does {f : Tree → Tree → List (A × Tree)} (hs : Gives θ s x σ cs)
    (hl : Gives θ l x (listT xs) cl) (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ →
      Does θ step (.cons x σ) (f x σ) (d x) ∧ ∀ q ∈ f x σ, Inv ys q.2) (hσ : Inv xs σ) :
    Does θ (foldF step s l) x (foldL f xs σ) (cs + cl + (xs.map fun x => d x + 30).sum + 20) := by
  simpa using foldT (encE := id) (enc := id) hs (by rwa [List.map_id]) (by simpa using h) hσ

/-- A deterministic fold. -/
theorem foldF_gives {g : Tree → Tree → Tree} (hs : Gives θ s x σ cs)
    (hl : Gives θ l x (listT xs) cl) (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ →
      Gives θ step (.cons x σ) (g x σ) (d x) ∧ Inv ys (g x σ)) (hσ : Inv xs σ) :
    Gives θ (foldF step s l) x (xs.foldl (fun σ x => g x σ) σ)
      (cs + cl + (xs.map fun x => d x + 30).sum + 20) :=
  foldTG (encE := id) (enc := id) hs (by rwa [List.map_id]) h hσ

end

/-- Reverse a list onto another one. -/
theorem foldl_rev (xs : List Tree) (ys : List Tree) :
    xs.foldl (fun σ x => Tree.cons x σ) (listT ys) = listT (xs.reverse ++ ys) := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, show Tree.cons x (listT ys) = listT (x :: ys) from rfl, ih]
    simp

theorem rev_gives {s l : Fm} {x : Tree} {cs cl : ℕ} {xs ys : List Tree} (hs : Gives θ s x (listT ys) cs)
    (hl : Gives θ l x (listT xs) cl) :
    Gives θ (foldF .id s l) x (listT (xs.reverse ++ ys)) (cs + cl + xs.length * 31 + 20) := by
  have := foldF_gives (step := .id) (g := fun x σ => .cons x σ) (Inv := fun _ _ => True) (d := fun _ => 1) hs hl
    (fun x _ σ _ _ => ⟨Gives.id _, trivial⟩) trivial
  rw [foldl_rev] at this
  simpa using this

/-- Concatenation. -/
def appF (a b : Fm) : Fm := foldF .id b (foldF .id (.quote .nil) a)

theorem appF_gives {a b : Fm} {x : Tree} {ca cb : ℕ} {xs ys : List Tree} (ha : Gives θ a x (listT xs) ca)
    (hb : Gives θ b x (listT ys) cb) :
    Gives θ (appF a b) x (listT (xs ++ ys)) (ca + cb + xs.length * 62 + 41) := by
  have h1 := rev_gives (Gives.quote (θ := θ) (listT []) x) ha
  rw [List.append_nil] at h1
  have h2 := rev_gives hb h1
  rw [List.reverse_reverse, List.length_reverse] at h2
  exact h2.mono (by omega)

/-- Concatenation of lists of bits. -/
theorem appBits_gives {a b : Fm} {x : Tree} {ca cb : ℕ} {v w : List Bool} (ha : Gives θ a x (ofBits v) ca)
    (hb : Gives θ b x (ofBits w) cb) : Gives θ (appF a b) x (ofBits (v ++ w)) (ca + cb + v.length * 62 + 41) := by
  rw [← listT_ofBits] at ha hb ⊢
  have := appF_gives ha hb
  rw [← List.map_append, List.length_map] at this
  exact this

end Fold

section Map

/-- Apply `step` to (parameter, element) for all elements of a list. The argument is (this program, (parameter,
list)). -/
def mapB (step : Fm) : Fm := .ite (.tl (.tl .id))
  (.cons (lett (.cons (.hd (.tl .id)) (.hd (.tl (.tl .id)))) step)
    (.run (.hd .id) (.cons (.hd .id) (.cons (.hd (.tl .id)) (.tl (.tl (.tl .id))))))) (.quote .nil)

/-- Map: `e` gives the parameter, `l` the list. -/
def mapF (step e l : Fm) : Fm := app (mapB step).code (.cons (.quote (mapB step).code) (.cons e l))

theorem mapB_gives {step : Fm} {e : Tree} {g : Tree → Tree} {d : Tree → ℕ} {xs : List Tree}
    (h : ∀ x ∈ xs, Gives θ step (.cons e x) (g x) (d x)) :
    Gives θ (mapB step) (.cons (mapB step).code (.cons e (listT xs))) (listT (xs.map g))
      ((xs.map fun x => d x + 40).sum + 10) := by
  induction xs with
  | nil => exact ((Gives.id _).tl.tl.ite_false (Gives.quote _ _)).mono (by simp)
  | cons x xs ih =>
    refine Does.mono (Gives.ite_true (Gives.id _).tl.tl (by simp [listT]) (Gives.cons
      (Gives.lett (Gives.cons (Gives.id _).tl.hd (Gives.id _).tl.tl.hd) (h x List.mem_cons_self))
      (Does.self ((Gives.id _).hd.cons ((Gives.id _).tl.hd.cons (Gives.id _).tl.tl.tl))
        (ih fun y hy => h y (List.mem_cons_of_mem _ hy))))) ?_
    simp only [List.map_cons, List.sum_cons]
    omega

theorem mapF_gives {step ef l : Fm} {x e : Tree} {ce cl : ℕ} {g : Tree → Tree} {d : Tree → ℕ} {xs : List Tree}
    (he : Gives θ ef x e ce) (hl : Gives θ l x (listT xs) cl) (h : ∀ x ∈ xs, Gives θ step (.cons e x) (g x) (d x)) :
    Gives θ (mapF step ef l) x (listT (xs.map g)) (ce + cl + (xs.map fun x => d x + 40).sum + 20) := by
  exact (Gives.lett (Gives.cons (Gives.quote _ _) (Gives.cons he hl)) (mapB_gives h)).mono
    (by omega)

end Map

section Eq

/-- Equality of trees: 1 if equal, else empty. The argument is (this program, (a, b)). -/
def eqB : Fm := .ite (.hd (.tl .id))
  (.ite (.tl (.tl .id))
    (.ite (.run (.hd .id) (.cons (.hd .id) (.cons (.hd (.hd (.tl .id))) (.hd (.tl (.tl .id))))))
      (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.tl (.tl (.tl .id))))))
      (.quote .nil))
    (.quote .nil))
  (.ite (.tl (.tl .id)) (.quote .nil) (.quote one))

/-- Equality of two values. -/
def eqF (a b : Fm) : Fm := app eqB.code (.cons (.quote eqB.code) (.cons a b))

theorem eqB_gives (a b : Tree) : Gives θ eqB (.cons eqB.code (.cons a b)) (bit (decide (a = b))) (60 * a.size) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil =>
      refine ((Gives.id _).tl.hd.ite_false ((Gives.id _).tl.tl.ite_false (Gives.quote one _))).mono ?_
      simp [size]
    | cons b1 b2 =>
      refine ((Gives.id _).tl.hd.ite_false ((Gives.id _).tl.tl.ite_true (by simp) (Gives.quote .nil _))).mono ?_
      simp [size]
  | cons a1 a2 ih1 ih2 =>
    cases b with
    | nil =>
      refine ((Gives.id _).tl.hd.ite_true (by simp) ((Gives.id _).tl.tl.ite_false (Gives.quote .nil _))).mono ?_
      simp only [size]
      omega
    | cons b1 b2 =>
      have r1 := Does.self ((Gives.id (θ := θ)
        (.cons eqB.code (.cons (.cons a1 a2) (.cons b1 b2)))).hd.cons
        ((Gives.id _).tl.hd.hd.cons (Gives.id _).tl.tl.hd)) (ih1 b1)
      by_cases hab : a1 = b1
      · have hb : bit (decide (a1 = b1)) ≠ .nil := by simp [hab, bit, one]
        have e : decide (Tree.cons a1 a2 = Tree.cons b1 b2) = decide (a2 = b2) := by simp [hab]
        rw [e]
        refine ((Gives.id _).tl.hd.ite_true (by simp) ((Gives.id _).tl.tl.ite_true (by simp)
          (Gives.ite_true r1 hb (Does.self
            ((Gives.id _).hd.cons ((Gives.id _).tl.hd.tl.cons (Gives.id _).tl.tl.tl))
            (ih2 b2))))).mono ?_
        simp only [size]
        omega
      · have hb : bit (decide (a1 = b1)) = .nil := by simp [hab, bit]
        rw [hb] at r1
        have e : bit (decide (Tree.cons a1 a2 = Tree.cons b1 b2)) = .nil := by simp [hab, bit]
        rw [e]
        refine ((Gives.id _).tl.hd.ite_true (by simp) ((Gives.id _).tl.tl.ite_true (by simp)
          (Gives.ite_false r1 (Gives.quote .nil _)))).mono ?_
        simp only [size]
        omega

theorem eqF_gives {a b : Fm} {x u v : Tree} {ca cb : ℕ} (ha : Gives θ a x u ca) (hb : Gives θ b x v cb) :
    Gives θ (eqF a b) x (bit (decide (u = v))) (ca + cb + 60 * u.size + 10) := by
  exact (Gives.lett (Gives.cons (Gives.quote _ _) (Gives.cons ha hb)) (eqB_gives u v)).mono
    (by omega)

end Eq

section Choice

/-- Choose an element of a list. The argument is (this program, list). -/
def pickB : Fm := .ite (.tl .id)
  (.ite .guess (.hd (.tl .id)) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id))))) .fail

/-- Choose an element of a list. -/
def pickF (l : Fm) : Fm := app pickB.code (.cons (.quote pickB.code) l)

theorem pickB_does (xs : List Tree) :
    Does θ pickB (.cons pickB.code (listT xs)) (xs.map fun x => (1, x)) (20 * xs.length + 10) := by
  induction xs with
  | nil => exact (Does.ite_false (Gives.id _).tl (Does.fail _)).mono (by simp)
  | cons x xs ih =>
    refine Does.mono (Does.ite_true (Gives.id _).tl (by simp [listT]) (Does.either
      (Gives.id _).tl.hd (Does.self ((Gives.id _).hd.cons (Gives.id _).tl.tl) ih))) ?_
    simp only [List.length_cons]
    omega

theorem pickF_does {l : Fm} {x : Tree} {cl : ℕ} {xs : List Tree} (hl : Gives θ l x (listT xs) cl) :
    Does θ (pickF l) x (xs.map fun x => (1, x)) (cl + 20 * xs.length + 20) := by
  exact (Does.of_gives (Gives.cons (Gives.quote _ _) hl) (pickB_does xs)).mono (by omega)

end Choice

section Tries

/-- Tries: (value, (left, right)); the empty tree is the empty trie. -/
def tget : List Bool → Tree → Tree
  | [], t => t.hd
  | true :: p, t => tget p t.tl.tl
  | false :: p, t => tget p t.tl.hd

/-- Write a value. -/
def tset : List Bool → Tree → Tree → Tree
  | [], v, t => .cons v t.tl
  | true :: p, v, t => .cons t.hd (.cons t.tl.hd (tset p v t.tl.tl))
  | false :: p, v, t => .cons t.hd (.cons (tset p v t.tl.hd) t.tl.tl)

theorem tget_nil (p : List Bool) : tget p .nil = .nil := by
  induction p with
  | nil => rfl
  | cons b p ih => cases b <;> exact ih

theorem tget_tset (p p' : List Bool) (v t : Tree) : tget p (tset p' v t) = if p = p' then v else tget p t := by
  induction p' generalizing p t with
  | nil =>
    cases p with
    | nil => rfl
    | cons b p => cases b <;> simp [tset, tget]
  | cons b' p' ih =>
    cases p with
    | nil => cases b' <;> simp [tset, tget]
    | cons b p =>
      cases b <;> cases b' <;> simp [tset, tget, ih]

/-- Read a value. The argument is (this program, (path, trie)). -/
def getB : Fm := .ite (.hd (.tl .id))
  (.ite (.hd (.hd (.tl .id)))
    (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.tl (.tl (.tl (.tl .id)))))))
    (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.hd (.tl (.tl (.tl .id))))))))
  (.hd (.tl (.tl .id)))

/-- Read a value: `p` gives the path, `t` the trie. -/
def getF (p t : Fm) : Fm := app getB.code (.cons (.quote getB.code) (.cons p t))

theorem getB_gives (p : Tree) (t : Tree) :
    Gives θ getB (.cons getB.code (.cons p t)) (tget p.path t) (30 * p.len + 10) := by
  induction p generalizing t with
  | nil => exact ((Gives.id _).tl.hd.ite_false (Gives.id _).tl.tl.hd).mono (by simp [len])
  | cons a p _ ih =>
    by_cases ha : a = .nil
    · subst ha
      refine Does.mono (Gives.ite_true (Gives.id _).tl.hd (by simp)
        (Gives.ite_false (Gives.id _).tl.hd.hd (Does.self
          ((Gives.id _).hd.cons ((Gives.id _).tl.hd.tl.cons (Gives.id _).tl.tl.tl.hd))
          (ih _)))) ?_
      simp only [len]
      omega
    · have e : tget (Tree.cons a p).path t = tget p.path t.tl.tl := by simp [path, ha, tget]
      rw [e]
      refine Does.mono (Gives.ite_true (Gives.id _).tl.hd (by simp)
        (Gives.ite_true (Gives.id _).tl.hd.hd (by simpa using ha) (Does.self
          ((Gives.id _).hd.cons ((Gives.id _).tl.hd.tl.cons (Gives.id _).tl.tl.tl.tl))
          (ih _)))) ?_
      simp only [len]
      omega

theorem getF_gives {pf tf : Fm} {x p t : Tree} {cp ct : ℕ} (hp : Gives θ pf x p cp) (ht : Gives θ tf x t ct) :
    Gives θ (getF pf tf) x (tget p.path t) (cp + ct + 30 * p.len + 20) := by
  exact (Gives.lett (Gives.cons (Gives.quote _ _) (Gives.cons hp ht)) (getB_gives p t)).mono
    (by omega)

/-- Write a value. The argument is (this program, (path, (value, trie))). -/
def setB : Fm := .ite (.hd (.tl .id))
  (.ite (.hd (.hd (.tl .id)))
    (.cons (.hd (.tl (.tl (.tl .id)))) (.cons (.hd (.tl (.tl (.tl (.tl .id)))))
      (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.cons (.hd (.tl (.tl .id)))
        (.tl (.tl (.tl (.tl (.tl .id)))))))))))
    (.cons (.hd (.tl (.tl (.tl .id)))) (.cons
      (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.cons (.hd (.tl (.tl .id)))
        (.hd (.tl (.tl (.tl (.tl .id)))))))))
      (.tl (.tl (.tl (.tl (.tl .id))))))))
  (.cons (.hd (.tl (.tl .id))) (.tl (.tl (.tl (.tl .id)))))

/-- Write a value: `p` gives the path, `v` the value, `t` the trie. -/
def setF (p v t : Fm) : Fm := app setB.code (.cons (.quote setB.code) (.cons p (.cons v t)))

theorem setB_gives (p v t : Tree) :
    Gives θ setB (.cons setB.code (.cons p (.cons v t))) (tset p.path v t) (60 * p.len + 20) := by
  induction p generalizing t with
  | nil =>
    exact ((Gives.id _).tl.hd.ite_false (Gives.cons (Gives.id _).tl.tl.hd (Gives.id _).tl.tl.tl.tl)).mono (by simp [len])
  | cons a p _ ih =>
    by_cases ha : a = .nil
    · subst ha
      refine Does.mono (Gives.ite_true (Gives.id _).tl.hd (by simp)
        (Gives.ite_false (Gives.id _).tl.hd.hd (Gives.cons (Gives.id _).tl.tl.tl.hd (Gives.cons
          (Does.self ((Gives.id _).hd.cons ((Gives.id _).tl.hd.tl.cons
            ((Gives.id _).tl.tl.hd.cons (Gives.id _).tl.tl.tl.tl.hd))) (ih _))
          (Gives.id _).tl.tl.tl.tl.tl)))) ?_
      simp only [len]
      omega
    · have e : tset (Tree.cons a p).path v t =
          .cons t.hd (.cons t.tl.hd (tset p.path v t.tl.tl)) := by
        simp [path, ha, tset]
      rw [e]
      refine Does.mono (Gives.ite_true (Gives.id _).tl.hd (by simp)
        (Gives.ite_true (Gives.id _).tl.hd.hd (by simpa using ha)
        (Gives.cons (Gives.id _).tl.tl.tl.hd (Gives.cons (Gives.id _).tl.tl.tl.tl.hd (Does.self
          ((Gives.id _).hd.cons ((Gives.id _).tl.hd.tl.cons ((Gives.id _).tl.tl.hd.cons
            (Gives.id _).tl.tl.tl.tl.tl))) (ih _)))))) ?_
      simp only [len]
      omega

theorem setF_gives {pf vf tf : Fm} {x p v t : Tree} {cp cv ct : ℕ} (hp : Gives θ pf x p cp) (hv : Gives θ vf x v cv)
    (ht : Gives θ tf x t ct) : Gives θ (setF pf vf tf) x (tset p.path v t) (cp + cv + ct + 60 * p.len + 30) := by
  refine (Gives.app (p := setB.code) (Gives.cons (Gives.quote _ _) (Gives.cons hp (Gives.cons hv ht))) (by
    rw [Fm.ofTree_code]
    exact setB_gives p v t)).mono (by omega)

end Tries

section Weights

/-- Formulas for elements of `A`. -/
inductive WE where
  /-- 0 -/
  | zero
  /-- 1 -/
  | one
  /-- a named constant -/
  | nm (p : List Bool)
  /-- sum -/
  | add (a b : WE)
  /-- product -/
  | mul (a b : WE)

/-- The value. -/
def WE.val (θ : List Bool → A) : WE → A
  | zero => 0
  | one => 1
  | nm p => θ p
  | add a b => a.val θ + b.val θ
  | mul a b => a.val θ * b.val θ

/-- The formula of the machine. -/
def WE.fm : WE → Fm
  | zero => .fail
  | one => .quote .nil
  | nm p => .theta (.quote (ofBits p))
  | add a b => .ite .guess a.fm b.fm
  | mul a b => lett a.fm (lett b.fm (.quote .nil))

/-- The cost. -/
def WE.cost : WE → ℕ
  | zero => 1
  | one => 1
  | nm _ => 2
  | add a b => max a.cost b.cost + 2
  | mul a b => a.cost + b.cost + 10

/-- Multiply the weight by an element of `A`. -/
theorem WE.does (e : WE) (x : Tree) : Does θ e.fm x [(e.val θ, .nil)] e.cost := by
  induction e generalizing x with
  | zero =>
    refine ((Does.fail x).congr (by simp) fun φ => ?_).mono (Nat.zero_le _)
    simp [WE.val]
  | one => exact Gives.quote .nil x
  | nm p =>
    have := Does.theta (Gives.quote (θ := θ) (ofBits p) x)
    rwa [path_ofBits] at this
  | add a b iha ihb =>
    refine (Does.either (iha x) (ihb x)).congr ?_ fun φ => ?_
    · intro q hq
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> rfl
    · simp [WE.val, add_mul]
  | mul a b iha ihb =>
    have h1 := Does.lett (R := fun _ => [(b.val θ, .nil)]) (G := lett b.fm (.quote .nil)) (iha x)
      (d := b.cost + 1 + 2) (by
        intro q hq
        have := Does.lett (R := fun _ => [((1 : A), Tree.nil)]) (G := .quote .nil) (ihb q.2) (d := 1)
          fun p _ => Gives.quote .nil p.2
        simpa [bindW] using this)
    refine (h1.congr ?_ fun φ => ?_).mono ?_
    · intro q hq
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [bindW, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil,
        List.mem_singleton] at hq
      subst hq
      rfl
    · simp [bindW, WE.val]
    · simp only [WE.cost]
      omega

/-- Every element of the subring generated by the constants has a formula, if −1 is a constant. -/
theorem WE.exists_of_adjoin {p₀ : List Bool} (h : θ p₀ = -1) {a : A} (ha : a ∈ Subring.closure (Set.range θ)) :
    ∃ e : WE, e.val θ = a := by
  induction ha using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨.nm p, rfl⟩
  | zero => exact ⟨.zero, rfl⟩
  | one => exact ⟨.one, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨f, rfl⟩ := hy
    exact ⟨.add e f, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨f, rfl⟩ := hy
    exact ⟨.mul e f, rfl⟩
  | neg x _ hx =>
    obtain ⟨e, rfl⟩ := hx
    exact ⟨.mul (.nm p₀) e, by simp [WE.val, h]⟩

end Weights

end NS1
