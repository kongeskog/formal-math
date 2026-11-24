/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Lists

/-!
# Weighted lists of typed values

Programs of the tree machine whose values are encodings of typed values. Lemmas on the weighted lists `bindW`, `wsum` of `NS1.Comp`.
`Does.appT`, `Does.lettT`, `foldT`: composition and folds with typed values.
-/

set_option linter.unusedSectionVars false

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
  simp only [bindW, List.flatMap_assoc, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def, mul_assoc]

theorem bindW_pure (l : List α) (g : α → β) (f : β → List (A × γ)) :
    bindW (l.map fun t => ((1 : A), g t)) f = l.flatMap fun t => f (g t) := by
  simp only [bindW, List.flatMap_map, one_mul, List.map_id']

/-- The weighted sums are determined by the program. -/
theorem _root_.NS1.Does.wsum_unique {F : Fm} {x : Tree} {Q Q' : List (A × Tree)} {c d : ℕ} (h : Does θ F x Q c)
    (h' : Does θ F x Q' d) (φ : Tree → A) : wsum Q φ = wsum Q' φ := by
  rw [← h.evl.2 φ, ← h'.evl.2 φ]

/-- Replace the list. -/
theorem _root_.NS1.Does.replace {F : Fm} {x : Tree} {Q Q' : List (A × Tree)} {c : ℕ} (h : Does θ F x Q c) (hQ : Q = Q') :
    Does θ F x Q' c := hQ ▸ h

/-- A rule for lists of trees with a function `R` on trees gives the rule for typed values. -/
theorem exists_untyped {p : Tree} {l : List (A × β)} {enc : β → Tree} {f : β → List (A × Tree)}
    {d : ℕ} (hG : ∀ b ∈ l, Does θ (Fm.ofTree p) (enc b.2) (f b.2) d) :
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
theorem _root_.NS1.Does.appT {F : Fm} {x p : Tree} {l : List (A × β)} {enc : β → Tree} {f : β → List (A × Tree)} {c d : ℕ}
    (hF : Does θ F x (l.map (Prod.map id enc)) c) (hG : ∀ b ∈ l, Does θ (Fm.ofTree p) (enc b.2) (f b.2) d) :
    Does θ (app p F) x (bindW l f) (c + d + 2) := by
  obtain ⟨R, h1, h2⟩ := exists_untyped hG
  exact h2 (Does.app hF h1)

/-- `let` with typed values. -/
theorem _root_.NS1.Does.lettT {F G : Fm} {x : Tree} {l : List (A × β)} {enc : β → Tree} {f : β → List (A × Tree)} {c d : ℕ}
    (hF : Does θ F x (l.map (Prod.map id enc)) c) (hG : ∀ b ∈ l, Does θ G (enc b.2) (f b.2) d) :
    Does θ (lett F G) x (bindW l f) (c + d + 2) :=
  Does.appT (p := G.code) hF (by rw [Fm.ofTree_code]; exact hG)

theorem bindW_map (l : List (A × α)) (f : α → List (A × β)) (e : β → γ) :
    bindW l (fun a => (f a).map (Prod.map id e)) = (bindW l f).map (Prod.map id e) := by
  simp only [bindW, List.map_flatMap, List.map_map]
  rfl

/-- `let` with typed values and typed results. -/
theorem _root_.NS1.Does.lettE {F G : Fm} {x : Tree} {l : List (A × β)} {enc : β → Tree} {enc' : γ → Tree}
    {f : β → List (A × γ)} {c d : ℕ} (hF : Does θ F x (l.map (Prod.map id enc)) c)
    (hG : ∀ b ∈ l, Does θ G (enc b.2) ((f b.2).map (Prod.map id enc')) d) :
    Does θ (lett F G) x ((bindW l f).map (Prod.map id enc')) (c + d + 2) := by
  rw [← bindW_map]
  exact Does.lettT hF hG

/-- The first of two formulas has the empty value: go on with the second one. -/
theorem _root_.NS1.Does.ite_nil {F G H : Fm} {x : Tree} {a : A} {Q : List (A × Tree)} {c d : ℕ} (hF : Does θ F x [(a, .nil)] c)
    (hH : Does θ H x Q d) : Does θ (.ite F G H) x (Q.map fun r => (a * r.1, r.2)) (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hH
  have hout : ∀ r ∈ l, r.out = .nil := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.ite (L := fun _ => l') e1 (fun r hr h => absurd (hout r hr) h) (fun r _ _ => f1), ?_, fun φ => ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, q, hq, b3⟩ := f2 s hs
    refine ⟨by simp [Run.seq, Run.tick, a1, b1], ?_, (a * q.1, q.2), List.mem_map.2 ⟨q, hq, rfl⟩, b3⟩
    simp only [Run.seq, Run.tick]
    omega
  · rw [sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.map fun s => (r.seq s).tick s.out).map fun u => u.th * φ u.out).sum = r.th * wsum Q φ := by
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
theorem _root_.NS1.Does.runT {F G : Fm} {x p : Tree} {l : List (A × β)} {enc : β → Tree} {f : β → List (A × Tree)} {c d e : ℕ}
    (hF : Gives θ F x p c) (hG : Does θ G x (l.map (Prod.map id enc)) d)
    (h : ∀ b ∈ l, Does θ (Fm.ofTree p) (enc b.2) (f b.2) e) : Does θ (.run F G) x (bindW l f) (c + d + e + 1) := by
  obtain ⟨R, h1, h2⟩ := exists_untyped h
  exact h2 (Does.runW hF hG h1)

/-- `let`, with the argument kept, typed values. -/
theorem _root_.NS1.Does.letkT {F G : Fm} {x : Tree} {l : List (A × β)} {enc : β → Tree} {f : β → List (A × Tree)}
    {c d : ℕ} (hF : Does θ F x (l.map (Prod.map id enc)) c) (hG : ∀ b ∈ l, Does θ G (.cons x (enc b.2)) (f b.2) d) :
    Does θ (lett (.cons .id F) G) x (bindW l f) (c + d + 4) := by
  have h1 : Does θ (.cons .id F) x (l.map (Prod.map id fun b => .cons x (enc b))) (1 + c + 1) := by
    refine (Does.cons (Gives.id (θ := θ) x) hF).replace ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, one_mul]
    rfl
  exact (Does.lettT h1 hG).mono (by omega)

section Fold

variable {ε : Type}

/-- The weighted list of a fold. -/
def foldL (f : ε → β → List (A × β)) : List ε → β → List (A × β)
  | [], s => [(1, s)]
  | x :: xs, s => bindW (f x s) (foldL f xs)

theorem foldB_doesT {step : Fm} {encE : ε → Tree} {enc : β → Tree} {f : ε → β → List (A × β)}
    {Inv : List ε → β → Prop} {d : ε → ℕ} {xs : List ε} (h : ∀ x ys s, x ∈ xs → Inv (x :: ys) s →
      Does θ step (.cons (encE x) (enc s)) ((f x s).map (Prod.map id enc)) (d x) ∧ ∀ q ∈ f x s, Inv ys q.2)
    {s : β} (hs : Inv xs s) :
    Does θ (foldB step) (.cons (foldB step).code (.cons (enc s) (listT (xs.map encE))))
      ((foldL f xs s).map (Prod.map id enc)) ((xs.map fun x => d x + 30).sum + 10) := by
  induction xs generalizing s with
  | nil => exact (Does.ite_false (Gives.id _).tl.tl (Gives.id _).tl.hd).mono (by simp)
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := h x xs s List.mem_cons_self hs
    rw [List.map_cons]
    have e1 : Does θ (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
        (.cons (foldB step).code (.cons (enc s) (listT (encE x :: xs.map encE)))) ((f x s).map (Prod.map id enc))
        (8 + d x + 2) :=
      Does.of_gives (Gives.cons (Gives.id _).tl.tl.hd (Gives.id _).tl.hd) h1
    have e2 := Does.cons (Gives.id (θ := θ) (.cons (foldB step).code (.cons (enc s) (listT (encE x :: xs.map encE))))).hd
      (Does.cons e1 (Gives.id (.cons (foldB step).code (.cons (enc s) (listT (encE x :: xs.map encE))))).tl.tl.tl)
    have e3 : Does θ (.cons (.hd .id) (.cons (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
        (.tl (.tl (.tl .id))))) (.cons (foldB step).code (.cons (enc s) (listT (encE x :: xs.map encE))))
        ((f x s).map (Prod.map id fun s' => .cons (foldB step).code (.cons (enc s') (listT (xs.map encE)))))
        (8 + d x + 2 + 8) := by
      refine (e2.replace ?_).mono (by omega)
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil, one_mul, mul_one,
        List.map_map, flatMap_single]
      rfl
    -- apply the program to the new state
    have hR : ∀ b ∈ f x s, Does θ (Fm.ofTree (foldB step).code)
        (.cons (foldB step).code (.cons (enc b.2) (listT (xs.map encE))))
        ((foldL f xs b.2).map (Prod.map id enc)) ((xs.map fun x => d x + 30).sum + 10) := by
      intro b hb
      rw [Fm.ofTree_code]
      exact ih (fun y ys s hy => h y ys s (List.mem_cons_of_mem _ hy)) (h2 b hb)
    have e4 := Does.runT (f := fun s' => (foldL f xs s').map (Prod.map id enc))
      (Gives.id (θ := θ) (.cons (foldB step).code (.cons (enc s) (listT (encE x :: xs.map encE))))).hd e3 hR
    rw [bindW_map] at e4
    refine (Does.ite_true (Gives.id _).tl.tl (by simp [listT]) e4).mono ?_
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A fold with a typed state. -/
theorem foldT {step s l : Fm} {x : Tree} {encE : ε → Tree} {enc : β → Tree} {f : ε → β → List (A × β)}
    {Inv : List ε → β → Prop} {d : ε → ℕ} {xs : List ε} {cs cl : ℕ} {s₀ : β} (hs : Gives θ s x (enc s₀) cs)
    (hl : Gives θ l x (listT (xs.map encE)) cl) (h : ∀ x ys s, x ∈ xs → Inv (x :: ys) s →
      Does θ step (.cons (encE x) (enc s)) ((f x s).map (Prod.map id enc)) (d x) ∧ ∀ q ∈ f x s, Inv ys q.2)
    (h0 : Inv xs s₀) : Does θ (foldF step s l) x ((foldL f xs s₀).map (Prod.map id enc))
      (cs + cl + (xs.map fun x => d x + 30).sum + 20) := by
  have h1 := Gives.cons (Gives.quote (θ := θ) (foldB step).code x) (Gives.cons hs hl)
  have h2 := Does.appT (p := (foldB step).code) (l := [((1 : A), ())])
    (enc := fun _ => .cons (foldB step).code (.cons (enc s₀) (listT (xs.map encE))))
    (f := fun _ => (foldL f xs s₀).map (Prod.map id enc)) h1 (fun b _ => by
      rw [Fm.ofTree_code]
      exact foldB_doesT h h0)
  rw [bindW_single] at h2
  exact h2.mono (by omega)

theorem foldL_det (g : ε → β → β) (xs : List ε) (s : β) :
    foldL (A := A) (fun x s => [(1, g x s)]) xs s = [(1, xs.foldl (fun s x => g x s) s)] := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rw [foldL, bindW_single, ih]; rfl

/-- A deterministic fold with a typed state. -/
theorem foldTG {step s l : Fm} {x : Tree} {encE : ε → Tree} {enc : β → Tree} {g : ε → β → β}
    {Inv : List ε → β → Prop} {d : ε → ℕ} {xs : List ε} {cs cl : ℕ} {s₀ : β} (hs : Gives θ s x (enc s₀) cs)
    (hl : Gives θ l x (listT (xs.map encE)) cl) (h : ∀ x ys s, x ∈ xs → Inv (x :: ys) s →
      Gives θ step (.cons (encE x) (enc s)) (enc (g x s)) (d x) ∧ Inv ys (g x s)) (h0 : Inv xs s₀) :
    Gives θ (foldF step s l) x (enc (xs.foldl (fun s x => g x s) s₀))
      (cs + cl + (xs.map fun x => d x + 30).sum + 20) := by
  have := foldT (θ := θ) (f := fun x s => [((1 : A), g x s)]) (enc := enc) hs hl (fun x ys s hx hs => by
    obtain ⟨h1, h2⟩ := h x ys s hx hs
    refine ⟨h1, fun q hq => ?_⟩
    rw [List.mem_singleton] at hq
    subst hq
    exact h2) h0
  rw [foldL_det] at this
  exact this

end Fold

end Nc.Grp
