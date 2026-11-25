/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Interp

/-!
# Lists of runs that correspond to other lists
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

section Rel

variable {α β γ δ : Type*}

theorem forall₂_flatMap {R : α → β → Prop} {S : γ → δ → Prop} {l : List α} {l' : List β} {f : α → List γ}
    {g : β → List δ} (h : List.Forall₂ R l l') (hf : ∀ a ∈ l, ∀ b ∈ l', R a b → List.Forall₂ S (f a) (g b)) :
    List.Forall₂ S (l.flatMap f) (l'.flatMap g) := by
  induction h with
  | nil => simp
  | cons hab _ ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    refine List.rel_append (hf _ List.mem_cons_self _ List.mem_cons_self hab) (ih fun a ha b hb =>
      hf a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))

theorem forall₂_exists {R : α → β → Prop} {l : List α} {l' : List β} (h : List.Forall₂ R l l') {a : α} (ha : a ∈ l) :
    ∃ b ∈ l', R a b := by
  induction h with
  | nil => simp at ha
  | cons hab _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

/-- `let`, for lists that correspond to other lists. -/
theorem lett_rel {e body : Fm} {x : Tree} {le : List (Run A)} (he : Ev θ e x le) {Q : List β}
    {R : Run A → β → Prop} (hR : List.Forall₂ R le Q) {Q2 : β → List γ} {R2 : Run A → γ → Prop}
    (h : ∀ s ∈ le, ∀ b ∈ Q, R s b → ∃ l2, Ev θ body s.out l2 ∧
      List.Forall₂ (fun t c => R2 ⟨s.cost + t.cost + 2, s.th * t.th, t.out⟩ c) l2 (Q2 b)) :
    ∃ l, Ev θ (lett e body) x l ∧ List.Forall₂ R2 l (Q.flatMap Q2) := by
  refine ⟨_, Ev.lett he fun s hs => ?_, forall₂_flatMap hR fun s hs b hb hsb => ?_⟩
  · obtain ⟨b, hb, hsb⟩ := forall₂_exists hR hs
    obtain ⟨l2, h2, -⟩ := h s hs b hb hsb
    exact h2.hl
  · obtain ⟨l2, h2, h3⟩ := h s hs b hb hsb
    rw [h2.evl, List.forall₂_map_left_iff]
    exact h3

/-- A `flatMap` of singletons is a `map`. -/
theorem flatMap_single {α β : Type*} (l : List α) (g : α → β) : (l.flatMap fun a => [g a]) = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

end Rel

end NS1

