/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.StepRole
import Nc.Grp.GrpVal

/-!
# GROUP computes the value of a group

The first run over the script is the sum over the contents of the cells of the group; with the
contents fixed, the instruction of a base party is its table at the beginning and the instruction
of a role is the table of the role.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {A' K E U0 U1 ub c T : ℕ} {Gr : Type} [DecidableEq Gr]
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}
  {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}
  {key : Cell M U0 U1 → List Bool} {tg : M.R → ℕ}

/-- The guessed bits, as a sum. -/
theorem wsum_gBits (n : ℕ) (G : List Bool → A) :
    wsum (gBits A n) G = ∑ v : Fin n → Bool, G (List.ofFn v) := by
  unfold gBits
  induction n generalizing G with
  | zero => simp [foldL]
  | succ n ih =>
    rw [List.replicate_succ', foldL_append, ih]
    have h1 : ∀ w : List Bool,
        wsum (foldL (fun (_ : Unit) (w : List Bool) => [((1 : A), true :: w), (1, false :: w)])
          [()] w) G = G (true :: w) + G (false :: w) := by
      intro w
      simp [foldL, wsum_bindW, wsum_cons, wsum_nil]
    simp only [h1]
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Bool).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_bool, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    have e : ∀ b : Bool, (Fin.consEquiv fun _ : Fin (n + 1) => Bool) (b, v) = Fin.cons b v :=
      fun _ => rfl
    rw [e, e, List.ofFn_cons, List.ofFn_cons]

theorem Rep.set (hkey : Function.Injective key) {t : Tree} {σ : Cell M U0 U1 → UW ub}
    (h : Rep ub key t σ) (c : Cell M U0 U1) (v : Fin ub → Bool) :
    Rep ub key (tset (key c) (ofBits (List.ofFn v)) t) (Function.update σ c (some v)) := by
  intro c'
  rw [tget_tset]
  by_cases hc : c' = c
  · subst hc
    rw [if_pos rfl, Function.update_self]
    rfl
  · rw [if_neg fun e => hc (hkey e), Function.update_of_ne hc, h]

/-- The contents `y` after the contents at the keys `ks` have been guessed, from the contents
`σ`. -/
def Gs (key : Cell M U0 U1 → List Bool) (ks : List (List Bool))
    (σ y : Cell M U0 U1 → UW ub) : Prop :=
  (∀ c, key c ∈ ks → σ c = none → y c ≠ none) ∧ ∀ c, (key c ∈ ks → σ c ≠ none) → y c = σ c

open Classical in
/-- **Guessing, as a sum over the contents.** -/
theorem wsum_gKs (hkey : Function.Injective key) (hub : 0 < ub) {Ψ : Tree → A}
    {Ψ' : (Cell M U0 U1 → UW ub) → A} (ks : List (List Bool)) (hks : ∀ k ∈ ks, ∃ c, key c = k)
    (t : Tree) (σ : Cell M U0 U1 → UW ub) (h : Rep ub key t σ)
    (hΨ : ∀ t y, Rep ub key t y → Gs key ks σ y → Ψ t = Ψ' y) :
    wsum (foldL (gK A ub) ks t) Ψ = ∑ y ∈ univ.filter (Gs key ks σ), Ψ' y := by
  induction ks generalizing t σ with
  | nil =>
    have e : univ.filter (Gs key [] σ) = {σ} := by
      ext y
      simp only [Gs, List.not_mem_nil, false_imp_iff, implies_true, true_and, mem_filter,
        mem_univ, mem_singleton]
      exact ⟨fun h => funext fun c => h c trivial, fun h c _ => h ▸ rfl⟩
    rw [e, sum_singleton, foldL, wsum_single]
    exact hΨ t σ h ⟨fun _ hc => absurd hc List.not_mem_nil, fun _ _ => rfl⟩
  | cons k ks ih =>
    obtain ⟨c, rfl⟩ := hks k List.mem_cons_self
    have hks' : ∀ k ∈ ks, ∃ c, key c = k := fun k hk => hks k (List.mem_cons_of_mem _ hk)
    have hmem : ∀ c', key c' ∈ key c :: ks ↔ c' = c ∨ key c' ∈ ks := fun c' => by
      rw [List.mem_cons, hkey.eq_iff]
    rw [foldL, wsum_bindW, gK]
    by_cases hc : σ c = none
    · have ht : tget (key c) t = .nil := by rw [h, hc]; rfl
      -- the contents after `c` has been guessed
      have hG : ∀ (v : Fin ub → Bool) y, Gs key ks (Function.update σ c (some v)) y ↔
          Gs key (key c :: ks) σ y ∧ y c = some v := by
        intro v y
        simp only [Gs, hmem, Function.update_apply]
        -- the cell `c` gets the content `some v`, the other cells are as before
        grind
      rw [if_pos ht, wsum_bindW, wsum_gBits]
      simp only [wsum_single]
      rw [Finset.sum_congr rfl fun v _ =>
          ih hks' _ _ (h.set hkey c v) fun t y hr hy => hΨ t y hr ((hG v y).1 hy).1,
        ← Finset.sum_fiberwise (univ.filter (Gs key (key c :: ks) σ)) (fun y => y c) Ψ',
        Fintype.sum_option]
      have e0 : (univ.filter (Gs key (key c :: ks) σ)).filter (fun y => y c = none) = ∅ := by
        ext y
        simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
        exact fun hy => hy.1 c List.mem_cons_self hc
      rw [e0, sum_empty, zero_add]
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr ?_ fun _ _ => rfl
      ext y
      simp only [mem_filter, mem_univ, true_and]
      exact hG v y
    · have ht : tget (key c) t ≠ .nil := by
        rw [h]
        exact fun e => (uwBits_ne_nil hub _).2 hc
          (ofBits_injective (e : ofBits (uwBits (σ c)) = ofBits []))
      have hG : ∀ y, Gs key ks σ y ↔ Gs key (key c :: ks) σ y := by
        intro y
        simp only [Gs, hmem]
        -- the cell `c` has a content, so nothing changes for it
        grind
      rw [if_neg ht, wsum_single, ih hks' t σ h fun t y hr hy => hΨ t y hr ((hG y).1 hy)]
      exact Finset.sum_congr (Finset.filter_congr fun y _ => hG y) fun _ _ => rfl

/-- A fold of folds is the fold over the list of all elements. -/
theorem wsum_foldL_flatMap {ε ε' β : Type} (f : ε' → β → List (A × β)) (F : ε → β → List (A × β))
    (hh : ε → List ε') (hF : ∀ i s (G : β → A), wsum (F i s) G = wsum (foldL f (hh i) s) G)
    (l : List ε) (s : β) (G : β → A) :
    wsum (foldL F l s) G = wsum (foldL f (l.flatMap hh) s) G := by
  induction l generalizing s with
  | nil => rfl
  | cons i l ih =>
    rw [List.flatMap_cons, foldL_append, foldL, wsum_bindW, hF]
    exact wsum_congr fun p _ => ih _

/-- The keys at which an instruction guesses. -/
def gKeys : Ins → List (List Bool)
  | .block _ _ B | .input _ B => B.kR.flatten ++ B.kC.flatten
  | .role _ _ _ keys => keys.flatten
  | _ => []

theorem wsum_insG (ub : ℕ) (i : Ins) (t : Tree) (G : Tree → A) :
    wsum (insG A ub i t) G = wsum (foldL (gK A ub) (gKeys i) t) G := by
  have hk : ∀ kss t (G : Tree → A),
      wsum (gKss A ub kss t) G = wsum (foldL (gK A ub) kss.flatten t) G :=
    fun kss t G => by
      rw [← List.flatMap_id]
      exact wsum_foldL_flatMap _ _ _ (fun _ _ _ => rfl) kss t G
  cases i with
  | block _ _ B | input _ B =>
    rw [insG, wsum_bindW, hk, gKeys, foldL_append]
    exact wsum_congr fun p _ => hk _ _ _
  | role => exact hk _ _ _
  | both | one => rfl

/-- The keys at which the script of a group guesses are the keys of the cells of the group. -/
theorem mem_gKeys_script (b : G.Uid (K + K) U0 M.N U1 → UW ub) (k : List Bool) :
    k ∈ (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key tg b).flatMap gKeys ↔
      ∃ c ∈ dom n o grp g, key c = k := by
  have hbase : ∀ p, gKeys (baseIns (fun z => (qn Q z : ℕ)) cb q x ρ n key p) =
      (List.ofFn fun b => ((List.finRange U0).filter fun k => k.1 < (n p b).1).map fun k =>
        key (Fin.castAdd A' p, .init p b k)).flatten ++
      (List.ofFn fun b => ((List.finRange U0).filter fun k => k.1 < (n b p).1).map fun k =>
        key (Fin.castAdd A' p, .init b p k)).flatten := by
    intro p
    unfold baseIns
    refine Fin.addCases (fun κ => ?_) (fun κ => ?_) p
    · rw [Fin.addCases_left]
      rfl
    · rw [Fin.addCases_right]
      rfl
  have hend : (endIns P n o grp g key b).flatMap gKeys = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro i hi
    obtain ⟨id, -, h⟩ := List.mem_filterMap.1 hi
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> rfl
  rw [script, List.flatMap_append, List.flatMap_append, hend, List.append_nil, List.mem_append,
    List.flatMap_map, List.flatMap_map, List.mem_flatMap, List.mem_flatMap]
  constructor
  · rintro (⟨p, hp, hk⟩ | ⟨r, hr, hk⟩)
    · rw [hbase, List.mem_append] at hk
      rcases hk with hk | hk
      · obtain ⟨l, hl, hk⟩ := List.mem_flatten.1 hk
        obtain ⟨b', rfl⟩ := (List.mem_ofFn' _ _).1 hl
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
        exact ⟨_, mem_dom.2 ⟨mem_baseList.1 hp, G.Plan.init_mem_seenAt.2 (by simpa using hi),
          Or.inl rfl⟩, rfl⟩
      · obtain ⟨l, hl, hk⟩ := List.mem_flatten.1 hk
        obtain ⟨b', rfl⟩ := (List.mem_ofFn' _ _).1 hl
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
        exact ⟨_, mem_dom.2 ⟨mem_baseList.1 hp, G.Plan.init_mem_seenAt.2 (by simpa using hi),
          Or.inr rfl⟩, rfl⟩
    · obtain ⟨l, hl, hk⟩ := List.mem_flatten.1 (show k ∈ List.flatten _ from hk)
      obtain ⟨ν, -, rfl⟩ := List.mem_map.1 hl
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
      exact ⟨_, mem_dom.2 ⟨mem_roleList.1 hr, G.Plan.new_mem_seenAt.2 ⟨r.1.2, by simpa using hi⟩,
        holds_cnAt ν i⟩, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    rcases dom_cases hc with ⟨p, b', i, hg, hi, rfl⟩ | ⟨p, b', i, hg, hi, rfl⟩ |
      ⟨r, ν, i, hg, hi, rfl⟩
    · refine Or.inl ⟨p, mem_baseList.2 hg, ?_⟩
      rw [hbase, List.mem_append]
      exact Or.inl (List.mem_flatten.2
        ⟨_, (List.mem_ofFn' _ _).2 ⟨b', rfl⟩, List.mem_map.2 ⟨i, by simpa using hi, rfl⟩⟩)
    · refine Or.inl ⟨p, mem_baseList.2 hg, ?_⟩
      rw [hbase, List.mem_append]
      exact Or.inr (List.mem_flatten.2
        ⟨_, (List.mem_ofFn' _ _).2 ⟨b', rfl⟩, List.mem_map.2 ⟨i, by simpa using hi, rfl⟩⟩)
    · exact Or.inr ⟨r, mem_roleList.2 hg,
        List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ν, Finset.mem_toList.2 (mem_univ ν), rfl⟩,
          List.mem_map.2 ⟨i, by simpa using hi, rfl⟩⟩⟩

/-- What is compared at a unit. -/
def EndOk (grp : Fin (K + K + A') → Gr) (g : Gr) (σ : Cell M U0 U1 → UW ub) (b : G.Uid (K + K) U0 M.N U1 → UW ub)
    (id : G.Uid (K + K) U0 M.N U1) : Prop :=
  (grp (G.hold0 M.np id) = g → grp (G.hold1 M.np id) = g →
      uwBits (σ (G.hold0 M.np id, id)) = uwBits (σ (G.hold1 M.np id, id))) ∧
    (grp (G.hold0 M.np id) = g → grp (G.hold1 M.np id) ≠ g → uwBits (σ (G.hold0 M.np id, id)) = uwBits (b id)) ∧
    (grp (G.hold0 M.np id) ≠ g → grp (G.hold1 M.np id) = g → uwBits (σ (G.hold1 M.np id, id)) = uwBits (b id))

open Classical in
/-- The last instructions compare. -/
theorem wsum_end (b : G.Uid (K + K) U0 M.N U1 → UW ub) (l : List (G.Uid (K + K) U0 M.N U1)) (t : Tree)
    (σ : Cell M U0 U1 → UW ub) (hr : Rep ub key t σ) :
    wsum (scriptSem (S := S) θ mu cb kinds T ub (l.filterMap fun id =>
      if grp (G.hold0 M.np id) = g then
        if grp (G.hold1 M.np id) = g then some (.both (key (G.hold0 M.np id, id)) (key (G.hold1 M.np id, id)))
        else some (.one (key (G.hold0 M.np id, id)) (uwBits (b id)))
      else if grp (G.hold1 M.np id) = g then some (.one (key (G.hold1 M.np id, id)) (uwBits (b id)))
      else none) t) (fun _ => 1) =
    if ∀ id ∈ l, EndOk grp g σ b id then 1 else 0 := by
  have hof : ∀ v w : List Bool, ofBits v = ofBits w ↔ v = w := fun v w => ofBits_injective.eq_iff
  induction l with
  | nil => simp [wsum_script_nil]
  | cons id l ih =>
    have hcons : (∀ i ∈ id :: l, EndOk grp g σ b i) ↔ EndOk grp g σ b id ∧ ∀ i ∈ l, EndOk grp g σ b i :=
      List.forall_mem_cons
    by_cases h0 : grp (G.hold0 M.np id) = g
    · by_cases h1 : grp (G.hold1 M.np id) = g
      · rw [List.filterMap_cons_some (by rw [if_pos h0, if_pos h1]), wsum_script_cons, insSem]
        simp only [hr _, hof]
        by_cases he : uwBits (σ (G.hold0 M.np id, id)) = uwBits (σ (G.hold1 M.np id, id))
        · rw [if_pos he, wsum_single, ih]
          refine if_congr ?_ rfl rfl
          rw [hcons]
          simp [EndOk, h0, h1, he]
        · rw [if_neg he, wsum_nil, if_neg fun h => he ((hcons.1 h).1.1 h0 h1)]
      · rw [List.filterMap_cons_some (by rw [if_pos h0, if_neg h1]), wsum_script_cons, insSem]
        simp only [hr _, hof]
        by_cases he : uwBits (σ (G.hold0 M.np id, id)) = uwBits (b id)
        · rw [if_pos he, wsum_single, ih]
          refine if_congr ?_ rfl rfl
          rw [hcons]
          simp [EndOk, h0, h1, he]
        · rw [if_neg he, wsum_nil, if_neg fun h => he ((hcons.1 h).1.2.1 h0 h1)]
    · by_cases h1 : grp (G.hold1 M.np id) = g
      · rw [List.filterMap_cons_some (by rw [if_neg h0, if_pos h1]), wsum_script_cons, insSem]
        simp only [hr _, hof]
        by_cases he : uwBits (σ (G.hold1 M.np id, id)) = uwBits (b id)
        · rw [if_pos he, wsum_single, ih]
          refine if_congr ?_ rfl rfl
          rw [hcons]
          simp [EndOk, h0, h1, he]
        · rw [if_neg he, wsum_nil, if_neg fun h => he ((hcons.1 h).1.2.2 h0 h1)]
      · rw [List.filterMap_cons_none (by rw [if_neg h0, if_neg h1]), ih]
        refine if_congr ?_ rfl rfl
        rw [hcons]
        simp [EndOk, h0, h1]

theorem rep_nil : Rep ub key .nil (fun _ : Cell M U0 U1 => none) :=
  fun c => by rw [tget_nil]; rfl

/-- **GROUP computes the value of a group**: it guesses the contents of all cells of the group, and
with these every instruction is the table of its base party or of its role. -/
theorem wsum_script [Fintype Gr] (hkey : Function.Injective key) (hub : 0 < ub)
    (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q') (hx : ∀ κ, (x κ).length ≤ T)
    (hρ : ∀ s p, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2)
    (hkind : ∀ r, kinds[tg r]? = some ⟨M.kind r.1, r.2⟩)
    (htab : ∀ (r : M.R) i y h, ∃ e : WE, e.val θ = (M.kind r.1).tab r.2 i y h)
    (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    wsum (bindW
          (foldL (insG A ub) (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key tg b) .nil)
          (scriptSem (S := S) θ mu cb kinds T ub
            (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key tg b)))
        (fun _ => 1) =
      G.grpVal mu T cb P q x ρ n o grp g b := by
  classical
  -- the second pass: every instruction compares
  have h2 : ∀ t σ, Rep ub key t σ → (∀ c, c ∉ dom n o grp g → σ c = none) →
      wsum (scriptSem (S := S) θ mu cb kinds T ub
          (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key tg b) t) (fun _ => 1) =
      if GAgree (G.hold0 M.np) (G.hold1 M.np) grp g (P.cur n o E) b (fun a id => σ (a, id)) then
        ∏ a ∈ univ.filter (fun a => grp a = g),
          G.tabFinal mu T cb P q x ρ n o a fun id => σ (a, id)
      else 0 := by
    intro t σ hr hσ
    have e1 : (baseList grp g).map
          ((fun i => wsum (insSem θ mu cb kinds T ub i t) fun _ => 1) ∘
            baseIns (fun z => (qn Q z : ℕ)) cb q x ρ n key) =
        (baseList grp g).map fun p =>
          G.tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p
            fun id => σ (Fin.castAdd A' p, id) :=
      List.map_congr_left fun p _ => wsum_base hub hmu hx (fun s => hρ s p) hr
        fun a b k hk => hσ _ fun hc =>
          absurd (G.Plan.init_mem_seenAt.1 (mem_dom.1 hc).2.1) (not_lt.2 hk)
    have e2 : (roleList grp g M).map
          ((fun i => wsum (insSem (S := S) θ mu cb kinds T ub i t) fun _ => 1) ∘
            roleIns P n o key tg) =
        (roleList grp g M).map fun r => G.roleAt P n o r fun id => σ (M.rp r, id) :=
      List.map_congr_left fun r _ => wsum_roleIns hub (hkind r) (htab r) hr
        fun ν k hk => hσ _ fun hc =>
          absurd (G.Plan.new_mem_seenAt.1 (mem_dom.1 hc).2.1).2 (not_le.2 hk)
    rw [script, wsum_script_append, wsum_script_prod, endIns, wsum_end b _ t σ hr, List.map_append,
      List.prod_append, List.map_map, List.map_map, e1, e2, prod_tab, mul_ite, mul_one, mul_zero]
    refine if_congr ?_ rfl rfl
    have huw : ∀ v w : UW ub, uwBits v = uwBits w ↔ v = w := fun v w => (uwBits_injective hub).eq_iff
    simp only [List.mem_filter, G.allIds, Finset.mem_toList, mem_univ, true_and, decide_eq_true_eq, EndOk, huw]
    constructor
    · intro h
      exact ⟨fun id hid => (h id hid).1, fun id hid => (h id hid).2.1, fun id hid => (h id hid).2.2⟩
    · intro h id hid
      exact ⟨h.both id hid, h.fst id hid, h.snd id hid⟩
  -- the first pass: the contents of the cells of the group are guessed
  have hks := mem_gKeys_script (cb := cb) (P := P) (q := q) (x := x) (ρ := ρ) (n := n) (o := o)
    (grp := grp) (g := g) (key := key) (tg := tg) b
  have hkd : ∀ c,
      key c ∈ (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key tg b).flatMap gKeys ↔
        c ∈ dom n o grp g := fun c =>
    (hks _).trans ⟨fun ⟨c', hc', e⟩ => hkey e ▸ hc', fun hc => ⟨c, hc, rfl⟩⟩
  rw [wsum_bindW, wsum_foldL_flatMap (gK A ub) (insG A ub) gKeys (wsum_insG ub),
    wsum_gKs hkey hub _ (fun k hk => by obtain ⟨c, -, rfl⟩ := (hks k).1 hk; exact ⟨c, rfl⟩) .nil
      (fun _ => none) rep_nil
      fun t y hr hy => h2 t y hr fun c hc => hy.2 c fun hm => absurd ((hkd c).1 hm) hc,
    G.grpVal, groupVal]
  refine Eq.trans ?_ (Finset.sum_filter_of_ne
    (p := fun y : Fin (K + K + A') → G.Uid (K + K) U0 M.N U1 → UW ub =>
      ∀ a id, (a, id) ∈ dom n o grp g → y a id ≠ none) fun y _ hy a id hc => ?_)
  · refine Finset.sum_equiv (Equiv.curry (Fin (K + K + A')) (G.Uid (K + K) U0 M.N U1) (UW ub))
      (fun y => ?_) fun y _ => rfl
    rw [mem_filter, mem_filter, mem_gcontents_iff]
    constructor
    · rintro ⟨-, h1, h3⟩
      exact ⟨fun a id hc => h3 (a, id) fun hm => absurd (mem_dom.1 ((hkd _).1 hm)) hc,
        fun a id hc => h1 (a, id) ((hkd _).2 hc) rfl⟩
    · rintro ⟨h4, h5⟩
      exact ⟨mem_univ _, fun c hm _ => h5 c.1 c.2 ((hkd c).1 hm),
        fun c hc => h4 c.1 c.2 fun hd => hc ((hkd c).2 (mem_dom.2 hd)) rfl⟩
  · obtain ⟨h4, h5, h6⟩ := mem_dom.1 hc
    refine G.tabFinal_ne_none (mu := mu) (T := T) (cb := cb) (P := P) (q := q) (x := x) (ρ := ρ)
      (fun h0 => hy ?_) h5 h6
    have : ∏ a ∈ univ.filter (fun a => grp a = g), G.tabFinal mu T cb P q x ρ n o a (y a) = 0 :=
      Finset.prod_eq_zero (mem_filter.2 ⟨mem_univ a, h4⟩) h0
    rw [this, ite_self]

/-- The conditions on the instructions hold. -/
theorem insOk_script (hkind : ∀ r, kinds[tg r]? = some ⟨M.kind r.1, r.2⟩) (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    ∀ i ∈ script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key tg b, InsOk S Q c kinds i := by
  intro i hi
  rcases List.mem_append.1 hi with hi | hi
  · rcases List.mem_append.1 hi with hi | hi
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hi
      unfold baseIns
      induction p using Fin.addCases with
      | left κ =>
        rw [Fin.addCases_left]
        exact ⟨(qn Q _).2, (qn Q _).2⟩
      | right κ =>
        rw [Fin.addCases_right]
        intro a ha
        rw [List.mem_reverse] at ha
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 ha
        simp
    · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hi
      exact ⟨_, hkind r, by simp [slList]⟩
  · obtain ⟨id, -, h⟩ := List.mem_filterMap.1 hi
    split_ifs at h
    · simp only [Option.some.injEq] at h
      subst h
      trivial
    · simp only [Option.some.injEq] at h
      subst h
      trivial
    · simp only [Option.some.injEq] at h
      subst h
      trivial

end Nc.Grp
