/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Postpone

/-!
# Guessing the budgets and naming the powers of the constants
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R]

namespace KT

/-- The constants `c, c², c⁴, …` (`n` of them); the names are `0, 10, 110, …`. -/
def comb (c : R) : ℕ → KT R
  | 0 => none
  | n + 1 => node (leaf c) (comb (c ^ 2) n)

/-- The powers `c ^ (2 ^ b)`, `b < B`, of all constants. -/
def expand (B : ℕ) : KT R → KT R
  | none => none
  | leaf c => comb c B
  | node l r => node (l.expand B) (r.expand B)

/-- The power of `c` that has a given name. -/
def combVal (c : R) : List Bool → R
  | [] => 0
  | [false] => c
  | false :: _ :: _ => 0
  | true :: p => combVal (c ^ 2) p

/-- The constant with a given name: `l ++ 1^b ++ 0` names the power `2 ^ b` of the constant with the name `l`. -/
def lk : KT R → List Bool → R
  | none, _ => 0
  | leaf c, p => combVal c p
  | node _ _, [] => 0
  | node _ r, true :: p => r.lk p
  | node l _, false :: p => l.lk p

/-- The name of the power `2 ^ b`. -/
def pw (b : ℕ) : List Bool := List.replicate b true ++ [false]

/-- Names of powers `2 ^ b`, `b < B`, of the constants. -/
def InB (B : ℕ) : KT R → List Bool → Prop
  | none, _ => False
  | leaf _, p => ∃ b < B, p = pw b
  | node _ _, [] => False
  | node _ r, true :: p => r.InB B p
  | node l _, false :: p => l.InB B p

/-- Names of the constants. -/
def Leaf : KT R → List Bool → Prop
  | none, _ => False
  | leaf _, p => p = []
  | node _ _, [] => False
  | node _ r, true :: p => r.Leaf p
  | node l _, false :: p => l.Leaf p

theorem Leaf.inB {K : KT R} {p : List Bool} (h : K.Leaf p) {b B : ℕ} (hb : b < B) : K.InB B (p ++ pw b) := by
  induction K generalizing p with
  | none => exact h.elim
  | leaf c =>
    have h : p = [] := h
    subst h
    exact ⟨b, hb, rfl⟩
  | node l r ihl ihr =>
    cases p with
    | nil => exact h.elim
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

/-- A name of a power of a constant is not longer than the height of the trie plus `B`. -/
theorem InB.length_le {K : KT R} {B : ℕ} {p : List Bool} (h : K.InB B p) : p.length ≤ K.ht + B := by
  induction K generalizing p with
  | none => exact h.elim
  | leaf c =>
    obtain ⟨b, hb, rfl⟩ := h
    simp [pw, ht]
    omega
  | node l r ihl ihr =>
    cases p with
    | nil => exact h.elim
    | cons a p =>
      cases a with
      | true => have := ihr h; simp only [ht, List.length_cons]; omega
      | false => have := ihl h; simp only [ht, List.length_cons]; omega

theorem pw_succ (b : ℕ) : pw (b + 1) = true :: pw b := rfl

theorem combVal_pw (c : R) (b : ℕ) : combVal c (pw b) = c ^ 2 ^ b := by
  induction b generalizing c with
  | zero => simp [pw, combVal]
  | succ b ih => rw [pw_succ, combVal, ih, ← pow_mul, pow_succ' 2 b]

theorem Leaf.lk {K : KT R} {p : List Bool} (h : K.Leaf p) : ∃ c, ∀ i, K.lk (p ++ pw i) = c ^ 2 ^ i := by
  induction K generalizing p with
  | none => exact h.elim
  | leaf c =>
    have h : p = [] := h
    subst h
    exact ⟨c, fun i => combVal_pw c i⟩
  | node l r ihl ihr =>
    cases p with
    | nil => exact h.elim
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem lookup_comb (c : R) {B b : ℕ} (h : b < B) : (comb c B).lookup (pw b) = combVal c (pw b) := by
  induction b generalizing c B with
  | zero =>
    cases B with
    | zero => omega
    | succ B => rfl
  | succ b ih =>
    cases B with
    | zero => omega
    | succ B =>
      rw [pw_succ, comb, lookup, combVal]
      exact ih _ (by omega)

theorem lookup_expand {B : ℕ} {K : KT R} {p : List Bool} (h : K.InB B p) : K.lk p = (K.expand B).lookup p := by
  induction K generalizing p with
  | none => exact h.elim
  | leaf c =>
    obtain ⟨b, hb, rfl⟩ := h
    rw [expand, lookup_comb c hb, lk]
  | node l r ihl ihr =>
    cases p with
    | nil => exact h.elim
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem InB.mono {B B' : ℕ} (hB : B ≤ B') {K : KT R} {p : List Bool} (h : K.InB B p) : K.InB B' p := by
  induction K generalizing p with
  | none => exact h
  | leaf c =>
    obtain ⟨b, hb, rfl⟩ := h
    exact ⟨b, lt_of_lt_of_le hb hB, rfl⟩
  | node l r ihl ihr =>
    cases p with
    | nil => exact h
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem nds_comb (c : R) (n : ℕ) : (comb c n).nds = 2 * n + 1 := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [comb, nds, ih]; omega

theorem nds_pos (K : KT R) : 0 < K.nds := by cases K <;> simp [nds]

theorem nds_expand (B : ℕ) (K : KT R) : (K.expand B).nds ≤ K.nds * (2 * B + 1) := by
  induction K with
  | none => simp [expand, nds]
  | leaf c => simp [expand, nds, nds_comb]
  | node l r ihl ihr =>
    simp only [expand, nds]
    nlinarith

theorem ht_comb (c : R) (n : ℕ) : (comb c n).ht ≤ n := by
  induction n generalizing c with
  | zero => exact le_rfl
  | succ n ih =>
    have := ih (c ^ 2)
    simp only [comb, ht]
    omega

theorem ht_expand (B : ℕ) (K : KT R) : (K.expand B).ht ≤ K.ht + B := by
  induction K with
  | none => simp [expand, ht]
  | leaf c =>
    have := ht_comb c B
    simp only [expand, ht]
    omega
  | node l r ihl ihr =>
    simp only [expand, ht]
    omega

theorem length_words {J : ℕ} {w : List Bool} (h : w ∈ words J) : w.length = J := by
  induction J generalizing w with
  | zero => simp [words] at h; simp [h]
  | succ J ih =>
    simp only [words, List.mem_flatMap, List.mem_map] at h
    obtain ⟨b, -, v, hv, rfl⟩ := h
    simp [ih hv]

theorem ht_nds_budg {J : ℕ} {K : KT R} {q : Bt × R} (h : q ∈ K.budg J) :
    q.1.ht ≤ K.ht + J + 1 ∧ q.1.nds ≤ K.nds * (J + 1) := by
  induction K generalizing q with
  | none =>
    simp only [budg, List.mem_singleton] at h
    subst h
    simp [Bt.ht, Bt.nds, nds]
  | leaf c =>
    simp only [budg, List.mem_map] at h
    obtain ⟨w, hw, rfl⟩ := h
    simp [Bt.ht, Bt.nds, length_words hw, ht, nds]
  | node l r ihl ihr =>
    simp only [budg, List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hp, q', hq, rfl⟩ := h
    obtain ⟨h1, h1'⟩ := ihl hp
    obtain ⟨h2, h2'⟩ := ihr hq
    simp only [Bt.ht, Bt.nds, ht, nds]
    exact ⟨by omega, by nlinarith⟩

end KT

section Formulas

-- A run's determinant, the names it reads and the size of a tree: what the side conditions of
-- every `_ev` and `_rel` lemma below come down to.
attribute [local simp] Run.det names Tree.size

/-- Run `F` and `G`, whose values are pairs (data, tree of names); the value is (`E` of the two
data, the names of both). `E` reads the data at `.hd (.hd .id)` and `.hd (.tl .id)`. -/
def zipF (E F G : Fm) : Fm := lett (.cons F G) (.cons E (node (.tl (.hd .id)) (.tl (.tl .id))))

/-- Pair the data. -/
def pairE : Fm := .cons (.hd (.hd .id)) (.hd (.tl .id))

/-- Guess a bit; if it is 1, name the constant `p`. The value is (bit, tree of names). -/
def gbit (p : List Bool) : Fm :=
  .ite .guess (.cons (.quote one) (leaf (.quote (ofBits p)))) (.quote (.cons .nil .nil))

/-- Guess the digits of a number; name the powers of a constant. `ν i` is the exponent in the name
that is used for the power `2 ^ i`. -/
def gw (ν : ℕ → ℕ) (pre : List Bool) (b : ℕ) : ℕ → ℕ → Fm
  | _, 0 => .quote (.cons .nil .nil)
  | j, n + 1 => zipF pairE (gbit (pre ++ KT.pw (ν (b + j)))) (gw ν pre b (j + 1) n)

/-- The budgets of the powers of a constant. -/
def gcomb (ν : ℕ → ℕ) (J : ℕ) (pre : List Bool) : ℕ → ℕ → Fm
  | _, 0 => .quote (.cons .nil .nil)
  | b, n + 1 => zipF (.cons pairE (.quote .nil)) (zipF pairE (.quote (.cons .nil .nil))
      (gw ν pre b 0 J))
    (gcomb ν J pre (b + 1) n)

/-- The budgets of all powers `2 ^ b`, `b < B`, of all constants. -/
def gt (ν : ℕ → ℕ) (J B : ℕ) : KT R → List Bool → Fm
  | .none, _ => .quote (.cons .nil .nil)
  | .leaf _, pre => gcomb ν J pre 0 B
  | .node l r, pre => zipF (.cons pairE (.quote .nil)) (gt ν J B l (pre ++ [false])) (gt ν J B r
      (pre ++ [true]))

/-- A run whose value is (`o`, a tree of names) with weight 1; the constants named multiply to `v`,
the names satisfy `P`, and cost plus size are at most `c`. -/
def RelT (κ : List Bool → R) (P : List Bool → Prop) (c : ℕ) (r : Run A) (o : Tree) (v : R) : Prop :=
  r.th = 1 ∧ r.out.hd = o ∧ ((names r.out.tl).map κ).prod = v ∧ (∀ p ∈ names r.out.tl, P p) ∧
    r.cost + r.out.size ≤ c

/-- A run that guesses a budget and names the powers of the constants. -/
def RelG (κ : List Bool → R) (P : List Bool → Prop) (c : ℕ) (r : Run A) (q : Bt × R) : Prop :=
  RelT κ P c r q.1.enc q.2

variable {κ : List Bool → R} {P : List Bool → Prop} {ν : ℕ → ℕ}

/-- The two subtrees are no larger than the tree, plus 1 (for `nil`). -/
theorem size_hd_tl (t : Tree) : t.hd.size + t.tl.size ≤ t.size + 1 := by
  cases t with
  | nil => simp [hd, tl]
  | cons a b => simp only [hd, tl, Tree.size]; omega

/-- The runs of `zipF`: products of the runs of `F` and `G`. -/
theorem zip_rel {α β : Type*} {E F G : Fm} {x : Tree} {lf lg : List (Run A)}
    {Qf : List α} {Qg : List β}
    {of : α → Tree} {og : β → Tree} {vf : α → R} {vg : β → R} {cf cg k : ℕ} {e : Tree → Tree → Tree}
    (hf : Ev θ F x lf) (hg : Ev θ G x lg) (rf : List.Forall₂ (fun r a => RelT κ P cf r
        (of a) (vf a)) lf Qf)
    (rg : List.Forall₂ (fun r b => RelT κ P cg r (og b) (vg b)) lg Qg)
    (hE : ∀ a ∈ Qf, ∀ b ∈ Qg, ∀ u w, u.hd = of a → w.hd = og b → ∃ k' ≤ k, Dt θ E (.cons u w)
        (e (of a) (og b)) k')
    (hs : ∀ a ∈ Qf, ∀ b ∈ Qg, (e (of a) (og b)).size ≤ (of a).size + (og b).size + 3) :
    ∃ l, Ev θ (zipF E F G) x l ∧ List.Forall₂ (fun r (p : α × β) =>
      RelT κ P (cf + cg + k + 25) r (e (of p.1) (og p.2)) (vf p.1 * vg p.2)) l
        (Qf.flatMap fun a => Qg.map fun b => (a, b)) := by
  obtain ⟨l, e, r⟩ := lett_rel (body := .cons E (node (.tl (.hd .id))
      (.tl (.tl .id)))) (Ev.cons hf hg)
    (Q := Qf.flatMap fun a => Qg.map fun b => (a, b))
    (R := fun r (p : α × β) => p.1 ∈ Qf ∧ p.2 ∈ Qg ∧ ∃ s t, r = (s.seq t).tick (.cons s.out t.out) ∧
      RelT κ P cf s (of p.1) (vf p.1) ∧ RelT κ P cg t (og p.2) (vg p.2))
    (forall₂_flatMap rf fun s _ a hqa ha => by
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact (List.forall₂_iff_zip.2 ⟨rg.length_eq, fun {t b} htb =>
        ⟨hqa, (List.of_mem_zip htb).2, s, t, rfl, ha,
            (List.forall₂_iff_zip.1 rg).2 htb⟩⟩)) (Q2 := fun p => [p])
    (R2 := fun r (p : α × β) => RelT κ P (cf + cg + k + 25) r (e (of p.1) (og p.2))
        (vf p.1 * vg p.2)) (by
      rintro r - p - ⟨hpa, hpb, s, t, rfl, ⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4, b5⟩⟩
      obtain ⟨k', hk', d0⟩ := hE p.1 hpa p.2 hpb s.out t.out a2 b2
      have d := Dt.cons d0 (Dt.cons (Dt.cons (Dt.hd (Dt.id _)).tl (Dt.tl (Dt.id _)).tl)
        (Dt.quote .nil _))
      refine ⟨_, d, .cons ⟨?_, ?_, ?_, ?_, ?_⟩ .nil⟩
      · simp [Run.seq, Run.tick, a1, b1]
      · simp
      · simp [a3, b3]
      · simp only [Run.det, tl_cons, hd_cons, names, List.mem_append]
        exact fun p hp => hp.elim (a4 p) (b4 p)
      · have h1 := hs p.1 hpa p.2 hpb
        have e1 : (of p.1).size = s.out.hd.size := by rw [a2]
        have e2 : (og p.2).size = t.out.hd.size := by rw [b2]
        have h2 := size_hd_tl s.out
        have h3 := size_hd_tl t.out
        simp only [Run.det, Run.seq, Run.tick, Tree.size, hd_cons, tl_cons]
        omega)
  rw [flatMap_single, List.map_id'] at r
  exact ⟨l, e, r⟩

/-- `pairE` pairs the first parts of the two halves of its argument. -/
theorem pairE_dt (u w : Tree) : Dt θ pairE (.cons u w) (.cons u.hd w.hd) 7 :=
  Dt.cons (Dt.hd (Dt.hd (Dt.id _))) (Dt.hd (Dt.tl (Dt.id _)))

/-- The two runs of `gbit`: (0, no names) and (1, the name `p`). -/
theorem gbit_ev (p : List Bool) (x : Tree) : Ev θ (gbit p) x
    [.det 3 (.cons .nil .nil), .det 7 (.cons one (.cons (ofBits p) (.cons .nil .nil)))] := by
  have h1 := Dt.cons (θ := θ) (Dt.quote one x) (Dt.cons (Dt.quote (ofBits p) x)
      (Dt.quote (.cons .nil .nil) x))
  have := Ev.ite (L := fun r => if r.out = .nil then [.det 1 (.cons .nil .nil)] else
      [.det 5 (.cons one (.cons (ofBits p) (.cons .nil .nil)))]) (Ev.guess (θ := θ) x)
    (b := .cons (.quote one) (leaf (.quote (ofBits p)))) (c := .quote (.cons .nil .nil))
    (fun r _ h => by rw [if_neg h]; exact h1) (fun r _ h => by rw [if_pos h]; exact Ev.quote _ x)
  simpa [Run.seq, Run.tick, one, gbit] using this

theorem gw_ev {pre : List Bool} {b L : ℕ} {c : R} (x : Tree) {n j : ℕ}
    (h : ∀ i < j + n, κ (pre ++ KT.pw (ν (b + i))) = c ^ 2 ^ (b + i) ∧
      P (pre ++ KT.pw (ν (b + i))) ∧ (pre ++ KT.pw (ν (b + i))).length ≤ L) :
    ∃ l, Ev θ (gw ν pre b j n) x l ∧
      List.Forall₂ (fun r w => RelT κ P ((4 * L + 48) * n + 4) r (ofBits w)
        ((c ^ 2 ^ (b + j)) ^ KT.val w)) l (KT.words n) := by
  induction n generalizing j with
  | zero => exact ⟨_, .quote _ x, .cons ⟨rfl, rfl, by simp [KT.val],
      by simp,
      by simp⟩ .nil⟩
  | succ n ih =>
    obtain ⟨l, e, hl⟩ := ih (j := j + 1) (fun i hi => h i (by omega))
    obtain ⟨hκ, hP, hL⟩ := h j (by omega)
    have hb : List.Forall₂ (fun r (a : Bool) => RelT κ P (4 * L + 16) r (bit a)
        (if a then c ^ 2 ^ (b + j) else 1))
        [(.det 3 (.cons .nil .nil) : Run A), .det 7
            (.cons one (.cons (ofBits (pre ++ KT.pw (ν (b + j)))) (.cons .nil .nil)))]
        [false, true] := by
      have := size_ofBits (pre ++ KT.pw (ν (b + j)))
      refine .cons ⟨rfl, rfl, by simp, by simp,
          by simp⟩
        (.cons ⟨rfl, rfl, ?_, ?_, ?_⟩ .nil)
      · simp only [Run.det, tl_cons, names, path_ofBits, List.map_cons,
          List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, hκ, if_true]
      · simpa [path_ofBits] using hP
      · simp only [Run.det, Tree.size, one]
        omega
    obtain ⟨l', e', r'⟩ := zip_rel (gbit_ev _ x) e hb hl
      (fun _ _ _ _ u w hu hw => ⟨_, le_rfl, hu ▸ hw ▸ pairE_dt u w⟩)
      fun _ _ _ _ => by simp
    refine ⟨l', e', ?_⟩
    have ew : KT.words (n + 1) = ([false, true].flatMap fun a => (KT.words n).map
        fun w => (a, w)).map
        fun p => p.1 :: p.2 := by simp [KT.words, Function.comp_def]
    rw [ew, List.forall₂_map_right_iff]
    refine r'.imp fun r p hr =>
      ⟨hr.1, by simpa [ofBits] using hr.2.1, ?_, hr.2.2.2.1, by nlinarith [hr.2.2.2.2]⟩
    rw [hr.2.2.1]
    rcases p with ⟨_ | _, w⟩ <;> simp [KT.val, pow_add, pow_mul]

theorem gcomb_ev {J L : ℕ} {pre : List Bool} {c : R} (x : Tree) {n b : ℕ}
    (h : ∀ i < b + n + J, κ (pre ++ KT.pw (ν i)) = c ^ 2 ^ i ∧ P (pre ++ KT.pw (ν i)) ∧
      (pre ++ KT.pw (ν i)).length ≤ L) :
    ∃ l, Ev θ (gcomb ν J pre b n) x l ∧
      List.Forall₂ (RelG κ P (((4 * L + 48) * J + 80) * n + 4)) l
        ((KT.comb (c ^ 2 ^ b) n).budg J) := by
  induction n generalizing b with
  | zero =>
    exact ⟨_, .quote _ x, .cons ⟨rfl, rfl, by simp, by simp,
      by simp⟩ .nil⟩
  | succ n ih =>
    obtain ⟨lg, eg, rg⟩ := ih (b := b + 1) (fun i hi => h i (by omega))
    obtain ⟨lw, ew, rw'⟩ := gw_ev (θ := θ) (κ := κ) (P := P) (ν := ν) (pre := pre) (b := b) (c := c) x (n := J) (j := 0)
      (fun i hi => h (b + i) (by omega))
    have r0 : List.Forall₂ (fun r (_ : Unit) => RelT κ P 4 r .nil 1)
        [(.det 1 (.cons .nil .nil) : Run A)] [()] :=
      .cons ⟨rfl, rfl, by simp, by simp,
        by simp⟩ .nil
    obtain ⟨lf, ef, rf⟩ := zip_rel (.quote _ x) ew r0 rw' (fun _ _ _ _ u w hu hw => ⟨_, le_rfl,
        hu ▸ hw ▸ pairE_dt u w⟩) fun _ _ _ _ => by simp
    obtain ⟨l, e, r⟩ := zip_rel (e := fun a b => .cons (.cons a b) .nil) ef eg rf (rg.imp
        fun _ _ h => h) (fun _ _ _ _ u w hu hw => ⟨_, le_rfl,
        hu ▸ hw ▸ (pairE_dt u w).cons (Dt.quote .nil _)⟩)
      fun _ _ _ _ => by simp
    refine ⟨l, e, ?_⟩
    have hc : (c ^ 2 ^ b) ^ 2 = c ^ 2 ^ (b + 1) := by rw [← pow_mul, ← pow_succ]
    have eL : (KT.comb (c ^ 2 ^ b) (n + 1)).budg J = (((KT.words J).map
        fun a => ((), a)).flatMap fun a =>
        ((KT.comb (c ^ 2 ^ (b + 1)) n).budg J).map fun q => (a, q)).map
          fun p => (Bt.node (.leaf p.1.2) p.2.1, (c ^ 2 ^ b) ^ KT.val p.1.2 * p.2.2) := by
      simp [KT.comb, KT.budg, hc, List.map_flatMap, List.flatMap_map, Function.comp_def]
    rw [eL, List.forall₂_map_right_iff]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at r
    refine r.imp fun s p hs => ⟨hs.1, hs.2.1, by simpa using hs.2.2.1, hs.2.2.2.1, ?_⟩
    have := hs.2.2.2.2
    nlinarith

/-- Runs of `gt` = budgets. The hypothesis: the names that are used name the right powers, and are
not longer than `L`. -/
theorem gt_ev {J B L : ℕ} (x : Tree) (K : KT R) (pre : List Bool)
    (h : ∀ p, K.Leaf p → ∀ i < B + J, κ (pre ++ (p ++ KT.pw (ν i))) = K.lk (p ++ KT.pw i) ∧
      P (pre ++ (p ++ KT.pw (ν i))) ∧ (pre ++ (p ++ KT.pw (ν i))).length ≤ L) :
    ∃ l, Ev θ (gt ν J B K pre) x l ∧
      List.Forall₂ (RelG κ P (((4 * L + 48) * J + 80) * (K.expand B).nds)) l
          ((K.expand B).budg J) := by
  induction K generalizing pre with
  | none =>
    refine ⟨_, .quote _ x, .cons ⟨rfl, rfl, by simp, by simp,
      ?_⟩ .nil⟩
    simp only [Run.det, Tree.size, KT.expand, KT.nds]
    omega
  | leaf c =>
    have h' : ∀ i < B + J, κ (pre ++ KT.pw (ν i)) = c ^ 2 ^ i ∧ P (pre ++ KT.pw (ν i)) ∧
        (pre ++ KT.pw (ν i)).length ≤ L := by
      intro i hi
      have := h [] rfl i hi
      simpa [KT.lk, KT.combVal_pw] using this
    obtain ⟨l, e, r⟩ := gcomb_ev (θ := θ) (J := J) (pre := pre) (c := c) x (n := B) (b := 0)
      (fun i hi => h' i (by omega))
    refine ⟨l, e, ?_⟩
    simp only [pow_zero, pow_one] at r
    refine r.imp fun s q hs => ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.trans ?_⟩
    simp only [KT.expand, KT.nds_comb]
    have hC : 80 ≤ (4 * L + 48) * J + 80 := Nat.le_add_left _ _
    nlinarith
  | node l r ihl ihr =>
    obtain ⟨ll, el, rl⟩ := ihl (pre ++ [false]) (fun p hp i hi => by
      have := h (false :: p) hp i hi
      simpa [KT.lk] using this)
    obtain ⟨lr, er, rr⟩ := ihr (pre ++ [true]) (fun p hp i hi => by
      have := h (true :: p) hp i hi
      simpa [KT.lk] using this)
    obtain ⟨l', e', r'⟩ := zip_rel (e := fun a b => .cons (.cons a b) .nil) el er rl rr
      (fun _ _ _ _ u w hu hw => ⟨_, le_rfl, hu ▸ hw ▸ (pairE_dt u w).cons
          (Dt.quote .nil _)⟩) fun _ _ _ _ => by simp
    refine ⟨l', e', ?_⟩
    have eL : ((KT.node l r).expand B).budg J = (((l.expand B).budg J).flatMap fun a =>
        ((r.expand B).budg J).map fun b => (a, b)).map
          fun p => (Bt.node p.1.1 p.2.1, p.1.2 * p.2.2) := by
      simp [KT.expand, KT.budg, List.map_flatMap, Function.comp_def]
    rw [eL, List.forall₂_map_right_iff]
    refine r'.imp fun s p hs => ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.trans ?_⟩
    have hC : 80 ≤ (4 * L + 48) * J + 80 := Nat.le_add_left _ _
    simp only [KT.expand, KT.nds]
    nlinarith

end Formulas

section Sizes

theorem size_num (k : ℕ) : (num k).size = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [num, Tree.size, ih]; omega

theorem size_gw (ν : ℕ → ℕ) (pre : List Bool) (b N : ℕ) (n j : ℕ) (h : ∀ i < j + n, ν (b + i) ≤ N) :
    (gw ν pre b j n).code.size ≤ n * (4 * (pre.length + N) + 400) + 5 := by
  induction n generalizing j with
  | zero => simp [gw, Fm.code, Tree.size, size_num]
  | succ n ih =>
    have h1 := ih (j + 1) (fun i hi => h i (by omega))
    have h2 := size_ofBits (pre ++ KT.pw (ν (b + j)))
    have h3 := h j (by omega)
    simp only [KT.pw, List.length_append, List.length_replicate, List.length_singleton] at h2
    simp only [gw, gbit, zipF, lett, pairE, leaf, node, one, Fm.code, Tree.size, size_num, KT.pw]
    nlinarith

theorem size_gcomb (ν : ℕ → ℕ) (J : ℕ) (pre : List Bool) (N : ℕ) (n b : ℕ) (h : ∀ i < b + n + J, ν i ≤ N) :
    (gcomb ν J pre b n).code.size ≤ n * ((J + 1) * (4 * (pre.length + N) + 400)) + 5 := by
  induction n generalizing b with
  | zero => simp [gcomb, Fm.code, Tree.size, size_num]
  | succ n ih =>
    have h1 := ih (b + 1) (fun i hi => h i (by omega))
    have h2 := size_gw ν pre b N J 0 (fun i hi => h _ (by omega))
    simp only [gcomb, zipF, lett, pairE, node, Fm.code, Tree.size, size_num]
    nlinarith

theorem size_gt (ν : ℕ → ℕ) (J B : ℕ) (K : KT R) (pre : List Bool) (N : ℕ) (h : ∀ i < B + J, ν i ≤ N) :
    (gt ν J B K pre).code.size ≤
      (K.expand B).nds * ((J + 1) * (4 * (pre.length + K.ht + N) + 400)) := by
  induction K generalizing pre with
  | none =>
    simp only [gt, Fm.code, Tree.size, size_num, KT.expand, KT.nds, KT.ht]
    nlinarith
  | leaf c =>
    have h1 := size_gcomb ν J pre N B 0 (fun i hi => h i (by omega))
    simp only [gt, KT.expand, KT.nds_comb, KT.ht, add_zero] at h1 ⊢
    refine h1.trans ?_
    have : 400 ≤ (J + 1) * (4 * (pre.length + N) + 400) := by nlinarith
    nlinarith
  | node l r ihl ihr =>
    have h1 := ihl (pre ++ [false])
    have h2 := ihr (pre ++ [true])
    simp only [List.length_append, List.length_singleton] at h1 h2
    simp only [gt, zipF, lett, pairE, node, Fm.code, Tree.size, size_num, KT.expand, KT.nds, KT.ht]
    have e1 : (J + 1) * (4 * (pre.length + 1 + l.ht + N) + 400) ≤
        (J + 1) * (4 * (pre.length + (max l.ht r.ht + 1) + N) + 400) := by
      apply Nat.mul_le_mul_left
      have := le_max_left l.ht r.ht
      omega
    have e2 : (J + 1) * (4 * (pre.length + 1 + r.ht + N) + 400) ≤
        (J + 1) * (4 * (pre.length + (max l.ht r.ht + 1) + N) + 400) := by
      apply Nat.mul_le_mul_left
      have := le_max_right l.ht r.ht
      omega
    nlinarith

end Sizes

end NS1
