/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Tableau.Basic
import Mathlib.Combinatorics.Young.RobinsonSchensted.Insertion

/-!
# The Robinson–Schensted insertion tableau

A Lean 4 port of the tableau part of `theories/LRrule/Schensted.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

A letter is inserted in a tableau by inserting it in the first row; the entry it bumps
out, if any, is then inserted in the next row, and so on.  Inserting all the letters of
a word `w` from left to right produces the insertion tableau `RS w`, whose first row is
the Schensted row `List.schensted w`.

## Main definitions

* `List.bumped r l` : the entry of the row `r` bumped out by the insertion of `l`
  (Coq `bumped`).
* `List.insTab t l` : insertion of the letter `l` in the tableau `t` (Coq `instab`).
* `List.RS w` : the insertion tableau of the word `w` (Coq `RS`).

## Main results

* `List.isTableau_insTab` : inserting a letter in a tableau yields a tableau
  (Coq `is_tableau_instab`).
* `List.isTableau_RS` : `List.RS w` is a tableau (Coq `is_tableau_RS`).
* `List.headD_RS` : the first row of `List.RS w` is `List.schensted w` (Coq `Sch_RS`).
* `List.sizeTab_RS` : `List.RS w` has one box per letter of `w` (Coq `size_RS`).
* `List.RS_first_row_isGreatest` : the length of the first row of `List.RS w` is the
  maximal length of a nondecreasing subsequence of `w`.
-/

namespace List

open List

variable {T : Type*} [LinearOrder T]

/-! ### The bumped letter -/

/-- The entry of the row `r` which is bumped out by the insertion of the letter `l`;
`none` if `l` is appended at the end of the row (Coq `bumped`). -/
def bumped (r : List T) (l : T) : Option T := r[insPos r l]?

lemma bumped_eq_none_iff {r : List T} {l : T} :
    bumped r l = none ↔ insPos r l = r.length := by
  rw [bumped, List.getElem?_eq_none_iff]
  exact ⟨fun h => le_antisymm (insPos_le_length r l) h, fun h => h.ge⟩

lemma insPos_lt_length_of_bumped {r : List T} {l b : T} (h : bumped r l = some b) :
    insPos r l < r.length := (List.getElem?_eq_some_iff.1 h).1

lemma lt_of_bumped {r : List T} {l b : T} (h : bumped r l = some b) : l < b :=
  lt_of_getElem?_insPos h

lemma insRow_length_of_bumped {r : List T} {l b : T} (h : bumped r l = some b) :
    (insRow r l).length = r.length := by
  rw [insRow_length]
  have := insPos_lt_length_of_bumped h
  omega

lemma insRow_length_of_bumped_none {r : List T} {l : T} (h : bumped r l = none) :
    (insRow r l).length = r.length + 1 := by
  rw [insRow_length, bumped_eq_none_iff.1 h]
  omega

/-! ### Insertion in a tableau -/

/-- Insertion of the letter `l` in the tableau `t`: `l` is inserted in the first row and
the bumped entry, if any, is inserted in the next row (Coq `instab`). -/
def insTab : List (List T) → T → List (List T)
  | [], l => [[l]]
  | t0 :: t, l =>
    match bumped t0 l with
    | none => insRow t0 l :: t
    | some b => insRow t0 l :: insTab t b

@[simp] lemma insTab_nil (l : T) : insTab ([] : List (List T)) l = [[l]] := rfl

lemma insTab_cons_of_bumped_none {t0 : List T} {t : List (List T)} {l : T}
    (h : bumped t0 l = none) : insTab (t0 :: t) l = insRow t0 l :: t := by
  rw [insTab, h]

lemma insTab_cons_of_bumped_some {t0 : List T} {t : List (List T)} {l b : T}
    (h : bumped t0 l = some b) : insTab (t0 :: t) l = insRow t0 l :: insTab t b := by
  rw [insTab, h]

/-- The first row of `insTab t l` is obtained by inserting `l` in the first row of `t`. -/
lemma headD_insTab (t : List (List T)) (l : T) :
    (insTab t l).headD [] = insRow (t.headD []) l := by
  cases t with
  | nil => rfl
  | cons t0 t =>
    cases h : bumped t0 l with
    | none => rw [insTab_cons_of_bumped_none h]; rfl
    | some b => rw [insTab_cons_of_bumped_some h]; rfl

lemma insTab_ne_nil (t : List (List T)) (l : T) : insTab t l ≠ [] := by
  cases t with
  | nil => simp
  | cons t0 t =>
    cases h : bumped t0 l with
    | none => rw [insTab_cons_of_bumped_none h]; simp
    | some b => rw [insTab_cons_of_bumped_some h]; simp

/-! ### Entries after row insertion -/

lemma insRow_getElem_eq {r : List T} {l : T} {k : ℕ} (hk : k < r.length)
    (hne : k ≠ insPos r l) (hk' : k < (insRow r l).length) : (insRow r l)[k] = r[k] := by
  have h := insRow_getElem?_of_ne (r := r) (l := l) hne
  rw [List.getElem?_eq_getElem hk', List.getElem?_eq_getElem hk, Option.some.injEq] at h
  exact h

lemma insRow_getElem_insPos_eq (r : List T) (l : T) :
    (insRow r l)[insPos r l]'(insPos_lt_insRow_length r l) = l := by
  have h := insRow_getElem?_insPos r l
  rw [List.getElem?_eq_getElem (insPos_lt_insRow_length r l), Option.some.injEq] at h
  exact h

lemma insRow_getElem_eq_of_eq_insPos {r : List T} {l : T} {k : ℕ} (hk : k = insPos r l)
    (hk' : k < (insRow r l).length) : (insRow r l)[k] = l := by
  subst hk
  exact insRow_getElem_insPos_eq r l

lemma bumped_eq_getElem {r : List T} {l b : T} (h : bumped r l = some b) :
    b = r[insPos r l]'(insPos_lt_length_of_bumped h) := by
  have h2 := List.getElem?_eq_getElem (insPos_lt_length_of_bumped h)
  rw [bumped, h2, Option.some.injEq] at h
  exact h.symm

/-! ### Domination after insertion -/

/-- The insertion position of a bumped letter in the row above is at most the position it
was bumped from. -/
lemma insPos_le_of_dominate {u r : List T} {l b : T} (hdom : Dominate u r)
    (hb : bumped r l = some b) : insPos u b ≤ insPos r l := by
  by_contra hcon
  push_neg at hcon
  have hp : insPos r l < u.length := lt_of_lt_of_le hcon (insPos_le_length u b)
  have hulb : u[insPos r l]? = some (u[insPos r l]'hp) := List.getElem?_eq_getElem hp
  have h1 : u[insPos r l]'hp ≤ b := le_of_lt_insPos hcon hulb
  have h2 : r[insPos r l]'(lt_of_lt_of_le hp hdom.length_le) < u[insPos r l]'hp :=
    hdom.getElem_lt _ hp
  have hbr : b = r[insPos r l]'(lt_of_lt_of_le hp hdom.length_le) := by
    have := List.getElem?_eq_getElem (lt_of_lt_of_le hp hdom.length_le)
    rw [bumped, this, Option.some.injEq] at hb
    exact hb.symm
  rw [hbr] at h1
  exact absurd (lt_of_lt_of_le h2 h1) (lt_irrefl _)

/-- Key domination lemma (Coq `dominate_instab`): if the row `u` dominates the row `r`,
then after inserting `l` in `r` and the bumped letter in `u`, domination still holds. -/
lemma dominate_insRow_of_bumped {u r : List T} {l b : T} (hdom : Dominate u r)
    (hb : bumped r l = some b) : Dominate (insRow u b) (insRow r l) := by
  have hplen : insPos r l < r.length := insPos_lt_length_of_bumped hb
  have hbr : b = r[insPos r l]'hplen := bumped_eq_getElem hb
  have hqp : insPos u b ≤ insPos r l := insPos_le_of_dominate hdom hb
  have hulen : u.length ≤ r.length := hdom.length_le
  have hlen : (insRow u b).length ≤ (insRow r l).length := by
    rw [insRow_length, insRow_length]; omega
  refine dominate_of_getElem hlen ?_
  intro i hi
  have hi' : i < (insRow r l).length := lt_of_lt_of_le hi hlen
  have hqu : insPos u b ≤ u.length := insPos_le_length u b
  have hiu : i < u.length ∨ i = insPos u b := by
    rcases lt_or_ge i u.length with h | h
    · exact Or.inl h
    · rw [insRow_length, lt_max_iff] at hi
      rcases hi with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by omega)
  by_cases hiq : i = insPos u b
  · subst hiq
    rw [insRow_getElem_insPos_eq u b]
    rcases eq_or_lt_of_le hqp with heq | hlt
    · rw [insRow_getElem_eq_of_eq_insPos heq hi']
      exact lt_of_bumped hb
    · have hir : insPos u b < r.length := lt_trans hlt hplen
      rw [insRow_getElem_eq hir (by omega) hi']
      have h1 : r[insPos u b]'hir ≤ l :=
        le_of_lt_insPos hlt (List.getElem?_eq_getElem hir)
      exact lt_of_le_of_lt h1 (lt_of_bumped hb)
  · have hiu' : i < u.length := hiu.resolve_right hiq
    rw [insRow_getElem_eq hiu' hiq hi]
    by_cases hip : i = insPos r l
    · have hir : i < r.length := lt_of_lt_of_le hiu' hulen
      have hbi : b = r[i] := by
        have h1 : r[i]? = some b := by rw [hip]; exact hb
        rw [List.getElem?_eq_getElem hir, Option.some.injEq] at h1
        exact h1.symm
      rw [insRow_getElem_eq_of_eq_insPos hip hi']
      calc l < b := lt_of_bumped hb
        _ = r[i] := hbi
        _ < u[i] := hdom.getElem_lt i hiu'
    · have hir : i < r.length := lt_of_lt_of_le hiu' hulen
      rw [insRow_getElem_eq hir hip hi']
      exact hdom.getElem_lt i hiu'

/-- If nothing is bumped out of `r`, the row above still dominates the enlarged row. -/
lemma dominate_insRow_of_bumped_none {u r : List T} {l : T} (hdom : Dominate u r)
    (hb : bumped r l = none) : Dominate u (insRow r l) := by
  have hp : insPos r l = r.length := bumped_eq_none_iff.1 hb
  have hulen : u.length ≤ r.length := hdom.length_le
  refine dominate_of_getElem (le_trans hulen (length_le_insRow_length r l)) ?_
  intro i hi
  have hir : i < r.length := lt_of_lt_of_le hi hulen
  rw [insRow_getElem_eq hir (by omega) (lt_of_lt_of_le hir (length_le_insRow_length r l))]
  exact hdom.getElem_lt i hi

/-! ### Insertion produces a tableau -/

lemma isRow_insRow {r : List T} (hr : IsRow r) (l : T) : IsRow (insRow r l) := by
  rw [IsRow, List.isChain_iff_pairwise] at hr ⊢
  exact insRow_pairwise_le hr l

/-- Coq `is_tableau_instab`. -/
lemma isTableau_insTab {t : List (List T)} (h : IsTableau t) (l : T) :
    IsTableau (insTab t l) := by
  induction t generalizing l with
  | nil =>
    refine ⟨by simp, ?_, by simp, by simp⟩
    simp [IsRow]
  | cons t0 t ih =>
    obtain ⟨hne, hrow, hdom, htab⟩ := h
    have hne' : insRow t0 l ≠ [] := by
      intro hcon
      have := length_le_insRow_length t0 l
      rw [hcon] at this
      simp only [List.length_nil, Nat.le_zero] at this
      exact hne (List.length_eq_zero_iff.1 this)
    cases hb : bumped t0 l with
    | none =>
      rw [insTab_cons_of_bumped_none hb]
      exact ⟨hne', isRow_insRow hrow l, dominate_insRow_of_bumped_none hdom hb, htab⟩
    | some b =>
      rw [insTab_cons_of_bumped_some hb]
      refine ⟨hne', isRow_insRow hrow l, ?_, ih htab b⟩
      rw [headD_insTab]
      exact dominate_insRow_of_bumped hdom hb

/-! ### The insertion tableau of a word -/

/-- The insertion tableau of the word `w` (Coq `RS`). -/
def RS (w : List T) : List (List T) := w.foldl insTab []

@[simp] lemma RS_nil : RS ([] : List T) = [] := rfl

lemma RS_concat (w : List T) (l : T) : RS (w ++ [l]) = insTab (RS w) l := by
  simp [RS]

/-- Coq `is_tableau_RS`. -/
theorem isTableau_RS (w : List T) : IsTableau (RS w) := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w l ih => rw [RS_concat]; exact isTableau_insTab ih l

/-- Coq `Sch_RS`: the first row of the insertion tableau is the Schensted row. -/
theorem headD_RS (w : List T) : (RS w).headD [] = schensted w := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w l ih =>
    rw [RS_concat, headD_insTab, ih, schensted_concat]

lemma sizeTab_insTab (t : List (List T)) (l : T) : sizeTab (insTab t l) = sizeTab t + 1 := by
  induction t generalizing l with
  | nil => simp [sizeTab]
  | cons t0 t ih =>
    cases h : bumped t0 l with
    | none =>
      rw [insTab_cons_of_bumped_none h]
      simp only [sizeTab, shape_cons, List.sum_cons, insRow_length_of_bumped_none h]
      omega
    | some b =>
      rw [insTab_cons_of_bumped_some h]
      simp only [sizeTab, shape_cons, List.sum_cons, insRow_length_of_bumped h]
      have := ih (l := b)
      simp only [sizeTab] at this
      omega

/-- Coq `size_RS`: the insertion tableau of `w` has one box per letter of `w`. -/
theorem sizeTab_RS (w : List T) : sizeTab (RS w) = w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [sizeTab]
  | append_singleton w l ih => rw [RS_concat, sizeTab_insTab, ih]; simp

/-- The length of the first row of the insertion tableau of `w` is the maximal length of
a nondecreasing subsequence of `w`. -/
theorem RS_first_row_isGreatest (w : List T) :
    IsGreatest {n : ℕ | ∃ s : List T, s.Sublist w ∧ s.Pairwise (· ≤ ·) ∧ s.length = n}
      ((RS w).headD []).length := by
  rw [headD_RS]
  exact schensted_isGreatest w

/-! ### The letters of the insertion tableau -/

lemma bumped_cons (x : T) (r : List T) (l : T) :
    bumped (x :: r) l = if l < x then some x else bumped r l := by
  rw [bumped, insPos_cons]
  split
  · simp
  · simp [bumped]

/-- Row insertion permutes the letters: the bumped letter together with the new row is a
permutation of the inserted letter together with the old row. -/
lemma perm_insRow (r : List T) (l : T) :
    ((bumped r l).toList ++ insRow r l).Perm (l :: r) := by
  induction r with
  | nil => simp [bumped]
  | cons x r ih =>
    rw [bumped_cons, insRow_cons]
    split
    · simpa using List.Perm.swap l x r
    · cases hb : bumped r l with
      | none =>
        rw [hb] at ih
        simp only [Option.toList_none, List.nil_append] at ih ⊢
        exact (ih.cons x).trans (List.Perm.swap l x r)
      | some b =>
        rw [hb] at ih
        simp only [Option.toList_some, List.cons_append] at ih ⊢
        refine ((List.Perm.swap x b (insRow r l)).trans ?_)
        exact (ih.cons x).trans (List.Perm.swap l x r)

/-- Inserting a letter in a tableau permutes the letters of its reading word. -/
lemma perm_toWord_insTab (t : List (List T)) (l : T) :
    (toWord (insTab t l)).Perm (l :: toWord t) := by
  induction t generalizing l with
  | nil => simp [toWord]
  | cons t0 t ih =>
    cases hb : bumped t0 l with
    | none =>
      rw [insTab_cons_of_bumped_none hb, toWord_cons, toWord_cons]
      have h := perm_insRow t0 l
      rw [hb] at h
      simp only [Option.toList_none, List.nil_append] at h
      calc (toWord t ++ insRow t0 l).Perm (toWord t ++ (l :: t0)) := h.append_left _
        _ ~ (l :: (toWord t ++ t0)) := List.perm_middle
    | some b =>
      rw [insTab_cons_of_bumped_some hb, toWord_cons, toWord_cons]
      have h := perm_insRow t0 l
      rw [hb] at h
      simp only [Option.toList_some, List.cons_append] at h
      calc (toWord (insTab t b) ++ insRow t0 l).Perm ((b :: toWord t) ++ insRow t0 l) :=
            (ih b).append_right _
        _ ~ (toWord t ++ (b :: insRow t0 l)) := List.perm_middle.symm
        _ ~ (toWord t ++ (l :: t0)) := h.append_left _
        _ ~ (l :: (toWord t ++ t0)) := List.perm_middle

/-- Coq `perm_eq_RS`: the reading word of the insertion tableau of `w` is a permutation
of `w`. -/
theorem perm_toWord_RS (w : List T) : (toWord (RS w)).Perm w := by
  induction w using List.reverseRecOn with
  | nil => simp [toWord]
  | append_singleton w l ih =>
    rw [RS_concat]
    calc (toWord (insTab (RS w) l)).Perm (l :: toWord (RS w)) := perm_toWord_insTab _ l
      _ ~ (l :: w) := ih.cons l
      _ ~ (w ++ [l]) := (List.perm_append_singleton l w).symm

end List
