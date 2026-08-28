/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Shape.Included
import Mathlib.Combinatorics.Young.Tableau.Basic

/-!
# Skew tableaux

A Lean 4 port of the basic part of `theories/Combi/skewtab.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

A skew tableau of shape `outer / inner` is stored as the list of the *filled* parts of its
rows: row `i` is a list of length `outer i - inner i`, whose entries occupy the columns
`inner i, …, outer i - 1`.  Rows are weakly increasing and, on the columns where two
consecutive rows overlap, the entries increase strictly downwards.  Since row `i + 1`
starts `inner i - inner (i + 1)` columns to the left of row `i`, this last condition is
domination after dropping that many entries.

## Main definitions

* `List.SkewDominate d u v` : `u` dominates `v` after dropping its first `d` entries
  (Coq `skew_dominate`).
* `List.IsSkewTableau inner t` : `t` is a skew tableau with inner shape `inner`
  (Coq `is_skew_tableau`).
* `List.addShape` : pointwise sum of two shapes, used to build the outer shape
  `List.outerShape inner t` of a skew tableau.

## Main results

* `List.isSkewTableau_nil_iff_isTableau` : skew tableaux with an empty inner shape are
  exactly the tableaux.
* `List.isPart_outerShape` : the outer shape of a skew tableau is a partition.
* `List.included_outerShape` and `List.diffShape_outerShape` : the inner shape is
  included in the outer shape, and the skew shape between them is the shape of the rows.
-/

namespace List

open List

variable {T : Type*} [LinearOrder T]

/-! ### Skew domination -/

/-- `SkewDominate d u v` holds when the row `u`, shifted `d` columns to the left of `v`,
dominates `v` on the columns where they overlap (Coq `skew_dominate`). -/
def SkewDominate (d : ℕ) (u v : List T) : Prop := Dominate (u.drop d) v

@[simp] lemma skewDominate_zero (u v : List T) : SkewDominate 0 u v ↔ Dominate u v := by
  rw [SkewDominate, List.drop_zero]

lemma SkewDominate.length_le {d : ℕ} {u v : List T} (h : SkewDominate d u v) :
    u.length - d ≤ v.length := by
  have := (Dominate.length_le h)
  rwa [List.length_drop] at this

/-! ### Skew tableaux -/

/-- `IsSkewTableau inner t` states that `t` is a skew tableau with inner shape `inner`:
its rows are weakly increasing and nonempty as rows of the skew shape, and consecutive
rows dominate each other on their common columns (Coq `is_skew_tableau`). -/
def IsSkewTableau : List ℕ → List (List T) → Prop
  | _, [] => True
  | inner, t0 :: t =>
      inner.headD 0 + t0.length ≠ 0 ∧ IsRow t0 ∧
        SkewDominate (inner.headD 0 - inner.tail.headD 0) (t.headD []) t0 ∧
        IsSkewTableau inner.tail t

@[simp] lemma isSkewTableau_nil (inner : List ℕ) :
    IsSkewTableau inner ([] : List (List T)) := trivial

@[simp] lemma isSkewTableau_cons {inner : List ℕ} {t0 : List T} {t : List (List T)} :
    IsSkewTableau inner (t0 :: t) ↔
      inner.headD 0 + t0.length ≠ 0 ∧ IsRow t0 ∧
        SkewDominate (inner.headD 0 - inner.tail.headD 0) (t.headD []) t0 ∧
        IsSkewTableau inner.tail t := Iff.rfl

/-- Skew tableaux with an empty inner shape are exactly the tableaux. -/
theorem isSkewTableau_nil_iff_isTableau {t : List (List T)} :
    IsSkewTableau ([] : List ℕ) t ↔ IsTableau t := by
  induction t with
  | nil => simp
  | cons t0 t ih =>
    rw [isSkewTableau_cons, isTableau_cons, ← ih]
    simp

/-! ### The outer shape -/

/-- Pointwise sum of two shapes, the shorter one being padded with zeroes. -/
def addShape : List ℕ → List ℕ → List ℕ
  | [], s => s
  | s, [] => s
  | a :: s, b :: t => (a + b) :: addShape s t

@[simp] lemma addShape_nil_left (s : List ℕ) : addShape [] s = s := by cases s <;> rfl

@[simp] lemma addShape_nil_right (s : List ℕ) : addShape s [] = s := by cases s <;> rfl

lemma addShape_cons_right (s : List ℕ) (a : ℕ) (u : List ℕ) :
    addShape s (a :: u) = (s.headD 0 + a) :: addShape s.tail u := by
  cases s <;> simp [addShape]

lemma headD_addShape (s u : List ℕ) (h : s ≠ [] ∨ u ≠ []) :
    (addShape s u).headD 1 = s.headD 0 + u.headD 0 := by
  cases s with
  | nil =>
    cases u with
    | nil => simp at h
    | cons b u => simp
  | cons a s =>
    cases u with
    | nil => simp
    | cons b u => simp [addShape]

/-- The outer shape of a skew tableau with inner shape `inner`. -/
def outerShape (inner : List ℕ) (t : List (List T)) : List ℕ := addShape inner (shape t)

omit [LinearOrder T] in
@[simp] lemma outerShape_nil_inner (t : List (List T)) : outerShape [] t = shape t := by
  simp [outerShape]

/-- The outer shape of a skew tableau is a partition. -/
theorem isPart_outerShape {inner : List ℕ} (hinner : IsPart inner) {t : List (List T)}
    (h : IsSkewTableau inner t) : IsPart (outerShape inner t) := by
  induction t generalizing inner with
  | nil => simpa [outerShape] using hinner
  | cons t0 t ih =>
    obtain ⟨hne, -, hdom, hskew⟩ := h
    have hinner' : IsPart inner.tail := by
      cases inner with
      | nil => trivial
      | cons a s => exact hinner.2
    have hi0 : inner.tail.headD 0 ≤ inner.headD 0 := by
      cases inner with
      | nil => simp
      | cons a s =>
        cases s with
        | nil => simp
        | cons b s => simpa using hinner.1
    have ihp := ih hinner' hskew
    rw [outerShape, shape_cons, addShape_cons_right]
    refine ⟨?_, ihp⟩
    by_cases hemp : inner.tail = [] ∧ t = []
    · obtain ⟨h1, h2⟩ := hemp
      rw [h1, h2]
      simp only [shape_nil, addShape_nil_left, List.headD_nil]
      omega
    · have hor : inner.tail ≠ [] ∨ shape t ≠ [] := by
        rcases not_and_or.1 hemp with h1 | h1
        · exact Or.inl h1
        · refine Or.inr ?_
          cases t with
          | nil => exact absurd rfl h1
          | cons t1 t => simp
      rw [headD_addShape _ _ hor]
      have hst : (shape t).headD 0 = (t.headD []).length := by
        cases t <;> rfl
      have hlen := hdom.length_le
      omega

/-! ### The inner shape sits inside the outer shape -/

lemma included_addShape (s u : List ℕ) : Included s (addShape s u) := by
  induction s generalizing u with
  | nil => simp
  | cons a s ih =>
    cases u with
    | nil => simp
    | cons b u => exact ⟨Nat.le_add_right a b, ih u⟩

omit [LinearOrder T] in
/-- The inner shape of a skew tableau is included in its outer shape. -/
lemma included_outerShape (inner : List ℕ) (t : List (List T)) :
    Included inner (outerShape inner t) := included_addShape _ _

omit [LinearOrder T] in
/-- The skew shape between the inner and the outer shape is the shape of the rows. -/
lemma diffShape_outerShape {inner : List ℕ} {t : List (List T)}
    (h : inner.length ≤ t.length) : diffShape inner (outerShape inner t) = shape t := by
  induction inner generalizing t with
  | nil => simp [outerShape]
  | cons a s ih =>
    cases t with
    | nil => simp at h
    | cons t0 t =>
      have h' : s.length ≤ t.length := by simpa using h
      rw [outerShape, shape_cons, addShape_cons_right]
      simp only [List.headD_cons, List.tail_cons, diffShape_cons_cons, Nat.add_sub_cancel_left,
        List.cons.injEq, true_and]
      exact ih h'

end List
