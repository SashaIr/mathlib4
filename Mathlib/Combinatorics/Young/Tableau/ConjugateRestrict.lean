/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Tableau.Conjugate
import Mathlib.Combinatorics.Young.Tableau.Restrict

/-!
# Restricting the transpose of a standard tableau

Transposing a standard tableau commutes with restricting it to its letters `< k`: the boxes
of the transpose carrying a letter `< k` are the transposed boxes of `t` carrying a letter
`< k`.  We record this at the level of shapes, which is what the Robinson–Schensted
correspondence for reversed words needs.

## Main results

* `List.lt_length_ltFilter_getD_iff` : in a weakly increasing row, the letters `< k` form a
  prefix.
* `List.shape_dropMax_conjTab` : `shape (dropMax k (conjTab t)) = conjPart (shape (dropMax k t))`
  for a standard tableau `t`.
-/

namespace List

/-- In a weakly increasing row, the letters `< k` form a prefix: the restricted row has more
than `j` letters exactly when the `j`-th letter of the row exists and is `< k`. -/
lemma lt_length_ltFilter_getD_iff {L : List ℕ} (hL : IsRow L) (k j : ℕ) :
    j < (ltFilter k L).length ↔ j < L.length ∧ L.getD j 0 < k := by
  constructor
  · intro h
    have hj : j < L.length := lt_of_lt_of_le h (length_ltFilter_le k L)
    refine ⟨hj, ?_⟩
    rw [List.getD_eq_getElem _ _ hj]
    exact (lt_length_ltFilter_iff hL hj).2 h
  · rintro ⟨hj, h⟩
    rw [List.getD_eq_getElem _ _ hj] at h
    exact (lt_length_ltFilter_iff hL hj).1 h

/-- **Transposing a standard tableau commutes with restricting it to its letters `< k`**, at
the level of shapes. -/
lemma shape_dropMax_conjTab {t : List (List ℕ)} (ht : IsStdTab t) (k : ℕ) :
    shape (dropMax k (conjTab t)) = conjPart (shape (dropMax k t)) := by
  have hc : IsStdTab (conjTab t) := ht.conjTab
  have hpt : IsPart (shape t) := isPart_shape ht.1
  refine IsPart.ext_getD (isPart_shape (isTableau_dropMax hc.1))
    (isPart_conjPart (isPart_shape (isTableau_dropMax ht.1))) fun j => ?_
  have key : ∀ i, i < (shape (dropMax k (conjTab t))).getD j 0 ↔
      i < (conjPart (shape (dropMax k t))).getD j 0 := by
    intro i
    have hA : i < (shape (dropMax k (conjTab t))).getD j 0 ↔
        (InShape (shape t) (i, j) ∧ (t.getD i []).getD j 0 < k) := by
      rw [getD_shape_dropMax hc.1, lt_length_ltFilter_getD_iff (hc.1.isRow_getD j) k i,
        length_getD_conjTab hpt]
      have hconj := inShape_conjPart hpt i j
      simp only [InShape] at hconj ⊢
      constructor
      · rintro ⟨h1, h2⟩
        have hij : InShape (shape t) (i, j) := by simpa only [InShape] using hconj.2 h1
        rw [getD_getD_conjTab hpt hij] at h2
        exact ⟨hconj.2 h1, h2⟩
      · rintro ⟨hij, h2⟩
        have hij' : InShape (shape t) (i, j) := by simpa only [InShape] using hij
        exact ⟨hconj.1 hij, by rwa [getD_getD_conjTab hpt hij']⟩
    have hB : i < (conjPart (shape (dropMax k t))).getD j 0 ↔
        (InShape (shape t) (i, j) ∧ (t.getD i []).getD j 0 < k) := by
      have h1 := getD_le_conjPart_iff (isPart_shape (isTableau_dropMax (N := k) ht.1)) i j
      rw [getD_shape_dropMax ht.1] at h1
      have h2 := lt_length_ltFilter_getD_iff (ht.1.isRow_getD i) k j
      have h4 : (shape t).getD i 0 = (t.getD i []).length := getD_shape t i
      simp only [InShape]
      omega
    rw [hA, hB]
  have h1 := key ((shape (dropMax k (conjTab t))).getD j 0)
  have h2 := key ((conjPart (shape (dropMax k t))).getD j 0)
  omega

end List
