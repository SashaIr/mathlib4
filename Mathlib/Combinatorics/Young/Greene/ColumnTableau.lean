/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Greene.ColumnDefs
import Mathlib.Combinatorics.Young.Greene.Tableau

/-!
# The Greene column invariants of the reading word of a tableau

A Lean 4 port of part of `theories/LRrule/Greene.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

The Greene column invariant `greeneCol (toWord t) k` of the reading word of a tableau `t`
is the number of boxes of `t` lying in the `k` first columns, that is
`∑ r, min (rowLen t r) k`.

## Main definitions

* `List.colCol t k` : the colouring of the reading word of `t` in which a letter in the
  column `j < k` gets the colour `j`, the other letters being uncoloured.

## Main results

* `List.greeneCol_toWord` : the Greene column invariant of the reading word of a tableau.
-/

namespace List

open List

variable {T : Type*} [LinearOrder T]

/-! ### Comparing two positions of the reading word -/

omit [LinearOrder T] in
/-- If two positions of the reading word are in the same column, the earlier one is in the
lower (larger index) row. -/
lemma row_lt_row_of_same_col {t : List (List T)} {i j : ℕ} (hi : i < (toWord t).length)
    (hj : j < (toWord t).length) (hij : i < j) (hcol : (coordOf t i).2 = (coordOf t j).2) :
    (coordOf t j).1 < (coordOf t i).1 := by
  obtain ⟨hr, hjc, he⟩ := coordOf_spec hi
  obtain ⟨hr', hjc', he'⟩ := coordOf_spec hj
  rcases lt_trichotomy (coordOf t j).1 (coordOf t i).1 with h | h | h
  · exact h
  · exfalso
    rw [h, ← hcol] at he'
    omega
  · exfalso
    have := rowOffset_add_rowLen_le h hr'
    omega

/-! ### The colouring given by the first `k` columns -/

/-- The colouring of the reading word of `t` in which the letters of the `j`-th column get
the colour `j`, for `j < k`, the other letters being uncoloured. -/
noncomputable def colCol (t : List (List T)) (k : ℕ) : ℕ → Option ℕ :=
  fun i => if (coordOf t i).2 < k then some (coordOf t i).2 else none

omit [LinearOrder T] in
lemma colCol_eq_some_iff {t : List (List T)} {k i x : ℕ} :
    colCol t k i = some x ↔ (coordOf t i).2 = x ∧ x < k := by
  unfold colCol
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun hx => ⟨hx, hx ▸ h⟩, fun hx => hx.1⟩
  · simp only [false_iff, not_and]
    rintro rfl
    exact fun hx => h hx

lemma isGreeneDecCol_colCol {t : List (List T)} (ht : IsTableau t) (k : ℕ) :
    IsGreeneDecCol (toWord t) k (colCol t k) := by
  constructor
  · intro i x hx
    exact (colCol_eq_some_iff.1 hx).2
  · intro i j x hij hj hci hcj
    have hi : i < (toWord t).length := hij.trans hj
    obtain ⟨hci', -⟩ := colCol_eq_some_iff.1 hci
    obtain ⟨hcj', -⟩ := colCol_eq_some_iff.1 hcj
    have hcol : (coordOf t i).2 = (coordOf t j).2 := by rw [hci', hcj']
    have hrow : (coordOf t j).1 < (coordOf t i).1 := row_lt_row_of_same_col hi hj hij hcol
    rw [getElem_toWord_coordOf hi, getElem_toWord_coordOf hj]
    have hbound : (coordOf t j).2 < (t.getD (coordOf t i).1 []).length := by
      rw [← hcol]
      simpa [rowLen] using (coordOf_spec hi).2.1
    have hdom := (ht.dominate_getD hrow).getElem_lt (coordOf t j).2 hbound
    convert hdom using 2

omit [LinearOrder T] in
lemma greeneSize_colCol (t : List (List T)) (k : ℕ) :
    greeneSize (toWord t) (colCol t k) = ∑ r ∈ Finset.range t.length, min (rowLen t r) k := by
  have hmaps : Set.MapsTo (fun i => (coordOf t i).1)
      (((Finset.range (toWord t).length).filter fun i => (colCol t k i).isSome) : Finset ℕ)
      (Finset.range t.length) := by
    intro i hi
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    exact (coordOf_spec hi.1).1
  rw [greeneSize, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun r hr => ?_
  simp only [Finset.mem_range] at hr
  rw [← Finset.card_range (min (rowLen t r) k)]
  refine Finset.card_nbij' (fun i => (coordOf t i).2) (fun j => rowOffset t r + j) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨⟨hilt, hsome⟩, hri⟩ := hi
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
    obtain ⟨hcx, hxk⟩ := colCol_eq_some_iff.1 hx
    have h2 := (coordOf_spec hilt).2.1
    rw [hri] at h2
    simp only [Finset.mem_coe, Finset.mem_range, lt_min_iff]
    exact ⟨h2, by rw [hcx]; exact hxk⟩
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_range, lt_min_iff] at hj
    obtain ⟨hjr, hjk⟩ := hj
    have hcoord := coordOf_eq (t := t) hr hjr
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨rowOffset_add_lt_length hr hjr, ?_⟩, by rw [hcoord]⟩
    rw [Option.isSome_iff_exists]
    exact ⟨j, colCol_eq_some_iff.2 ⟨by rw [hcoord], hjk⟩⟩
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨⟨hilt, -⟩, hri⟩ := hi
    change rowOffset t r + (coordOf t i).2 = i
    have h3 := (coordOf_spec hilt).2.2
    rw [hri] at h3
    exact h3.symm
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_range, lt_min_iff] at hj
    change (coordOf t (rowOffset t r + j)).2 = j
    rw [coordOf_eq hr hj.1]

/-! ### The upper bound -/

/-- Two positions in the same row of a tableau cannot carry the same colour of a strictly
decreasing colouring. -/
lemma not_deccolour_eq_of_same_row {t : List (List T)} (ht : IsTableau t) {k : ℕ}
    {c : ℕ → Option ℕ} (hc : IsGreeneDecCol (toWord t) k c) {i j x : ℕ}
    (hi : i < (toWord t).length) (hj : j < (toWord t).length) (hci : c i = some x)
    (hcj : c j = some x) (hrow : (coordOf t i).1 = (coordOf t j).1) (hij : i < j) : False := by
  obtain ⟨hr1, hj1, he1⟩ := coordOf_spec hi
  obtain ⟨hr2, hj2, he2⟩ := coordOf_spec hj
  rw [hrow] at hr1 hj1 he1
  have hlt : (coordOf t i).2 < (coordOf t j).2 := by omega
  have hwi : (toWord t)[i]'hi
      = (t.getD (coordOf t j).1 [])[(coordOf t i).2]'(by simpa [rowLen] using hj1) := by
    have h := getElem?_toWord hr1 hj1
    rw [← he1] at h
    rwa [List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (show (coordOf t i).2 < (t.getD (coordOf t j).1 []).length by
        simpa [rowLen] using hj1), Option.some_inj] at h
  have hwj : (toWord t)[j]'hj
      = (t.getD (coordOf t j).1 [])[(coordOf t j).2]'(by simpa [rowLen] using hj2) := by
    have h := getElem?_toWord hr2 hj2
    rw [← he2] at h
    rwa [List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem (show (coordOf t j).2 < (t.getD (coordOf t j).1 []).length by
        simpa [rowLen] using hj2), Option.some_inj] at h
  have hgt := hc.gt_of_colour hij hj hci hcj
  rw [hwi, hwj] at hgt
  exact absurd (ht.row_le hlt.le (by simpa [rowLen] using hj2)) (not_le.2 hgt)

lemma greeneSize_le_sum_min {t : List (List T)} (ht : IsTableau t) {k : ℕ} {c : ℕ → Option ℕ}
    (hc : IsGreeneDecCol (toWord t) k c) :
    greeneSize (toWord t) c ≤ ∑ r ∈ Finset.range t.length, min (rowLen t r) k := by
  have hmaps : Set.MapsTo (fun i => (coordOf t i).1)
      (((Finset.range (toWord t).length).filter fun i => (c i).isSome) : Finset ℕ)
      (Finset.range t.length) := by
    intro i hi
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    exact (coordOf_spec hi.1).1
  rw [greeneSize, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_le_sum fun r _ => ?_
  set F := ((Finset.range (toWord t).length).filter fun i => (c i).isSome).filter
    fun i => (coordOf t i).1 = r with hF
  have hrowLen : F.card ≤ rowLen t r := by
    rw [← Finset.card_range (rowLen t r)]
    refine Finset.card_le_card_of_injOn (fun i => (coordOf t i).2) ?_ ?_
    · intro i hi
      simp only [hF, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨⟨hilt, -⟩, hri⟩ := hi
      have h2 := (coordOf_spec hilt).2.1
      rw [hri] at h2
      simpa using h2
    · intro i hi i' hi' heq
      simp only [hF, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi hi'
      obtain ⟨⟨hilt, -⟩, hri⟩ := hi
      obtain ⟨⟨hilt', -⟩, hri'⟩ := hi'
      obtain ⟨-, -, he⟩ := coordOf_spec hilt
      obtain ⟨-, -, he'⟩ := coordOf_spec hilt'
      have heq' : (coordOf t i).2 = (coordOf t i').2 := heq
      rw [he, he', hri, hri', heq']
  have hk : F.card ≤ k := by
    rw [← Finset.card_range k]
    refine Finset.card_le_card_of_injOn (fun i => (c i).getD 0) ?_ ?_
    · intro i hi
      simp only [hF, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨⟨hilt, hsome⟩, -⟩ := hi
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
      simp only [Finset.mem_coe, Finset.mem_range, hx, Option.getD_some]
      exact hc.lt_of_colour hx
    · intro i hi i' hi' heq
      simp only [hF, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi hi'
      obtain ⟨⟨hilt, hsome⟩, hri⟩ := hi
      obtain ⟨⟨hilt', hsome'⟩, hri'⟩ := hi'
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
      obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.1 hsome'
      simp only [hx, hx', Option.getD_some] at heq
      subst heq
      have hrow : (coordOf t i).1 = (coordOf t i').1 := by rw [hri, hri']
      rcases lt_trichotomy i i' with h | h | h
      · exact absurd (not_deccolour_eq_of_same_row ht hc hilt hilt' hx hx' hrow h) (by simp)
      · exact h
      · exact absurd (not_deccolour_eq_of_same_row ht hc hilt' hilt hx' hx hrow.symm h) (by simp)
  exact le_min hrowLen hk

/-- **The Greene column invariant of the reading word of a tableau** is the number of its
boxes lying in the `k` first columns (Coq `Greene_col_tab`). -/
theorem greeneCol_toWord {t : List (List T)} (ht : IsTableau t) (k : ℕ) :
    greeneCol (toWord t) k = ∑ r ∈ Finset.range t.length, min (rowLen t r) k := by
  refine le_antisymm (greeneCol_le fun c hc => greeneSize_le_sum_min ht hc) ?_
  rw [← greeneSize_colCol t k]
  exact le_greeneCol (isGreeneDecCol_colCol ht k)

end List
