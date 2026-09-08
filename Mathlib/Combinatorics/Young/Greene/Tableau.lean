/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Young.Tableau.Basic
import Mathlib.Combinatorics.Young.Greene.Defs

/-!
# The Greene invariants of the reading word of a tableau

A Lean 4 port of part of `theories/LRrule/Greene.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

The Greene invariant `greeneRow (toWord t) k` of the reading word of a tableau `t` is the
sum of the lengths of the `k` first rows of `t`.

## Main definitions

* `List.rowLen t r` : the length of the `r`-th row of `t` (`0` if there is no such row).
* `List.rowOffset t r` : the position at which the `r`-th row starts in the reading word.
* `List.coordOf t i` : the coordinates (row, column) of the position `i` of the reading
  word.
-/

namespace List

open List

variable {T : Type*}

/-! ### Coordinates in the reading word -/

/-- The length of the `r`-th row of `t`, or `0` if `t` has at most `r` rows. -/
def rowLen (t : List (List T)) (r : ℕ) : ℕ := (t.getD r []).length

lemma rowLen_eq_zero {t : List (List T)} {r : ℕ} (hr : t.length ≤ r) : rowLen t r = 0 := by
  simp [rowLen, List.getD_eq_getElem?_getD, List.getElem?_eq_none hr]

@[simp] lemma rowLen_cons_succ (t0 : List T) (t : List (List T)) (r : ℕ) :
    rowLen (t0 :: t) (r + 1) = rowLen t r := by
  simp [rowLen, List.getD_eq_getElem?_getD]

@[simp] lemma rowLen_cons_zero (t0 : List T) (t : List (List T)) :
    rowLen (t0 :: t) 0 = t0.length := by
  simp [rowLen, List.getD_eq_getElem?_getD]

/-- The position in the reading word at which the `r`-th row of `t` starts. -/
def rowOffset (t : List (List T)) (r : ℕ) : ℕ := ((t.drop (r + 1)).map List.length).sum

@[simp] lemma rowOffset_cons_succ (t0 : List T) (t : List (List T)) (r : ℕ) :
    rowOffset (t0 :: t) (r + 1) = rowOffset t r := by
  simp [rowOffset]

lemma rowOffset_cons_zero (t0 : List T) (t : List (List T)) :
    rowOffset (t0 :: t) 0 = (toWord t).length := by
  simp [rowOffset, toWord, List.length_flatten]

lemma length_toWord_eq_sum (t : List (List T)) :
    (toWord t).length = ((t.map List.length).sum) := by
  simp [toWord, List.length_flatten]

/-- Every box of `t` corresponds to a position of the reading word. -/
lemma rowOffset_add_lt_length {t : List (List T)} {r j : ℕ} (hr : r < t.length)
    (hj : j < rowLen t r) : rowOffset t r + j < (toWord t).length := by
  induction t generalizing r with
  | nil => simp at hr
  | cons t0 t ih =>
    cases r with
    | zero =>
      rw [rowOffset_cons_zero]
      simp only [rowLen_cons_zero] at hj
      rw [toWord_cons]
      simp only [List.length_append]
      omega
    | succ r =>
      rw [rowOffset_cons_succ]
      simp only [rowLen_cons_succ] at hj
      have := ih (by simpa using hr) hj
      rw [toWord_cons]
      simp only [List.length_append]
      omega

/-- The letter of the reading word at the position of the box `(r, j)`. -/
lemma getElem?_toWord {t : List (List T)} {r j : ℕ} (hr : r < t.length) (hj : j < rowLen t r) :
    (toWord t)[rowOffset t r + j]? = (t.getD r [])[j]? := by
  induction t generalizing r with
  | nil => simp at hr
  | cons t0 t ih =>
    cases r with
    | zero =>
      simp only [rowLen_cons_zero] at hj
      rw [toWord_cons, rowOffset_cons_zero,
        List.getElem?_append_right (by omega)]
      simp [List.getD_eq_getElem?_getD]
    | succ r =>
      simp only [rowLen_cons_succ] at hj
      have hr' : r < t.length := by simpa using hr
      rw [toWord_cons, rowOffset_cons_succ,
        List.getElem?_append_left (rowOffset_add_lt_length hr' hj), ih hr' hj]
      rfl

lemma getElem_toWord {t : List (List T)} {r j : ℕ} (hr : r < t.length) (hj : j < rowLen t r)
    (h : rowOffset t r + j < (toWord t).length) :
    (toWord t)[rowOffset t r + j] = (t.getD r [])[j]'(by simpa [rowLen] using hj) := by
  have := getElem?_toWord hr hj
  rwa [List.getElem?_eq_getElem h,
    List.getElem?_eq_getElem (show j < (t.getD r []).length by simpa [rowLen] using hj),
    Option.some_inj] at this

/-- Every position of the reading word is the position of a box. -/
lemma exists_coord {t : List (List T)} {i : ℕ} (hi : i < (toWord t).length) :
    ∃ r j, r < t.length ∧ j < rowLen t r ∧ i = rowOffset t r + j := by
  induction t generalizing i with
  | nil => simp [toWord] at hi
  | cons t0 t ih =>
    rw [toWord_cons, List.length_append] at hi
    by_cases h : i < (toWord t).length
    · obtain ⟨r, j, hr, hj, rfl⟩ := ih h
      exact ⟨r + 1, j, by simpa using hr, by simpa using hj, by rw [rowOffset_cons_succ]⟩
    · refine ⟨0, i - (toWord t).length, by simp, by simp; omega, ?_⟩
      rw [rowOffset_cons_zero]
      omega

/-- The offset decreases strictly from one row to the next. -/
lemma rowOffset_step {t : List (List T)} {r : ℕ} (hr : r + 1 < t.length) :
    rowOffset t r = rowLen t (r + 1) + rowOffset t (r + 1) := by
  induction t generalizing r with
  | nil => simp at hr
  | cons t0 t ih =>
    cases r with
    | zero =>
      rw [rowOffset_cons_zero, rowLen_cons_succ, rowOffset_cons_succ]
      cases t with
      | nil => simp at hr
      | cons t1 t =>
        rw [toWord_cons, List.length_append, rowOffset_cons_zero, rowLen_cons_zero]
        omega
    | succ r =>
      rw [rowOffset_cons_succ, rowLen_cons_succ, rowOffset_cons_succ]
      exact ih (by simpa using hr)

lemma rowOffset_add_rowLen_le {t : List (List T)} {r r' : ℕ} (hrr : r < r')
    (hr' : r' < t.length) : rowOffset t r' + rowLen t r' ≤ rowOffset t r := by
  induction r' generalizing r with
  | zero => omega
  | succ n ih =>
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hrr) with rfl | h
    · rw [rowOffset_step (r := r) (by omega)]
      omega
    · have : rowOffset t n + rowLen t n ≤ rowOffset t r := ih h (by omega)
      have hstep : rowOffset t n = rowLen t (n + 1) + rowOffset t (n + 1) :=
        rowOffset_step (by omega)
      omega

/-- The coordinates of a box are determined by its position. -/
lemma coord_unique {t : List (List T)} {r j r' j' : ℕ} (hr : r < t.length)
    (hj : j < rowLen t r) (hr' : r' < t.length) (hj' : j' < rowLen t r')
    (h : rowOffset t r + j = rowOffset t r' + j') : r = r' ∧ j = j' := by
  rcases lt_trichotomy r r' with hlt | rfl | hgt
  · have := rowOffset_add_rowLen_le hlt hr'
    omega
  · exact ⟨rfl, by omega⟩
  · have := rowOffset_add_rowLen_le hgt hr
    omega

open Classical in
/-- The coordinates (row, column) of the position `i` in the reading word of `t`. -/
noncomputable def coordOf (t : List (List T)) (i : ℕ) : ℕ × ℕ :=
  if h : ∃ rj : ℕ × ℕ, rj.1 < t.length ∧ rj.2 < rowLen t rj.1 ∧ i = rowOffset t rj.1 + rj.2
    then h.choose else (0, 0)

lemma coordOf_spec {t : List (List T)} {i : ℕ} (hi : i < (toWord t).length) :
    (coordOf t i).1 < t.length ∧ (coordOf t i).2 < rowLen t (coordOf t i).1 ∧
      i = rowOffset t (coordOf t i).1 + (coordOf t i).2 := by
  obtain ⟨r, j, hr, hj, hij⟩ := exists_coord hi
  have h : ∃ rj : ℕ × ℕ, rj.1 < t.length ∧ rj.2 < rowLen t rj.1 ∧ i = rowOffset t rj.1 + rj.2 :=
    ⟨(r, j), hr, hj, hij⟩
  rw [coordOf, dite_eq_left h]
  exact h.choose_spec

lemma coordOf_eq {t : List (List T)} {r j : ℕ} (hr : r < t.length) (hj : j < rowLen t r) :
    coordOf t (rowOffset t r + j) = (r, j) := by
  obtain ⟨hr', hj', hij⟩ := coordOf_spec (rowOffset_add_lt_length hr hj)
  obtain ⟨h1, h2⟩ := coord_unique hr' hj' hr hj hij.symm
  exact Prod.ext h1 h2

/-! ### Columns of a tableau -/

lemma finset_eq_range_card {S : Finset ℕ} (h : ∀ a b : ℕ, a ≤ b → b ∈ S → a ∈ S) :
    S = Finset.range S.card := by
  refine Finset.eq_of_subset_of_card_le ?_ (by simp)
  intro x hx
  rw [Finset.mem_range]
  apply Nat.lt_of_add_one_le
  rw [← Finset.card_range (x+1)]
  apply Finset.card_le_card
  exact fun y hy => h y x (by simpa using Nat.lt_succ_iff.1 (Finset.mem_range.1 hy)) hx

lemma rowLen_antitone {t : List (List T)} [LinearOrder T] (ht : IsTableau t) {i j : ℕ}
    (hij : i ≤ j) : rowLen t j ≤ rowLen t i := by
  rcases eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  · exact (ht.dominate_getD h).length_le

/-- The height of the `j`-th column of `t`. -/
def colHeight (t : List (List T)) (j : ℕ) : ℕ :=
  ((Finset.range t.length).filter fun r => j < rowLen t r).card

lemma lt_rowLen_iff {t : List (List T)} [LinearOrder T] (ht : IsTableau t) (j r : ℕ) :
    j < rowLen t r ↔ r < colHeight t j := by
  have hS : ((Finset.range t.length).filter fun r => j < rowLen t r)
      = Finset.range (colHeight t j) := by
    refine finset_eq_range_card ?_
    intro a b hab hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨by omega, lt_of_lt_of_le hb.2 (rowLen_antitone ht hab)⟩
  constructor
  · intro h
    have hr : r < t.length := by
      by_contra hcon
      rw [rowLen_eq_zero (by omega)] at h
      omega
    have hmem : r ∈ (Finset.range t.length).filter fun r => j < rowLen t r := by
      simp [hr, h]
    rw [hS] at hmem
    simpa using hmem
  · intro h
    have hmem : r ∈ Finset.range (colHeight t j) := by simpa using h
    rw [← hS] at hmem
    exact (Finset.mem_filter.1 hmem).2

lemma card_filter_lt_rowLen {t : List (List T)} [LinearOrder T] (ht : IsTableau t) (m j : ℕ) :
    ((Finset.range m).filter fun r => j < rowLen t r).card = min m (colHeight t j) := by
  have h : ((Finset.range m).filter fun r => j < rowLen t r)
      = Finset.range (min m (colHeight t j)) := by
    ext r
    simp [lt_rowLen_iff ht]
  rw [h, Finset.card_range]

lemma sum_card_filter_lt_rowLen {t : List (List T)} [LinearOrder T] (ht : IsTableau t) (m : ℕ) :
    ∑ j ∈ Finset.range (rowLen t 0), ((Finset.range m).filter fun r => j < rowLen t r).card
      = ∑ r ∈ Finset.range m, rowLen t r := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.card_filter]
  have h : (Finset.range (rowLen t 0)).filter (fun j => j < rowLen t r)
      = Finset.range (rowLen t r) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h (rowLen_antitone ht (Nat.zero_le r)), h⟩⟩
  rw [h, Finset.card_range]

/-! ### The colouring given by the first `k` rows -/

/-- The colouring of the reading word of `t` in which the letters of the `r`-th row get the
colour `r`, for `r < k`, the other letters being uncoloured. -/
noncomputable def rowCol (t : List (List T)) (k : ℕ) : ℕ → Option ℕ :=
  fun i => if (coordOf t i).1 < k then some (coordOf t i).1 else none

lemma rowCol_eq_some_iff {t : List (List T)} {k i x : ℕ} :
    rowCol t k i = some x ↔ (coordOf t i).1 = x ∧ x < k := by
  unfold rowCol
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun hx => ⟨hx, hx ▸ h⟩, fun hx => hx.1⟩
  · simp only [false_iff, not_and]
    rintro rfl
    exact fun hx => h hx

lemma isGreeneCol_rowCol {t : List (List T)} [LinearOrder T] (ht : IsTableau t) (k : ℕ) :
    IsGreeneCol (toWord t) k (rowCol t k) := by
  constructor
  · intro i x hx
    exact (rowCol_eq_some_iff.1 hx).2
  · intro i j x hij hj hci hcj
    obtain ⟨hri, hxi⟩ := rowCol_eq_some_iff.1 hci
    obtain ⟨hrj, -⟩ := rowCol_eq_some_iff.1 hcj
    have hi : i < (toWord t).length := hij.trans hj
    obtain ⟨hr1, hj1, he1⟩ := coordOf_spec hi
    obtain ⟨hr2, hj2, he2⟩ := coordOf_spec hj
    rw [hri] at he1 hj1 hr1
    rw [hrj] at he2 hj2
    have hlt : (coordOf t i).2 < (coordOf t j).2 := by omega
    have hwi : (toWord t)[i]'hi = (t.getD x [])[(coordOf t i).2]'(by simpa [rowLen] using hj1) := by
      have h := getElem?_toWord hr1 hj1
      rw [← he1] at h
      rwa [List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem (show (coordOf t i).2 < (t.getD x []).length by
          simpa [rowLen] using hj1), Option.some_inj] at h
    have hwj : (toWord t)[j] = (t.getD x [])[(coordOf t j).2]'(by simpa [rowLen] using hj2) := by
      have h := getElem?_toWord hr1 hj2
      rw [← he2] at h
      rwa [List.getElem?_eq_getElem hj,
        List.getElem?_eq_getElem (show (coordOf t j).2 < (t.getD x []).length by
          simpa [rowLen] using hj2), Option.some_inj] at h
    rw [hwi, hwj]
    exact ht.row_le hlt.le (by simpa [rowLen] using hj2)

lemma greeneSize_rowCol (t : List (List T)) (k : ℕ) :
    greeneSize (toWord t) (rowCol t k) = ∑ r ∈ Finset.range (min k t.length), rowLen t r := by
  have hmaps : Set.MapsTo (fun i => (coordOf t i).1)
      (((Finset.range (toWord t).length).filter fun i => (rowCol t k i).isSome) : Finset ℕ)
      (Finset.range (min k t.length)) := by
    intro i hi
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at hi
    obtain ⟨hilt, hsome⟩ := hi
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
    obtain ⟨hr, hxk⟩ := rowCol_eq_some_iff.1 hx
    have := (coordOf_spec hilt).1
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  rw [greeneSize, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun r hr => ?_
  simp only [Finset.mem_range, lt_min_iff] at hr
  obtain ⟨hrk, hrt⟩ := hr
  rw [← Finset.card_range (rowLen t r)]
  refine Finset.card_nbij' (fun i => (coordOf t i).2) (fun j => rowOffset t r + j) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨⟨hilt, -⟩, hri⟩ := hi
    have h2 := (coordOf_spec hilt).2.1
    rw [hri] at h2
    simpa using h2
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_range] at hj
    have hcoord := coordOf_eq (t := t) hrt hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨rowOffset_add_lt_length hrt hj, ?_⟩, by rw [hcoord]⟩
    rw [Option.isSome_iff_exists]
    exact ⟨r, rowCol_eq_some_iff.2 ⟨by rw [hcoord], hrk⟩⟩
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨⟨hilt, -⟩, hri⟩ := hi
    change rowOffset t r + (coordOf t i).2 = i
    have h3 := (coordOf_spec hilt).2.2
    rw [hri] at h3
    exact h3.symm
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_range] at hj
    change (coordOf t (rowOffset t r + j)).2 = j
    rw [coordOf_eq hrt hj]

/-! ### The upper bound -/

/-- The letter of the reading word at a position, in terms of its coordinates. -/
lemma getElem_toWord_coordOf {t : List (List T)} {i : ℕ} (hi : i < (toWord t).length) :
    (toWord t)[i] = (t.getD (coordOf t i).1 [])[(coordOf t i).2]'(by
      simpa [rowLen] using (coordOf_spec hi).2.1) := by
  obtain ⟨hr, hj, he⟩ := coordOf_spec hi
  have h := getElem?_toWord hr hj
  rw [← he] at h
  rwa [List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (show (coordOf t i).2 < (t.getD (coordOf t i).1 []).length by
      simpa [rowLen] using hj), Option.some_inj] at h

/-- Two positions in the same column of a tableau cannot carry the same colour. -/
lemma not_colour_eq_of_same_col {t : List (List T)} [LinearOrder T] (ht : IsTableau t) {k : ℕ}
    {c : ℕ → Option ℕ} (hc : IsGreeneCol (toWord t) k c) {i i' x : ℕ} (hi : i < (toWord t).length)
    (hi' : i' < (toWord t).length) (hci : c i = some x) (hci' : c i' = some x)
    (hcol : (coordOf t i).2 = (coordOf t i').2)
    (hrow : (coordOf t i).1 < (coordOf t i').1) : False := by
  obtain ⟨hr, hj, he⟩ := coordOf_spec hi
  obtain ⟨hr', hj', he'⟩ := coordOf_spec hi'
  have hoff := rowOffset_add_rowLen_le hrow hr'
  have hlt : i' < i := by
    rw [he, he', ← hcol]
    omega
  have hle := hc.le_of_colour hlt hi hci' hci
  rw [getElem_toWord_coordOf hi, getElem_toWord_coordOf hi'] at hle
  have hdom := (ht.dominate_getD hrow).getElem_lt (coordOf t i).2
    (by rw [hcol]; simpa [rowLen] using hj')
  exact absurd hle (not_le.2 (by convert hdom using 2; exact hcol.symm))

lemma greeneSize_le_sum_rowLen {t : List (List T)} [LinearOrder T] (ht : IsTableau t) {k : ℕ}
    {c : ℕ → Option ℕ} (hc : IsGreeneCol (toWord t) k c) :
    greeneSize (toWord t) c ≤ ∑ r ∈ Finset.range (min k t.length), rowLen t r := by
  have hmaps : Set.MapsTo (fun i => (coordOf t i).2)
      (((Finset.range (toWord t).length).filter fun i => (c i).isSome) : Finset ℕ)
      (Finset.range (rowLen t 0)) := by
    intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hilt, -⟩ := hi
    obtain ⟨hr, hj, -⟩ := coordOf_spec hilt
    simp only [Finset.mem_coe, Finset.mem_range]
    exact lt_of_lt_of_le hj (rowLen_antitone ht (Nat.zero_le _))
  rw [greeneSize, Finset.card_eq_sum_card_fiberwise hmaps,
    ← sum_card_filter_lt_rowLen ht (min k t.length)]
  refine Finset.sum_le_sum fun j _ => ?_
  set F := ((Finset.range (toWord t).length).filter fun i => (c i).isSome).filter
    fun i => (coordOf t i).2 = j with hF
  have hcolh : F.card ≤ colHeight t j := by
    refine Finset.card_le_card_of_injOn (fun i => (coordOf t i).1) ?_ ?_
    · intro i hi
      simp only [hF, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨⟨hilt, -⟩, hij⟩ := hi
      obtain ⟨hr, hjj, -⟩ := coordOf_spec hilt
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      exact ⟨hr, by rw [← hij]; exact hjj⟩
    · intro i hi i' hi' heq
      simp only [hF, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi hi'
      obtain ⟨⟨hilt, -⟩, hij⟩ := hi
      obtain ⟨⟨hilt', -⟩, hij'⟩ := hi'
      obtain ⟨-, -, he⟩ := coordOf_spec hilt
      obtain ⟨-, -, he'⟩ := coordOf_spec hilt'
      have heq' : (coordOf t i).1 = (coordOf t i').1 := heq
      rw [he, he', heq', hij, hij']
  have hk : F.card ≤ k := by
    have : F.card ≤ (Finset.range k).card := by
      refine Finset.card_le_card_of_injOn (fun i => (c i).getD 0) ?_ ?_
      · intro i hi
        simp only [hF, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
        obtain ⟨⟨hilt, hsome⟩, -⟩ := hi
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
        simp only [Finset.mem_coe, Finset.mem_range, hx, Option.getD_some]
        exact hc.lt_of_colour hx
      · intro i hi i' hi' heq
        simp only [hF, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi hi'
        obtain ⟨⟨hilt, hsome⟩, hij⟩ := hi
        obtain ⟨⟨hilt', hsome'⟩, hij'⟩ := hi'
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
        obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.1 hsome'
        simp only [hx, hx', Option.getD_some] at heq
        subst heq
        by_contra hne
        have hcolj : (coordOf t i).2 = (coordOf t i').2 := by rw [hij, hij']
        rcases lt_trichotomy (coordOf t i).1 (coordOf t i').1 with h | h | h
        · exact not_colour_eq_of_same_col ht hc hilt hilt' hx hx' hcolj h
        · refine hne ?_
          obtain ⟨-, -, he⟩ := coordOf_spec hilt
          obtain ⟨-, -, he'⟩ := coordOf_spec hilt'
          rw [he, he', h, hcolj]
        · exact not_colour_eq_of_same_col ht hc hilt' hilt hx' hx hcolj.symm h
    simpa using this
  have hlen : colHeight t j ≤ t.length := by
    simpa [colHeight] using Finset.card_filter_le (Finset.range t.length)
      (fun r => j < rowLen t r)
  rw [card_filter_lt_rowLen ht]
  exact le_min (le_min hk (hcolh.trans hlen)) hcolh

/-- **The Greene invariant of the reading word of a tableau** is the sum of the lengths of
its `k` first rows (Coq `Greene_row_tab`). -/
theorem greeneRow_toWord {t : List (List T)} [LinearOrder T] (ht : IsTableau t) (k : ℕ) :
    greeneRow (toWord t) k = ∑ r ∈ Finset.range (min k t.length), rowLen t r := by
  refine le_antisymm (greeneRow_le fun c hc => greeneSize_le_sum_rowLen ht hc) ?_
  rw [← greeneSize_rowCol t k]
  exact le_greeneRow (isGreeneCol_rowCol ht k)

end List
