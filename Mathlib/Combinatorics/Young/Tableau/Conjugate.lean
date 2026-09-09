/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.Young.Shape.Conjugate
import Mathlib.Combinatorics.Young.Tableau.Standard

/-!
# The conjugate of a tableau

A Lean 4 port of the conjugation part of `theories/Combi/stdtab.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

The *conjugate* (or transpose) `conjTab t` of a tableau `t` is obtained by exchanging the
roles of the rows and the columns.  Its shape is the conjugate `conjPart (shape t)` of the
shape of `t`, and conjugation is an involution.  It does not preserve semistandardness —
the rows of the transpose are the columns of `t`, which increase strictly — but it does
preserve *standardness*, whose defining condition is symmetric in the two directions.

## Main definitions

* `List.conjTab` : the transpose of a list of rows (Coq `conj_tab`).

## Main results

* `List.shape_conjTab` : the shape of the transpose is the conjugate shape
  (Coq `shape_conj_tab`).
* `List.conjTab_conjTab` : conjugation is an involution (Coq `conj_tabK`).
* `List.perm_toWord_conjTab` : the transpose has the same entries as the tableau.
* `List.IsStdTab.conjTab` : the transpose of a standard tableau is a standard tableau
  (Coq `is_stdtab_conj`).
-/

namespace List

open List

/-! ### The transpose of a list of rows -/

/-- The transpose of a list of rows: its `j`-th row lists the `j`-th entries of the rows of
`t`, for as long as they exist (Coq `conj_tab`). -/
def conjTab (t : List (List ℕ)) : List (List ℕ) :=
  (range ((shape t).headD 0)).map fun j =>
    (range ((conjPart (shape t)).getD j 0)).map fun i => (t.getD i []).getD j 0

@[simp] lemma length_conjTab (t : List (List ℕ)) :
    (conjTab t).length = (shape t).headD 0 := by
  simp [conjTab]

/-- The first entry of a list of naturals, as a `getD`. -/
lemma getD_zero_eq_headD (l : List ℕ) : l.getD 0 0 = l.headD 0 := by cases l <;> rfl

/-- The rows of the transpose, indexed by the columns of `t`. -/
lemma getD_conjTab (t : List (List ℕ)) {j : ℕ} (hj : j < (shape t).headD 0) :
    (conjTab t).getD j [] =
      (range ((conjPart (shape t)).getD j 0)).map fun i => (t.getD i []).getD j 0 := by
  rw [conjTab, List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

/-- A tableau has at most `sh 0` columns, where `sh` is its shape. -/
lemma lt_headD_shape_of_inShape {t : List (List ℕ)} (h : IsPart (shape t)) {i j : ℕ}
    (hij : InShape (shape t) (i, j)) : j < (shape t).headD 0 := by
  have hmono := h.getD_antitone (Nat.zero_le i)
  have h0 := getD_zero_eq_headD (shape t)
  simp only [InShape] at hij
  omega

/-- The `j`-th row of the transpose has as many entries as the `j`-th column of `t`. -/
lemma length_getD_conjTab {t : List (List ℕ)} (h : IsPart (shape t)) (j : ℕ) :
    ((conjTab t).getD j []).length = (conjPart (shape t)).getD j 0 := by
  rcases Nat.lt_or_ge j ((shape t).headD 0) with hj | hj
  · rw [getD_conjTab t hj]; simp
  · rw [List.getD_eq_default _ _ (by simpa using hj),
      List.getD_eq_default _ _ (by rw [length_conjPart h]; exact hj)]
    simp

/-- Coq `shape_conj_tab`: the shape of the transpose is the conjugate shape. -/
theorem shape_conjTab {t : List (List ℕ)} (h : IsPart (shape t)) :
    shape (conjTab t) = conjPart (shape t) := by
  have hlen : (shape (conjTab t)).length = (conjPart (shape t)).length := by
    rw [length_shape, length_conjTab, length_conjPart h]
  refine List.ext_getElem hlen fun j hj hj' => ?_
  rw [← List.getD_eq_getElem (shape (conjTab t)) 0 hj,
    ← List.getD_eq_getElem (conjPart (shape t)) 0 hj', getD_shape, length_getD_conjTab h]

/-- The shape of the transpose is a partition as soon as the shape is. -/
lemma isPart_shape_conjTab {t : List (List ℕ)} (h : IsPart (shape t)) :
    IsPart (shape (conjTab t)) := by
  rw [shape_conjTab h]; exact isPart_conjPart h

/-- The entries of the transpose are the entries of `t`, with the coordinates exchanged. -/
lemma getD_getD_conjTab {t : List (List ℕ)} (h : IsPart (shape t)) {i j : ℕ}
    (hij : InShape (shape t) (i, j)) :
    ((conjTab t).getD j []).getD i 0 = (t.getD i []).getD j 0 := by
  rw [getD_conjTab t (lt_headD_shape_of_inShape h hij),
    List.getD_eq_getElem _ _ (by
      simpa [List.length_map, List.length_range, InShape] using
        (inShape_conjPart h i j).1 hij)]
  simp

/-- The entries of the transpose, in `getElem` form. -/
lemma getElem_getD_conjTab {t : List (List ℕ)} (h : IsPart (shape t)) {i j : ℕ}
    (hi : i < ((conjTab t).getD j []).length) :
    ((conjTab t).getD j [])[i] = (t.getD i []).getD j 0 := by
  rw [length_getD_conjTab h] at hi
  have hij : InShape (shape t) (i, j) := (inShape_conjPart h i j).2 hi
  rw [← List.getD_eq_getElem _ 0 (by rw [length_getD_conjTab h]; exact hi),
    getD_getD_conjTab h hij]

/-- Coq `conj_tabK`: conjugation is an involution. -/
theorem conjTab_conjTab {t : List (List ℕ)} (h : IsPart (shape t)) : conjTab (conjTab t) = t := by
  have hc := isPart_shape_conjTab h
  have hsh : shape (conjTab (conjTab t)) = shape t := by
    rw [shape_conjTab hc, shape_conjTab h, conjPart_conjPart h]
  have hrow : ∀ i, (conjTab (conjTab t)).getD i [] = t.getD i [] := by
    intro i
    have hlenrow : ((conjTab (conjTab t)).getD i []).length = (t.getD i []).length := by
      rw [← getD_shape, hsh, getD_shape]
    refine List.ext_getElem hlenrow fun j hj hj' => ?_
    have hij : InShape (shape t) (i, j) := by rwa [InShape, getD_shape]
    rw [← List.getD_eq_getElem _ 0 hj, ← List.getD_eq_getElem _ 0 hj',
      getD_getD_conjTab hc (by rw [shape_conjTab h]; exact (inShape_conjPart h i j).1 hij),
      getD_getD_conjTab h hij]
  have hlen : (conjTab (conjTab t)).length = t.length := by
    rw [← length_shape, hsh, length_shape]
  refine List.ext_getElem hlen fun i hi hi' => ?_
  rw [← List.getD_eq_getElem _ [] hi, ← List.getD_eq_getElem _ [] hi', hrow]

/-! ### The entries of the transpose -/

/-- A list of naturals, as the sum of the singletons of its entries. -/
private lemma coe_eq_sum_singleton (l : List ℕ) :
    (l : Multiset ℕ) = ∑ j ∈ Finset.range l.length, ({l.getD j 0} : Multiset ℕ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    have hs : ∀ j, (a :: l).getD (j + 1) 0 = l.getD j 0 := fun _ => rfl
    simp only [hs, List.getD_cons_zero, ← ih, ← Multiset.cons_coe]
    rw [← Multiset.singleton_add, add_comm]

/-- The same sum, over any range containing the entries. -/
private lemma coe_eq_sum_singleton_range (l : List ℕ) {C : ℕ} (hC : l.length ≤ C) :
    (l : Multiset ℕ)
      = ∑ j ∈ Finset.range C, (if j < l.length then ({l.getD j 0} : Multiset ℕ) else 0) := by
  have hsub : Finset.range l.length ⊆ Finset.range C := by
    intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
  rw [← Finset.sum_subset hsub
    (fun x _ hx => by simp only [Finset.mem_range] at hx; rw [ite_eq_right hx]),
    coe_eq_sum_singleton l]
  exact Finset.sum_congr rfl fun j hj => by rw [ite_eq_left (Finset.mem_range.1 hj)]

/-- The reading word and the concatenation have the same entries. -/
private lemma coe_toWord (L : List (List ℕ)) :
    (toWord L : Multiset ℕ) = (L.flatten : Multiset ℕ) := by
  induction L with
  | nil => simp [toWord]
  | cons r L ih =>
    rw [toWord_cons, List.flatten_cons]
    simp only [← Multiset.coe_add, ih, add_comm]

/-- The concatenation of a list of rows, summed over the rows. -/
private lemma coe_flatten_eq_sum (L : List (List ℕ)) :
    (L.flatten : Multiset ℕ)
      = ∑ i ∈ Finset.range L.length, ((L.getD i [] : List ℕ) : Multiset ℕ) := by
  induction L with
  | nil => simp
  | cons r L ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.flatten_cons]
    have hs : ∀ i, (r :: L).getD (i + 1) [] = L.getD i [] := fun _ => rfl
    simp only [hs, List.getD_cons_zero, ← ih]
    simp [add_comm]

/-- The entries of a list of rows, summed box by box over a rectangle containing it. -/
private lemma coe_flatten_eq_sum_boxes {u : List (List ℕ)} (h : IsPart (shape u)) {R C : ℕ}
    (hR : u.length ≤ R) (hC : (shape u).headD 0 ≤ C) :
    (u.flatten : Multiset ℕ) = ∑ i ∈ Finset.range R, ∑ j ∈ Finset.range C,
      (if InShape (shape u) (i, j) then ({(u.getD i []).getD j 0} : Multiset ℕ) else 0) := by
  have hsub : Finset.range u.length ⊆ Finset.range R := by
    intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
  have hiff : ∀ i j, InShape (shape u) (i, j) ↔ j < (u.getD i []).length := by
    intro i j
    change j < (shape u).getD i 0 ↔ _
    rw [getD_shape]
  have hrow : ∀ i, ((u.getD i [] : List ℕ) : Multiset ℕ) = ∑ j ∈ Finset.range C,
      (if InShape (shape u) (i, j) then ({(u.getD i []).getD j 0} : Multiset ℕ) else 0) := by
    intro i
    have hle : (u.getD i []).length ≤ C := by
      have := h.getD_antitone (Nat.zero_le i)
      have h0 := getD_zero_eq_headD (shape u)
      rw [← getD_shape]
      omega
    rw [coe_eq_sum_singleton_range (u.getD i []) hle]
    exact Finset.sum_congr rfl fun j _ => by simp only [hiff]
  have hzero : ∀ x ∈ Finset.range R, x ∉ Finset.range u.length →
      ((u.getD x [] : List ℕ) : Multiset ℕ) = 0 := by
    intro x _ hx
    simp only [Finset.mem_range, not_lt] at hx
    rw [List.getD_eq_default _ _ hx]
    simp
  rw [coe_flatten_eq_sum u, Finset.sum_subset hsub hzero]
  exact Finset.sum_congr rfl fun i _ => hrow i

/-- The transpose of a tableau has the same entries as the tableau. -/
theorem perm_toWord_conjTab {t : List (List ℕ)} (h : IsPart (shape t)) :
    (toWord (conjTab t)).Perm (toWord t) := by
  have hc := isPart_shape_conjTab h
  have hheadC : (shape (conjTab t)).headD 0 = t.length := by
    rw [shape_conjTab h, ← length_conjPart (isPart_conjPart h), conjPart_conjPart h, length_shape]
  have hshiff : ∀ i j, InShape (shape (conjTab t)) (j, i) ↔ InShape (shape t) (i, j) := by
    intro i j
    rw [shape_conjTab h]
    exact (inShape_conjPart h i j).symm
  rw [← Multiset.coe_eq_coe, coe_toWord, coe_toWord,
    coe_flatten_eq_sum_boxes hc (le_of_eq (length_conjTab t)) (le_of_eq hheadC),
    coe_flatten_eq_sum_boxes h (le_refl _) (le_refl _), Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : InShape (shape t) (i, j)
  · rw [ite_eq_left hij, ite_eq_left ((hshiff i j).2 hij), getD_getD_conjTab h hij]
  · rw [ite_eq_right hij, ite_eq_right (fun hx => hij ((hshiff i j).1 hx))]

/-! ### Conjugating a standard tableau -/

/-- The rows of a standard tableau are duplicate-free. -/
lemma IsStdTab.nodup_getD {t : List (List ℕ)} (h : IsStdTab t) (i : ℕ) :
    (t.getD i []).Nodup := by
  rcases Nat.lt_or_ge i t.length with hi | hi
  · have hnd : (toWord t).Nodup := h.2.nodup_iff.2 List.nodup_range
    refine hnd.sublist ?_
    rw [toWord]
    exact List.sublist_flatten_of_mem
      (by rw [List.getD_eq_getElem _ _ hi]; exact List.mem_reverse.2 (List.getElem_mem hi))
  · rw [List.getD_eq_default _ _ hi]; exact List.nodup_nil

/-- The rows of a standard tableau increase strictly. -/
lemma IsStdTab.row_lt {t : List (List ℕ)} (h : IsStdTab t) {i c c' : ℕ} (hcc : c < c')
    (hc' : c' < (t.getD i []).length) :
    (t.getD i [])[c]'(by omega) < (t.getD i [])[c'] := by
  refine lt_of_le_of_ne (h.1.row_le (le_of_lt hcc) hc') fun heq => ?_
  have := (h.nodup_getD i).getElem_inj_iff.1 heq
  omega

/-- The transpose of a standard tableau is a tableau. -/
lemma IsStdTab.isTableau_conjTab {t : List (List ℕ)} (h : IsStdTab t) :
    IsTableau (conjTab t) := by
  have hp : IsPart (shape t) := isPart_shape h.1
  have hcp : IsPart (conjPart (shape t)) := isPart_conjPart hp
  refine isTableau_of_getD ?_ ?_ ?_
  · intro j hj
    rw [length_conjTab] at hj
    have hpos : 0 < ((conjTab t).getD j []).length := by
      rw [length_getD_conjTab hp]
      exact hcp.getD_pos (by rwa [length_conjPart hp])
    exact fun he => by rw [he] at hpos; simp at hpos
  · intro j
    change List.IsChain (· ≤ ·) _
    rw [isChain_iff_getElem]
    intro i hi
    have hi' : i < ((conjTab t).getD j []).length := by omega
    have hlen : i + 1 < (conjPart (shape t)).getD j 0 := by
      rwa [length_getD_conjTab hp] at hi
    have hin : InShape (shape t) (i + 1, j) := (inShape_conjPart hp (i + 1) j).2 hlen
    have hjlen : j < (t.getD (i + 1) []).length := by rwa [InShape, getD_shape] at hin
    have hjlen0 : j < (t.getD i []).length :=
      lt_of_lt_of_le hjlen (h.1.dominate_getD i.lt_succ_self).length_le
    rw [getElem_getD_conjTab hp hi', getElem_getD_conjTab hp hi,
      List.getD_eq_getElem _ _ hjlen0, List.getD_eq_getElem _ _ hjlen]
    exact le_of_lt (h.1.col_lt hjlen)
  · intro j
    refine dominate_of_getElem ?_ ?_
    · rw [length_getD_conjTab hp, length_getD_conjTab hp]
      exact hcp.getD_succ_le j
    · intro i hi
      have hdomlen : ((conjTab t).getD (j + 1) []).length ≤ ((conjTab t).getD j []).length := by
        rw [length_getD_conjTab hp, length_getD_conjTab hp]
        exact hcp.getD_succ_le j
      have hlen : i < (conjPart (shape t)).getD (j + 1) 0 := by
        rwa [length_getD_conjTab hp] at hi
      have hin : InShape (shape t) (i, j + 1) := (inShape_conjPart hp i (j + 1)).2 hlen
      have hjlen : j + 1 < (t.getD i []).length := by rwa [InShape, getD_shape] at hin
      have hjlen0 : j < (t.getD i []).length := by omega
      rw [getElem_getD_conjTab hp hi, getElem_getD_conjTab hp (lt_of_lt_of_le hi hdomlen),
        List.getD_eq_getElem _ _ hjlen0, List.getD_eq_getElem _ _ hjlen]
      exact h.row_lt j.lt_succ_self hjlen

/-- Coq `is_stdtab_conj`: the transpose of a standard tableau is a standard tableau. -/
theorem IsStdTab.conjTab {t : List (List ℕ)} (h : IsStdTab t) : IsStdTab (List.conjTab t) :=
  ⟨h.isTableau_conjTab, h.2.of_perm (perm_toWord_conjTab (isPart_shape h.1))⟩

end List
