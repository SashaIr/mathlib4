/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
module

public import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# Semistandard Young tableaux

A semistandard Young tableau is a filling of a Young diagram by natural numbers, such that
the entries are weakly increasing left-to-right along rows (i.e. for fixed `i`), and
strictly-increasing top-to-bottom along columns (i.e. for fixed `j`).

An example of an SSYT of shape `μ = [4, 2, 1]` is:

```text
0 0 0 2
1 1
2
```

We represent a semistandard Young tableau as a function `ℕ → ℕ → ℕ`, which is required to be zero
for all pairs `(i, j) ∉ μ` and to satisfy the row-weak and column-strict conditions on `μ`.


## Main definitions

- `SemistandardYoungTableau (μ : YoungDiagram)`: semistandard Young tableaux of shape `μ`. There is
  a `coe` instance such that `T i j` is value of the `(i, j)` entry of the semistandard Young
  tableau `T`.
- `SemistandardYoungTableau.highestWeight (μ : YoungDiagram)`: the semistandard Young tableau whose
  `i`th row consists entirely of `i`s, for each `i`.

## Main results

- `SemistandardYoungTableau.entry_le_entry`: the entries increase weakly down-and-right.
- `SemistandardYoungTableau.le_entry`: the entries of the `i`th row are at least `i`.
- `SemistandardYoungTableau.highestWeight_le`: `highestWeight μ` is the pointwise smallest
  semistandard Young tableau of shape `μ`.

## Tags

Semistandard Young tableau

## References

<https://en.wikipedia.org/wiki/Young_tableau>

-/

@[expose] public section


/-- A semistandard Young tableau is a filling of the cells of a Young diagram by natural
numbers, such that the entries in each row are weakly increasing (left to right), and the entries
in each column are strictly increasing (top to bottom).

Here, a semistandard Young tableau is represented as an unrestricted function `ℕ → ℕ → ℕ` that, for
reasons of extensionality, is required to vanish outside `μ`. -/
structure SemistandardYoungTableau (μ : YoungDiagram) where
  /-- `entry i j` is value of the `(i, j)` entry of the SSYT `μ`. -/
  entry : ℕ → ℕ → ℕ
  /-- The entries in each row are weakly increasing (left to right). -/
  row_weak' : ∀ {i j1 j2 : ℕ}, j1 < j2 → (i, j2) ∈ μ → entry i j1 ≤ entry i j2
  /-- The entries in each column are strictly increasing (top to bottom). -/
  col_strict' : ∀ {i1 i2 j : ℕ}, i1 < i2 → (i2, j) ∈ μ → entry i1 j < entry i2 j
  /-- `entry` is required to be zero for all pairs `(i, j) ∉ μ`. -/
  zeros' : ∀ {i j}, (i, j) ∉ μ → entry i j = 0

namespace SemistandardYoungTableau

instance instFunLike {μ : YoungDiagram} : FunLike (SemistandardYoungTableau μ) ℕ (ℕ → ℕ) where
  coe := SemistandardYoungTableau.entry
  coe_injective T T' h := by
    cases T
    cases T'
    congr

@[simp]
theorem to_fun_eq_coe {μ : YoungDiagram} {T : SemistandardYoungTableau μ} :
    T.entry = (T : ℕ → ℕ → ℕ) :=
  rfl

@[ext]
theorem ext {μ : YoungDiagram} {T T' : SemistandardYoungTableau μ} (h : ∀ i j, T i j = T' i j) :
    T = T' :=
  DFunLike.ext T T' fun _ ↦ by
    funext
    apply h

/-- Copy of an `SemistandardYoungTableau μ` with a new `entry` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (entry' : ℕ → ℕ → ℕ)
    (h : entry' = T) : SemistandardYoungTableau μ where
  entry := entry'
  row_weak' := h.symm ▸ T.row_weak'
  col_strict' := h.symm ▸ T.col_strict'
  zeros' := h.symm ▸ T.zeros'

@[simp]
theorem coe_copy {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (entry' : ℕ → ℕ → ℕ)
    (h : entry' = T) : ⇑(T.copy entry' h) = entry' :=
  rfl

theorem copy_eq {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (entry' : ℕ → ℕ → ℕ)
    (h : entry' = T) : T.copy entry' h = T :=
  DFunLike.ext' h

theorem row_weak {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j1 j2 : ℕ} (hj : j1 < j2)
    (hcell : (i, j2) ∈ μ) : T i j1 ≤ T i j2 :=
  T.row_weak' hj hcell

theorem col_strict {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i1 i2 j : ℕ} (hi : i1 < i2)
    (hcell : (i2, j) ∈ μ) : T i1 j < T i2 j :=
  T.col_strict' hi hcell

theorem zeros {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j : ℕ}
    (not_cell : (i, j) ∉ μ) : T i j = 0 :=
  T.zeros' not_cell

theorem row_weak_of_le {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j1 j2 : ℕ}
    (hj : j1 ≤ j2) (cell : (i, j2) ∈ μ) : T i j1 ≤ T i j2 := by
  rcases eq_or_lt_of_le hj with h | h
  · rw [h]
  · exact T.row_weak h cell

theorem col_weak {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i1 i2 j : ℕ} (hi : i1 ≤ i2)
    (cell : (i2, j) ∈ μ) : T i1 j ≤ T i2 j := by
  rcases eq_or_lt_of_le hi with h | h
  · rw [h]
  · exact le_of_lt (T.col_strict h cell)

theorem entry_le_entry {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i1 i2 j1 j2 : ℕ}
    (hi : i1 ≤ i2) (hj : j1 ≤ j2) (hcell : (i2, j2) ∈ μ) : T i1 j1 ≤ T i2 j2 :=
  (T.col_weak hi (μ.up_left_mem le_rfl hj hcell)).trans (T.row_weak_of_le hj hcell)

/-- Since the entries of a column increase strictly, the entries of the `i`-th row of a
semistandard Young tableau are at least `i`. -/
theorem le_entry {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j : ℕ}
    (hcell : (i, j) ∈ μ) : i ≤ T i j := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    exact (ih (μ.up_left_mem (Nat.le_succ i) le_rfl hcell)).trans_lt
      (T.col_strict (Nat.lt_succ_self i) hcell)

/-- The "highest weight" SSYT of a given shape has all i's in row i, for each i. -/
def highestWeight (μ : YoungDiagram) : SemistandardYoungTableau μ where
  entry i j := if (i, j) ∈ μ then i else 0
  row_weak' hj hcell := by
    rw [ite_eq_left hcell, ite_eq_left (μ.up_left_mem (by rfl) (le_of_lt hj) hcell)]
  col_strict' hi hcell := by
    rwa [ite_eq_left hcell, ite_eq_left (μ.up_left_mem (le_of_lt hi) (by rfl) hcell)]
  zeros' not_cell := ite_eq_right not_cell

@[simp]
theorem highestWeight_apply {μ : YoungDiagram} {i j : ℕ} :
    highestWeight μ i j = if (i, j) ∈ μ then i else 0 :=
  rfl

/-- The highest weight tableau is the pointwise smallest semistandard Young tableau of its
shape. -/
theorem highestWeight_le {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (i j : ℕ) :
    highestWeight μ i j ≤ T i j := by
  rw [highestWeight_apply]
  split
  · exact T.le_entry ‹_›
  · exact Nat.zero_le _

instance {μ : YoungDiagram} : Inhabited (SemistandardYoungTableau μ) :=
  ⟨highestWeight μ⟩

end SemistandardYoungTableau
