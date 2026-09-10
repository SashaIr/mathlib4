/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.SemistandardTableau
public import Mathlib.Combinatorics.Young.Shape.ToYoungDiagram
public import Mathlib.Combinatorics.Young.Tableau.Basic

/-!
# Tableaux and Mathlib's semistandard Young tableaux

Following Coq-Combi, a Young tableau is here a list of rows (`t : List (List ℕ)` with
`Young.IsTableau t`), whose shape `Young.shape t` is the list of row lengths.  Mathlib
represents the same object as a function `ℕ → ℕ → ℕ` vanishing outside a `YoungDiagram`
(`SemistandardYoungTableau`).

This file is the dictionary between the two.  The entry `(i, j)` of the Coq-Combi tableau
`t` is `(t.getD i []).getD j 0`, and this function is exactly the corresponding
semistandard Young tableau.

## Main definitions

* `Young.ssytOfTableau` : the semistandard Young tableau of a Coq-Combi tableau.
* `Young.tableauOfSSYT` : the list of rows of a semistandard Young tableau.
* `Young.tableauEquivSSYT` : the tableaux of a given shape are in bijection with the
  semistandard Young tableaux of the corresponding Young diagram.

## Main results

* `Young.isTableau_tableauOfSSYT`, `Young.shape_tableauOfSSYT` : the rows of a
  semistandard Young tableau form a tableau with the expected shape.
* `Young.entry_tableauOfSSYT` : the entries are preserved by the dictionary.
* `Young.sizeTab_eq_card` : the number of boxes agrees.
-/

@[expose] public section

namespace Young

open List

variable {t : List (List ℕ)} {μ : YoungDiagram}

/-! ### From tableaux to semistandard Young tableaux -/

/-- The rows of a tableau whose shape is the list of row lengths of `μ` have the lengths
prescribed by `μ`. -/
lemma length_getD_of_shape_eq (hshape : shape t = μ.rowLens) (i : ℕ) :
    (t.getD i []).length = μ.rowLen i := by
  rw [← getD_shape, hshape, YoungDiagram.getD_rowLens]

/-- **A Coq-Combi tableau is a semistandard Young tableau**: the entry function of a
tableau of shape `μ.rowLens` is a semistandard Young tableau of shape `μ`. -/
def ssytOfTableau (μ : YoungDiagram) (htab : IsTableau t) (hshape : shape t = μ.rowLens) :
    SemistandardYoungTableau μ where
  entry i j := (t.getD i []).getD j 0
  row_weak' {i j1 j2} hj hcell := by
    have h2 : j2 < (t.getD i []).length := by
      rw [length_getD_of_shape_eq hshape]
      exact YoungDiagram.mem_iff_lt_rowLen.1 hcell
    rw [List.getD_eq_getElem _ _ (lt_trans hj h2), List.getD_eq_getElem _ _ h2]
    exact htab.row_le hj.le h2
  col_strict' {i1 i2 j} hi hcell := by
    have h2 : j < (t.getD i2 []).length := by
      rw [length_getD_of_shape_eq hshape]
      exact YoungDiagram.mem_iff_lt_rowLen.1 hcell
    have hdom := htab.dominate_getD hi
    have h1 : j < (t.getD i1 []).length := lt_of_lt_of_le h2 hdom.length_le
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
    exact hdom.getElem_lt j h2
  zeros' {i j} hcell := by
    refine List.getD_eq_default _ _ ?_
    rw [length_getD_of_shape_eq hshape]
    exact not_lt.1 fun h => hcell (YoungDiagram.mem_iff_lt_rowLen.2 h)

@[simp] lemma ssytOfTableau_apply (μ : YoungDiagram) (htab : IsTableau t)
    (hshape : shape t = μ.rowLens) (i j : ℕ) :
    ssytOfTableau μ htab hshape i j = (t.getD i []).getD j 0 := rfl

/-! ### From semistandard Young tableaux to tableaux -/

/-- The list of rows of a semistandard Young tableau. -/
def tableauOfSSYT (μ : YoungDiagram) (T : SemistandardYoungTableau μ) : List (List ℕ) :=
  (List.range (μ.colLen 0)).map fun i => (List.range (μ.rowLen i)).map (T i)

@[simp] lemma length_tableauOfSSYT (μ : YoungDiagram) (T : SemistandardYoungTableau μ) :
    (tableauOfSSYT μ T).length = μ.colLen 0 := by
  simp [tableauOfSSYT]

lemma getD_tableauOfSSYT (μ : YoungDiagram) (T : SemistandardYoungTableau μ) (i : ℕ) :
    (tableauOfSSYT μ T).getD i [] = (List.range (μ.rowLen i)).map (T i) := by
  rcases Nat.lt_or_ge i (μ.colLen 0) with hi | hi
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp [tableauOfSSYT]
  · have hrow : μ.rowLen i = 0 := by
      by_contra hc
      have : (i, 0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.2 (by omega)
      exact absurd (YoungDiagram.mem_iff_lt_colLen.1 this) (by omega)
    rw [List.getD_eq_default _ _ (by simpa using hi), hrow]
    simp

/-- The entries are preserved: the `(i, j)` entry of the tableau of rows of `T` is
`T i j`. -/
lemma entry_tableauOfSSYT (μ : YoungDiagram) (T : SemistandardYoungTableau μ)
    (i j : ℕ) : (((tableauOfSSYT μ T).getD i []).getD j 0) = T i j := by
  rw [getD_tableauOfSSYT]
  rcases Nat.lt_or_ge j (μ.rowLen i) with hj | hj
  · rw [List.getD_eq_getElem _ _ (by simpa using hj)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using hj)]
    exact (T.zeros fun hc => absurd (YoungDiagram.mem_iff_lt_rowLen.1 hc) (by omega)).symm

/-- The shape of the tableau of rows of `T` is the list of row lengths of `μ`. -/
@[simp] lemma shape_tableauOfSSYT (μ : YoungDiagram) (T : SemistandardYoungTableau μ) :
    shape (tableauOfSSYT μ T) = μ.rowLens := by
  simp [shape, tableauOfSSYT, YoungDiagram.rowLens, List.map_map, Function.comp_def]

/-- The rows of a semistandard Young tableau form a Coq-Combi tableau. -/
lemma isTableau_tableauOfSSYT (μ : YoungDiagram) (T : SemistandardYoungTableau μ) :
    IsTableau (tableauOfSSYT μ T) := by
  refine isTableau_of_getD (fun i hi => ?_) (fun i => ?_) (fun i => ?_)
  · rw [length_tableauOfSSYT] at hi
    have hrow : 0 < μ.rowLen i :=
      YoungDiagram.mem_iff_lt_rowLen.1 (YoungDiagram.mem_iff_lt_colLen.2 hi)
    rw [getD_tableauOfSSYT]
    simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
    omega
  · rw [getD_tableauOfSSYT]
    refine List.isChain_iff_pairwise.2 (List.pairwise_map.2 ?_)
    rw [List.pairwise_iff_getElem]
    intro a b ha hb hab
    simp only [List.getElem_range] at *
    exact T.row_weak hab (YoungDiagram.mem_iff_lt_rowLen.2 (by simpa using hb))
  · rw [getD_tableauOfSSYT, getD_tableauOfSSYT]
    refine dominate_of_getElem (by simpa using μ.rowLen_anti i (i + 1) (Nat.le_succ i)) ?_
    intro j hj
    simp only [List.length_map, List.length_range] at hj
    simp only [List.getElem_map, List.getElem_range]
    exact T.col_strict (Nat.lt_succ_self i) (YoungDiagram.mem_iff_lt_rowLen.2 hj)

/-! ### The bijection -/

/-- Two lists of rows with the same shape and the same entries are equal. -/
lemma eq_of_shape_eq_of_getD_eq {a b : List (List ℕ)} (hs : shape a = shape b)
    (he : ∀ i j, (a.getD i []).getD j 0 = (b.getD i []).getD j 0) : a = b := by
  have hlen : a.length = b.length := by
    simpa [shape] using congrArg List.length hs
  refine List.ext_getElem hlen fun i hi hi' => ?_
  have hrow : (a.getD i []).length = (b.getD i []).length := by
    rw [← getD_shape, ← getD_shape, hs]
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at hrow
  refine List.ext_getElem hrow fun j hj hj' => ?_
  have hij := he i j
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi',
    List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at hij
  exact hij

/-- **The tableaux of a given shape are the semistandard Young tableaux of the
corresponding Young diagram.** -/
def tableauEquivSSYT (μ : YoungDiagram) :
    {t : List (List ℕ) // IsTableau t ∧ shape t = μ.rowLens} ≃
      SemistandardYoungTableau μ where
  toFun t := ssytOfTableau μ t.2.1 t.2.2
  invFun T := ⟨tableauOfSSYT μ T, isTableau_tableauOfSSYT μ T, shape_tableauOfSSYT μ T⟩
  left_inv t := Subtype.ext <| eq_of_shape_eq_of_getD_eq
    (by rw [shape_tableauOfSSYT, t.2.2]) fun i j => entry_tableauOfSSYT μ _ i j
  right_inv T := SemistandardYoungTableau.ext fun i j => entry_tableauOfSSYT μ T i j

/-- **The tableaux of shape `sh` are the semistandard Young tableaux of the Young diagram
of `sh`.** -/
def shapeTableauEquivSSYT (sh : List ℕ) (hsh : IsPart sh) :
    {t : List (List ℕ) // IsTableau t ∧ shape t = sh} ≃
      SemistandardYoungTableau (youngDiagram sh hsh) :=
  (Equiv.subtypeEquivRight fun _ => by rw [rowLens_youngDiagram]).trans
    (tableauEquivSSYT (youngDiagram sh hsh))

/-- The number of boxes of a tableau is the number of boxes of the corresponding Young
diagram. -/
lemma sizeTab_eq_card (htab : IsTableau t) :
    sizeTab t = (youngDiagram (shape t) (isPart_shape htab)).card := by
  rw [card_youngDiagram, sizeTab]

end Young

namespace Nat.Partition

open List Young

/-- **The tableaux whose shape is the partition `p` are the semistandard Young tableaux of
the Young diagram of `p`.** -/
def tableauEquivSSYT {n : ℕ} (p : Partition n) :
    {t : List (List ℕ) // IsTableau t ∧ shape t = p.partsList} ≃
      SemistandardYoungTableau p.youngDiagram :=
  Young.shapeTableauEquivSSYT p.partsList (isPart_partsList p)

end Nat.Partition
