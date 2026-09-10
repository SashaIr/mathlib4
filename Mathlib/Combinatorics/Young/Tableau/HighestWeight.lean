/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Tableau.Kostka
public import Mathlib.Combinatorics.Young.Tableau.Semistandard

/-!
# The superstandard tableau is the highest weight tableau

The Coq-Combi superstandard tableau of a shape `η` (`Young.superTab`, whose `i`-th row
consists of copies of `i`) and Mathlib's highest weight semistandard Young tableau
(`SemistandardYoungTableau.highestWeight`) are the same object, seen through the
dictionary of `Mathlib.Combinatorics.Young.Tableau.Semistandard`.

## Main results

* `Young.ssytOfTableau_superTab` : the two canonical tableaux of a shape agree.
* `Young.tableauOfSSYT_highestWeight` : the same statement, read in the other direction.
-/

@[expose] public section

namespace Young

open List

/-- **The superstandard tableau of a shape is the highest weight semistandard Young
tableau of its Young diagram.** -/
theorem ssytOfTableau_superTab {η : List ℕ} (hη : IsPart η) :
    ssytOfTableau (youngDiagram η hη) (isTableau_superTab hη)
        (by rw [shape_superTab, rowLens_youngDiagram]) =
      SemistandardYoungTableau.highestWeight (youngDiagram η hη) := by
  ext i j
  rw [ssytOfTableau_apply, getD_superTab, SemistandardYoungTableau.highestWeight_apply]
  simp only [mk_mem_youngDiagram]
  rcases Nat.lt_or_ge j (η.getD i 0) with hj | hj
  · rw [ite_eq_left hj, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_replicate]
  · rw [ite_eq_right (by omega), List.getD_eq_default _ _ (by simpa using hj)]

/-- The list of rows of the highest weight semistandard Young tableau is the
superstandard tableau. -/
theorem tableauOfSSYT_highestWeight {η : List ℕ} (hη : IsPart η) :
    tableauOfSSYT (youngDiagram η hη)
        (SemistandardYoungTableau.highestWeight (youngDiagram η hη)) = superTab η := by
  have h := congrArg (shapeTableauEquivSSYT η hη).symm (ssytOfTableau_superTab hη)
  rw [show (shapeTableauEquivSSYT η hη).symm
      (ssytOfTableau (youngDiagram η hη) (isTableau_superTab hη)
        (by rw [shape_superTab, rowLens_youngDiagram]))
      = ⟨superTab η, isTableau_superTab hη, shape_superTab η⟩ from
    (shapeTableauEquivSSYT η hη).symm_apply_eq.2 rfl] at h
  exact congrArg Subtype.val h.symm

end Young
