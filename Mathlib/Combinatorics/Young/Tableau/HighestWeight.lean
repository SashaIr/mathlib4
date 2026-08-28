/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Tableau.Kostka
import Mathlib.Combinatorics.Young.Tableau.Semistandard

/-!
# The superstandard tableau is the highest weight tableau

The Coq-Combi superstandard tableau of a shape `lam` (`List.superTab`, whose `i`-th row
consists of copies of `i`) and Mathlib's highest weight semistandard Young tableau
(`SemistandardYoungTableau.highestWeight`) are the same object, seen through the
dictionary of `Mathlib.Combinatorics.Young.Tableau.Semistandard`.

## Main results

* `List.ssytOfTableau_superTab` : the two canonical tableaux of a shape agree.
* `List.tableauOfSSYT_highestWeight` : the same statement, read in the other direction.
-/

namespace List

open List

/-- **The superstandard tableau of a shape is the highest weight semistandard Young
tableau of its Young diagram.** -/
theorem ssytOfTableau_superTab {lam : List ℕ} (hlam : IsPart lam) :
    ssytOfTableau (youngDiagram lam hlam) (isTableau_superTab hlam)
        (by rw [shape_superTab, rowLens_youngDiagram]) =
      SemistandardYoungTableau.highestWeight (youngDiagram lam hlam) := by
  ext i j
  rw [ssytOfTableau_apply, getD_superTab, SemistandardYoungTableau.highestWeight_apply]
  simp only [mk_mem_youngDiagram]
  rcases Nat.lt_or_ge j (lam.getD i 0) with hj | hj
  · rw [if_pos hj, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_replicate]
  · rw [if_neg (by omega), List.getD_eq_default _ _ (by simpa using hj)]

/-- The list of rows of the highest weight semistandard Young tableau is the
superstandard tableau. -/
theorem tableauOfSSYT_highestWeight {lam : List ℕ} (hlam : IsPart lam) :
    tableauOfSSYT (youngDiagram lam hlam)
        (SemistandardYoungTableau.highestWeight (youngDiagram lam hlam)) = superTab lam := by
  have h := congrArg (shapeTableauEquivSSYT lam hlam).symm (ssytOfTableau_superTab hlam)
  rw [show (shapeTableauEquivSSYT lam hlam).symm
      (ssytOfTableau (youngDiagram lam hlam) (isTableau_superTab hlam)
        (by rw [shape_superTab, rowLens_youngDiagram]))
      = ⟨superTab lam, isTableau_superTab hlam, shape_superTab lam⟩ from
    (shapeTableauEquivSSYT lam hlam).symm_apply_eq.2 rfl] at h
  exact congrArg Subtype.val h.symm

end List
