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

The Coq-Combi superstandard tableau of a shape `μ` (`Young.superTab`, whose `i`-th row
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
theorem ssytOfTableau_superTab {μ : List ℕ} (hμ : IsPart μ) :
    ssytOfTableau (YoungDiagram.ofRowLens μ hμ.sortedGE) (isTableau_superTab hμ)
        (by rw [shape_superTab, YoungDiagram.rowLens_ofRowLens_eq_self hμ.2]) =
      SemistandardYoungTableau.highestWeight (YoungDiagram.ofRowLens μ hμ.sortedGE) := by
  ext i j
  rw [ssytOfTableau_apply, getD_superTab, SemistandardYoungTableau.highestWeight_apply]
  simp only [mk_mem_ofRowLens hμ]
  rcases Nat.lt_or_ge j (μ.getD i 0) with hj | hj
  · rw [ite_eq_left hj, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_replicate]
  · rw [ite_eq_right (by omega), List.getD_eq_default _ _ (by simpa using hj)]

/-- The list of rows of the highest weight semistandard Young tableau is the
superstandard tableau. -/
theorem tableauOfSSYT_highestWeight {μ : List ℕ} (hμ : IsPart μ) :
    tableauOfSSYT (YoungDiagram.ofRowLens μ hμ.sortedGE)
        (SemistandardYoungTableau.highestWeight (YoungDiagram.ofRowLens μ hμ.sortedGE)) =
      superTab μ := by
  have h := congrArg (shapeTableauEquivSSYT μ hμ).symm (ssytOfTableau_superTab hμ)
  rw [show (shapeTableauEquivSSYT μ hμ).symm
      (ssytOfTableau (YoungDiagram.ofRowLens μ hμ.sortedGE) (isTableau_superTab hμ)
        (by rw [shape_superTab, YoungDiagram.rowLens_ofRowLens_eq_self hμ.2]))
      = ⟨superTab μ, isTableau_superTab hμ, shape_superTab μ⟩ from
    (shapeTableauEquivSSYT μ hμ).symm_apply_eq.2 rfl] at h
  exact congrArg Subtype.val h.symm

end Young
