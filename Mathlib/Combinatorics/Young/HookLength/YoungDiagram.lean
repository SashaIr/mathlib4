/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Shape.YoungDiagram
import Mathlib.Combinatorics.Young.HookLength.Formula

/-!
# Hook lengths and the hook length formula for Mathlib's Young diagrams

The hook lengths of `Mathlib.Combinatorics.Young.HookLength.Basic` are defined for a shape
given as a weakly decreasing list.  Through the dictionary of
`Mathlib.Combinatorics.Young.Shape.YoungDiagram`, they are transported here to Mathlib's
`YoungDiagram`, where the hook length of a box is expressed by `YoungDiagram.rowLen` and
`YoungDiagram.colLen`, and the hook product is a product over the boxes of the diagram.

## Main definitions

* `YoungDiagram.hookLength` : the hook length of a box of a Young diagram.
* `YoungDiagram.hookProd` : the product of the hook lengths of all boxes.
* `YoungDiagram.numStdTab` : the number of standard Young tableaux of a given diagram.

## Main results

* `YoungDiagram.hookProd_eq_hookProd` : the two hook products agree.
* `YoungDiagram.numStdTab_mul_hookProd` : **the hook length formula** for a Young diagram:
  the number of standard Young tableaux of shape `mu`, times the product of the hook
  lengths of the boxes of `mu`, is `(mu.card)!`.
* `YoungDiagram.numStdTab_eq_factorial_div_hookProd` : the same, in division form.
-/

namespace YoungDiagram

open List

/-- A product over the boxes of a Young diagram, computed row by row. -/
lemma prod_cells {M : Type*} [CommMonoid M] (mu : YoungDiagram) (f : ℕ × ℕ → M) :
    ∏ x ∈ mu.cells, f x
      = ∏ r ∈ Finset.range (mu.colLen 0), ∏ c ∈ Finset.range (mu.rowLen r), f (r, c) := by
  rw [cells_eq_biUnion, Finset.prod_biUnion]
  · exact Finset.prod_congr rfl fun r _ => by
      rw [Finset.prod_product, Finset.prod_singleton]
  · intro i _ j _ hij
    refine Finset.disjoint_left.2 fun ⟨a, b⟩ ha hb => ?_
    simp only [Finset.mem_product, Finset.mem_singleton] at ha hb
    exact hij (ha.1 ▸ hb.1 ▸ rfl)

/-- The hook length of a box of a Young diagram: the number of boxes to its right in its
row, plus the number of boxes below it in its column, plus one for the box itself. -/
def hookLength (mu : YoungDiagram) (x : ℕ × ℕ) : ℕ :=
  (mu.rowLen x.1 - x.2) + (mu.colLen x.2 - x.1) - 1

/-- The product of the hook lengths of all the boxes of a Young diagram. -/
def hookProd (mu : YoungDiagram) : ℕ := ∏ x ∈ mu.cells, mu.hookLength x

/-- The number of standard Young tableaux of shape `mu`. -/
noncomputable def numStdTab (mu : YoungDiagram) : ℕ := List.numStdTab mu.rowLens

/-- The hook length of a box, read on the list of row lengths. -/
lemma hookLength_eq (mu : YoungDiagram) (r c : ℕ) :
    mu.hookLength (r, c) = List.hookLength mu.rowLens r c := by
  rw [hookLength, List.hookLength, getD_rowLens, colLen_eq_getD_conjPart]

/-- **The two hook products agree**: the product over the boxes of `mu` of the hook
lengths is the hook product of its list of row lengths. -/
theorem hookProd_eq_hookProd (mu : YoungDiagram) : mu.hookProd = List.hookProd mu.rowLens := by
  rw [hookProd, prod_cells, List.hookProd]
  rw [show mu.colLen 0 = mu.rowLens.length from (length_rowLens).symm]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [List.rowHookProd, getD_rowLens]
  exact Finset.prod_congr rfl fun c _ => hookLength_eq mu r c

/-- **The hook length formula for a Young diagram**: the number of standard Young tableaux
of shape `mu`, multiplied by the product of the hook lengths of the boxes of `mu`, is
`(mu.card)!`. -/
theorem numStdTab_mul_hookProd (mu : YoungDiagram) :
    mu.numStdTab * mu.hookProd = Nat.factorial mu.card := by
  rw [numStdTab, hookProd_eq_hookProd, ← sum_rowLens]
  exact List.numStdTab_mul_hookProd (isPart_rowLens mu)

/-- **The hook length formula for a Young diagram**, in division form. -/
theorem numStdTab_eq_factorial_div_hookProd (mu : YoungDiagram) :
    mu.numStdTab = Nat.factorial mu.card / mu.hookProd := by
  rw [numStdTab, hookProd_eq_hookProd, ← sum_rowLens]
  exact List.numStdTab_eq_factorial_div_hookProd (isPart_rowLens mu)

end YoungDiagram
