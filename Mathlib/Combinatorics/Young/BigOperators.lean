/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# Products and sums over the cells of a Young diagram

A product over the cells of a Young diagram can be computed row by row, which is the form in
which such products are usually written:
`∏ x ∈ μ.cells, f x = ∏ i ∈ range (μ.colLen 0), ∏ j ∈ range (μ.rowLen i), f (i, j)`.

## Main results

- `YoungDiagram.cells_eq_biUnion`: the cells of a Young diagram, row by row.
- `YoungDiagram.prod_cells`, `YoungDiagram.sum_cells`: products and sums over the cells of a
  Young diagram, computed row by row.
- `YoungDiagram.card_eq_sum_rowLen`, `YoungDiagram.card_eq_sum_colLen`: the number of cells is
  the sum of the row lengths, and also the sum of the column lengths.
-/

@[expose] public section

namespace YoungDiagram

/-- The cells of a Young diagram, row by row. -/
theorem cells_eq_biUnion (μ : YoungDiagram) :
    μ.cells = (Finset.range (μ.colLen 0)).biUnion
      fun i => {i} ×ˢ Finset.range (μ.rowLen i) := by
  ext ⟨i, j⟩
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product, Finset.mem_singleton,
    mem_cells]
  constructor
  · intro hij
    exact ⟨i, mem_iff_lt_colLen.1 (μ.up_left_mem le_rfl (Nat.zero_le j) hij), rfl,
      mem_iff_lt_rowLen.1 hij⟩
  · rintro ⟨i, -, rfl, hj⟩
    exact mem_iff_lt_rowLen.2 hj

/-- A product over the cells of a Young diagram, computed row by row. -/
@[to_additive /-- A sum over the cells of a Young diagram, computed row by row. -/]
theorem prod_cells {M : Type*} [CommMonoid M] (μ : YoungDiagram) (f : ℕ × ℕ → M) :
    ∏ x ∈ μ.cells, f x
      = ∏ i ∈ Finset.range (μ.colLen 0), ∏ j ∈ Finset.range (μ.rowLen i), f (i, j) := by
  rw [cells_eq_biUnion, Finset.prod_biUnion]
  · exact Finset.prod_congr rfl fun i _ => by
      rw [Finset.prod_product, Finset.prod_singleton]
  · intro i _ j _ hij
    refine Finset.disjoint_left.2 fun ⟨a, b⟩ ha hb => ?_
    simp only [Finset.mem_product, Finset.mem_singleton] at ha hb
    exact hij (ha.1 ▸ hb.1 ▸ rfl)

/-- The number of cells of a Young diagram is the sum of its row lengths. -/
theorem card_eq_sum_rowLen (μ : YoungDiagram) :
    μ.card = ∑ i ∈ Finset.range (μ.colLen 0), μ.rowLen i := by
  rw [YoungDiagram.card, Finset.card_eq_sum_ones, sum_cells]
  simp

/-- The number of cells of a Young diagram is the sum of its column lengths. -/
theorem card_eq_sum_colLen (μ : YoungDiagram) :
    μ.card = ∑ j ∈ Finset.range (μ.rowLen 0), μ.colLen j := by
  rw [← card_transpose, card_eq_sum_rowLen, colLen_transpose]
  exact Finset.sum_congr rfl fun j _ => rowLen_transpose μ j

end YoungDiagram
