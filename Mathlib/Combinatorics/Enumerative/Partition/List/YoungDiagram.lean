/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.List.Included
public import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# The list model of partitions and Mathlib's Young diagrams

The Coq-Combi development, and therefore this port, represents the shape of a Young diagram
by the weakly decreasing list of its row lengths (`ν : List ℕ` with `Young.IsPart ν`),
and the box `(r, c)` belongs to that diagram when `Young.InShape ν (r, c)`, that is
`c < ν.getD r 0`.  Mathlib instead represents a Young diagram by the finite lower set of
its boxes (`YoungDiagram`), and its `YoungDiagram.ofRowLens` builds it from the list of row
lengths; since `Young.IsPart ν` *is* the condition `ν.SortedGE ∧ ∀ x ∈ ν, 0 < x` defining the
subtype of `YoungDiagram.equivListRowLens`, the diagram of a partition `ν` is literally
`YoungDiagram.ofRowLens ν h.sortedGE`, and the bijection between the two models is
`YoungDiagram.equivListRowLens`.

This file is the dictionary between the two.  It translates every basic notion of the
list model (parts, size, number of parts, conjugate, inclusion) into the corresponding
Mathlib notion (`YoungDiagram.rowLen`, `YoungDiagram.card`, `YoungDiagram.colLen`,
`YoungDiagram.transpose`, `≤`).

## Main results

* `Young.isPart_rowLens` : the row lengths of a Young diagram are a partition.
* `Young.mem_ofRowLens_iff_inShape` : the boxes of `YoungDiagram.ofRowLens ν _` are the
  boxes of `ν`.
* `Young.rowLen_ofRowLens_eq_getD` : the row lengths are the parts.
* `Young.colLen_ofRowLens_eq_getD_conjPart`, `Young.colLen_eq_getD_conjPart` : the column
  lengths are the parts of the conjugate.
* `Young.card_ofRowLens_eq_sum` : the number of boxes is the size of the partition.
* `Young.transpose_ofRowLens`, `Young.rowLens_transpose` : `Young.conjPart` is
  `YoungDiagram.transpose`.
* `Young.ofRowLens_le_iff_included` : `Young.Included` is the containment order on Young
  diagrams.
* `Young.listPartEquivYoungDiagramCard` : the partitions of `n` as lists are the Young
  diagrams with `n` boxes.
-/

@[expose] public section

namespace Young

open List YoungDiagram

variable {ν : List ℕ}

/-! ### The Young diagram of a partition -/

/-- The list of row lengths of a Young diagram is a partition in the sense of Coq-Combi. -/
lemma isPart_rowLens (μ : YoungDiagram) : IsPart μ.rowLens :=
  ⟨μ.rowLens_sorted, μ.pos_of_mem_rowLens⟩

/-- The Young diagram of a partition only depends on its list of parts. -/
lemma ofRowLens_congr {ν1 ν2 : List ℕ} (h1 : IsPart ν1) (h2 : IsPart ν2) (h : ν1 = ν2) :
    ofRowLens ν1 h1.sortedGE = ofRowLens ν2 h2.sortedGE := by
  subst h; rfl

/-- The boxes of the Young diagram of `ν` are exactly the boxes of the shape `ν`. -/
@[simp] theorem mem_ofRowLens_iff_inShape (h : IsPart ν) (rc : ℕ × ℕ) :
    rc ∈ ofRowLens ν h.sortedGE ↔ InShape ν rc := by
  rw [YoungDiagram.mem_ofRowLens, InShape]
  constructor
  · rintro ⟨hlt, hc⟩
    rwa [List.getD_eq_getElem _ _ hlt]
  · intro hc
    have hlt : rc.1 < ν.length := by
      by_contra hr
      rw [List.getD_eq_default _ _ (not_lt.1 hr)] at hc
      exact absurd hc (by simp)
    exact ⟨hlt, by rwa [List.getD_eq_getElem _ _ hlt] at hc⟩

theorem mk_mem_ofRowLens (h : IsPart ν) (r c : ℕ) :
    (r, c) ∈ ofRowLens ν h.sortedGE ↔ c < ν.getD r 0 :=
  mem_ofRowLens_iff_inShape h (r, c)

/-- The `i`-th row length of the Young diagram of `ν` is the `i`-th part of `ν`. -/
@[simp] theorem rowLen_ofRowLens_eq_getD (h : IsPart ν) (i : ℕ) :
    (ofRowLens ν h.sortedGE).rowLen i = ν.getD i 0 := by
  refine Nat.le_antisymm ?_ ?_
  · by_contra hc
    have hmem : (i, ν.getD i 0) ∈ ofRowLens ν h.sortedGE :=
      YoungDiagram.mem_iff_lt_rowLen.2 (by omega)
    rw [mk_mem_ofRowLens h] at hmem
    omega
  · by_contra hc
    have hmem : (i, (ofRowLens ν h.sortedGE).rowLen i) ∈ ofRowLens ν h.sortedGE := by
      rw [mk_mem_ofRowLens h]; omega
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.1 hmem) (lt_irrefl _)

/-- The number of nonempty rows of the Young diagram of `ν` is the number of parts. -/
theorem colLen_zero_ofRowLens (h : IsPart ν) :
    (ofRowLens ν h.sortedGE).colLen 0 = ν.length := by
  rw [← YoungDiagram.length_rowLens, rowLens_ofRowLens_eq_self h.2]

/-- The `j`-th column length of the Young diagram of `ν` is the `j`-th part of the
conjugate partition. -/
@[simp] theorem colLen_ofRowLens_eq_getD_conjPart (h : IsPart ν) (j : ℕ) :
    (ofRowLens ν h.sortedGE).colLen j = (conjPart ν).getD j 0 := by
  refine Nat.le_antisymm ?_ ?_
  · by_contra hc
    have hmem : ((conjPart ν).getD j 0, j) ∈ ofRowLens ν h.sortedGE :=
      YoungDiagram.mem_iff_lt_colLen.2 (by omega)
    rw [mk_mem_ofRowLens h] at hmem
    exact absurd ((inShape_conjPart h ((conjPart ν).getD j 0) j).1 hmem) (lt_irrefl _)
  · by_contra hc
    have hmem : InShape (conjPart ν) (j, (ofRowLens ν h.sortedGE).colLen j) := by
      simp only [InShape]; omega
    have hin : ((ofRowLens ν h.sortedGE).colLen j, j) ∈ ofRowLens ν h.sortedGE := by
      rw [mk_mem_ofRowLens h]
      exact (inShape_conjPart h _ j).2 hmem
    exact absurd (YoungDiagram.mem_iff_lt_colLen.1 hin) (lt_irrefl _)

/-- The number of boxes of the Young diagram of `ν` is the size of `ν`. -/
@[simp] theorem card_ofRowLens_eq_sum (h : IsPart ν) :
    (ofRowLens ν h.sortedGE).card = ν.sum :=
  YoungDiagram.card_cellsOfRowLens ν

/-- The column lengths of a Young diagram are the parts of the conjugate of its list of
row lengths. -/
theorem colLen_eq_getD_conjPart (μ : YoungDiagram) (j : ℕ) :
    μ.colLen j = (conjPart μ.rowLens).getD j 0 := by
  conv_lhs => rw [← YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := μ)]
  exact colLen_ofRowLens_eq_getD_conjPart (isPart_rowLens μ) j

/-! ### Conjugation is transposition -/

/-- **Conjugation of shapes is transposition of Young diagrams**: the Coq-Combi
`conj_part` corresponds to Mathlib's `YoungDiagram.transpose`. -/
theorem transpose_ofRowLens (h : IsPart ν) :
    (ofRowLens ν h.sortedGE).transpose = ofRowLens (conjPart ν) (isPart_conjPart h).sortedGE := by
  ext ⟨r, c⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_transpose, Prod.swap_prod_mk,
    mk_mem_ofRowLens h, mk_mem_ofRowLens (isPart_conjPart h)]
  simpa [InShape] using inShape_conjPart h c r

/-- The row lengths of the transpose of a Young diagram are the conjugate of its row
lengths. -/
theorem rowLens_transpose (μ : YoungDiagram) : μ.transpose.rowLens = conjPart μ.rowLens := by
  conv_lhs => rw [← YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := μ)]
  rw [transpose_ofRowLens (isPart_rowLens μ),
    rowLens_ofRowLens_eq_self (isPart_conjPart (isPart_rowLens μ)).2]

/-! ### Inclusion is containment -/

/-- **Inclusion of shapes is containment of Young diagrams.** -/
theorem ofRowLens_le_iff_included {ν1 ν2 : List ℕ} (h1 : IsPart ν1) (h2 : IsPart ν2) :
    ofRowLens ν1 h1.sortedGE ≤ ofRowLens ν2 h2.sortedGE ↔ Included ν1 ν2 := by
  rw [h1.included_iff_getD]
  constructor
  · intro hle i
    by_contra hc
    push Not at hc
    have hmem : (i, ν2.getD i 0) ∈ ofRowLens ν1 h1.sortedGE := by
      rw [mk_mem_ofRowLens h1]; omega
    have := hle hmem
    rw [mk_mem_ofRowLens h2] at this
    omega
  · intro hall x hx
    have hx' : (x.1, x.2) ∈ ofRowLens ν1 h1.sortedGE := hx
    rw [mk_mem_ofRowLens h1] at hx'
    exact show (x.1, x.2) ∈ ofRowLens ν2 h2.sortedGE from
      (mk_mem_ofRowLens h2 x.1 x.2).2 (lt_of_lt_of_le hx' (hall x.1))

/-- Two partitions with the same Young diagram are equal. -/
theorem eq_of_ofRowLens_eq {ν1 ν2 : List ℕ} (h1 : IsPart ν1) (h2 : IsPart ν2)
    (h : ofRowLens ν1 h1.sortedGE = ofRowLens ν2 h2.sortedGE) : ν1 = ν2 := by
  rw [← rowLens_ofRowLens_eq_self (hw := h1.sortedGE) h1.2,
    ← rowLens_ofRowLens_eq_self (hw := h2.sortedGE) h2.2, h]

/-- The list-based partitions of `n` are in bijection with the Young diagrams with `n`
boxes. -/
def listPartEquivYoungDiagramCard (n : ℕ) :
    {p : List ℕ // IsPart p ∧ p.sum = n} ≃ {μ : YoungDiagram // μ.card = n} where
  toFun p := ⟨ofRowLens p.1 p.2.1.sortedGE, by rw [card_ofRowLens_eq_sum p.2.1, p.2.2]⟩
  invFun μ := ⟨μ.1.rowLens, isPart_rowLens μ.1, by rw [← YoungDiagram.card_eq_sum_rowLens, μ.2]⟩
  left_inv p := Subtype.ext (rowLens_ofRowLens_eq_self (hw := p.2.1.sortedGE) p.2.1.2)
  right_inv μ := Subtype.ext YoungDiagram.ofRowLens_to_rowLens_eq_self

end Young
