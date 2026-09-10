/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Shape.Included
public import Mathlib.Combinatorics.Young.Shape.NatPartitionConj
public import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# Shapes and Mathlib's Young diagrams

The Coq-Combi development, and therefore this port, represents the shape of a Young diagram
by the weakly decreasing list of its row lengths (`ν : List ℕ` with `Young.IsPart ν`),
and the box `(r, c)` belongs to that diagram when `Young.InShape ν (r, c)`, that is
`c < ν.getD r 0`.  Mathlib instead represents a Young diagram by the finite lower set of
its boxes (`YoungDiagram`).

This file is the dictionary between the two.  It translates every basic notion of the
Coq-Combi side (parts, size, number of parts, conjugate, inclusion) into the corresponding
Mathlib notion (`YoungDiagram.rowLen`, `YoungDiagram.card`, `YoungDiagram.colLen`,
`YoungDiagram.transpose`, `≤`), and packages the translation as a bijection.  It also
connects both with Mathlib's `Nat.Partition`.

## Main definitions

* `Young.youngDiagram` : the Young diagram of a partition, as a `YoungDiagram`.
* `Young.partEquivYoungDiagram` : partitions are in bijection with Young diagrams.
* `Nat.Partition.youngDiagram` : the Young diagram of a partition of `n` in Mathlib's sense.
* `Nat.Partition.equivYoungDiagramCard` : the partitions of `n` are in bijection with the
  Young diagrams with `n` boxes.

## Main results

* `Young.mem_youngDiagram` : the boxes of `Young.youngDiagram ν` are the boxes of `ν`.
* `Young.rowLen_youngDiagram`, `Young.rowLens_youngDiagram` : rows and row lengths.
* `Young.colLen_youngDiagram` : the column lengths are the parts of the conjugate.
* `Young.card_youngDiagram` : the number of boxes is the size of the partition.
* `Young.transpose_youngDiagram` : `Young.conjPart` is Mathlib's `YoungDiagram.transpose`.
* `Young.youngDiagram_le_iff` : `Young.Included` is the containment order on Young diagrams.
* `Nat.Partition.youngDiagram_conj` : the conjugate of `Nat.Partition` is the transpose.
-/

@[expose] public section

namespace Young

open List

variable {ν : List ℕ}

/-! ### The Young diagram of a partition -/

/-- A partition, as a weakly decreasing list, is a sorted list in Mathlib's sense. -/
lemma IsPart.sortedGE (h : IsPart ν) : ν.SortedGE :=
  ((isPart_iff_pairwise.1 h).1).sortedGE

/-- The list of row lengths of a Young diagram is a partition in the sense of Coq-Combi. -/
lemma isPart_rowLens (μ : YoungDiagram) : IsPart μ.rowLens :=
  isPart_iff_pairwise.2
    ⟨μ.rowLens_sorted.pairwise, fun hc => absurd (μ.pos_of_mem_rowLens 0 hc) (lt_irrefl 0)⟩

/-- The Young diagram of a partition given by its list of row lengths. -/
def youngDiagram (ν : List ℕ) (h : IsPart ν) : YoungDiagram :=
  YoungDiagram.ofRowLens ν h.sortedGE

/-- The Young diagram only depends on the list of row lengths. -/
lemma youngDiagram_congr {ν1 ν2 : List ℕ} (h1 : IsPart ν1) (h2 : IsPart ν2)
    (h : ν1 = ν2) : youngDiagram ν1 h1 = youngDiagram ν2 h2 := by
  subst h; rfl

/-- The boxes of `youngDiagram ν` are exactly the boxes of the shape `ν`. -/
@[simp] theorem mem_youngDiagram (h : IsPart ν) (rc : ℕ × ℕ) :
    rc ∈ youngDiagram ν h ↔ InShape ν rc := by
  rw [youngDiagram, YoungDiagram.mem_ofRowLens, InShape]
  constructor
  · rintro ⟨hlt, hc⟩
    rwa [List.getD_eq_getElem _ _ hlt]
  · intro hc
    have hlt : rc.1 < ν.length := by
      by_contra hr
      rw [List.getD_eq_default _ _ (not_lt.1 hr)] at hc
      exact absurd hc (by simp)
    exact ⟨hlt, by rwa [List.getD_eq_getElem _ _ hlt] at hc⟩

theorem mk_mem_youngDiagram (h : IsPart ν) (r c : ℕ) :
    (r, c) ∈ youngDiagram ν h ↔ c < ν.getD r 0 :=
  mem_youngDiagram h (r, c)

/-- The `i`-th row length of the Young diagram of `ν` is the `i`-th part of `ν`. -/
@[simp] theorem rowLen_youngDiagram (h : IsPart ν) (i : ℕ) :
    (youngDiagram ν h).rowLen i = ν.getD i 0 := by
  refine Nat.le_antisymm ?_ ?_
  · by_contra hc
    have hmem : (i, ν.getD i 0) ∈ youngDiagram ν h :=
      YoungDiagram.mem_iff_lt_rowLen.2 (by omega)
    rw [mk_mem_youngDiagram] at hmem
    omega
  · by_contra hc
    have hmem : (i, (youngDiagram ν h).rowLen i) ∈ youngDiagram ν h := by
      rw [mk_mem_youngDiagram]; omega
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.1 hmem) (lt_irrefl _)

/-- The list of row lengths of the Young diagram of `ν` is `ν` itself. -/
@[simp] theorem rowLens_youngDiagram (h : IsPart ν) : (youngDiagram ν h).rowLens = ν :=
  YoungDiagram.rowLens_ofRowLens_eq_self fun _ hx => h.pos_of_mem hx

/-- Conversely, the Young diagram of the row lengths of `μ` is `μ`. -/
@[simp] theorem youngDiagram_rowLens (μ : YoungDiagram) :
    youngDiagram μ.rowLens (isPart_rowLens μ) = μ :=
  YoungDiagram.ofRowLens_to_rowLens_eq_self

/-- The number of nonempty rows of the Young diagram of `ν` is the number of parts. -/
theorem colLen_zero_youngDiagram (h : IsPart ν) :
    (youngDiagram ν h).colLen 0 = ν.length := by
  rw [← YoungDiagram.length_rowLens, rowLens_youngDiagram]

/-- The `j`-th column length of the Young diagram of `ν` is the `j`-th part of the
conjugate partition. -/
@[simp] theorem colLen_youngDiagram (h : IsPart ν) (j : ℕ) :
    (youngDiagram ν h).colLen j = (conjPart ν).getD j 0 := by
  refine Nat.le_antisymm ?_ ?_
  · by_contra hc
    have hmem : ((conjPart ν).getD j 0, j) ∈ youngDiagram ν h :=
      YoungDiagram.mem_iff_lt_colLen.2 (by omega)
    rw [mk_mem_youngDiagram] at hmem
    exact absurd ((inShape_conjPart h ((conjPart ν).getD j 0) j).1 hmem) (lt_irrefl _)
  · by_contra hc
    have hmem : InShape (conjPart ν) (j, (youngDiagram ν h).colLen j) := by
      simp only [InShape]; omega
    have hin : ((youngDiagram ν h).colLen j, j) ∈ youngDiagram ν h := by
      rw [mk_mem_youngDiagram]
      exact (inShape_conjPart h _ j).2 hmem
    exact absurd (YoungDiagram.mem_iff_lt_colLen.1 hin) (lt_irrefl _)

/-- The number of boxes of the Young diagram of `ν` is the size of `ν`. -/
@[simp] theorem card_youngDiagram (h : IsPart ν) : (youngDiagram ν h).card = ν.sum :=
  YoungDiagram.card_cellsOfRowLens ν

/-- The column lengths of a Young diagram are the parts of the conjugate of its list of
row lengths. -/
theorem colLen_eq_getD_conjPart (μ : YoungDiagram) (j : ℕ) :
    μ.colLen j = (conjPart μ.rowLens).getD j 0 := by
  conv_lhs => rw [← youngDiagram_rowLens μ]
  exact colLen_youngDiagram (isPart_rowLens μ) j

/-! ### Conjugation is transposition -/

/-- **Conjugation of shapes is transposition of Young diagrams**: the Coq-Combi
`conj_part` corresponds to Mathlib's `YoungDiagram.transpose`. -/
theorem transpose_youngDiagram (h : IsPart ν) :
    (youngDiagram ν h).transpose = youngDiagram (conjPart ν) (isPart_conjPart h) := by
  ext ⟨r, c⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_transpose, Prod.swap_prod_mk,
    mk_mem_youngDiagram]
  simpa [InShape] using inShape_conjPart h c r

/-! ### Inclusion is containment -/

/-- **Inclusion of shapes is containment of Young diagrams.** -/
theorem youngDiagram_le_iff {ν1 ν2 : List ℕ} (h1 : IsPart ν1) (h2 : IsPart ν2) :
    youngDiagram ν1 h1 ≤ youngDiagram ν2 h2 ↔ Included ν1 ν2 := by
  rw [h1.included_iff_getD]
  constructor
  · intro hle i
    by_contra hc
    push Not at hc
    have hmem : (i, ν2.getD i 0) ∈ youngDiagram ν1 h1 := by
      rw [mk_mem_youngDiagram]; omega
    have := hle hmem
    rw [mk_mem_youngDiagram] at this
    omega
  · intro hall x hx
    have hx' : (x.1, x.2) ∈ youngDiagram ν1 h1 := hx
    rw [mk_mem_youngDiagram] at hx'
    exact show (x.1, x.2) ∈ youngDiagram ν2 h2 from
      (mk_mem_youngDiagram h2 x.1 x.2).2 (lt_of_lt_of_le hx' (hall x.1))

/-- Two partitions with the same Young diagram are equal. -/
theorem youngDiagram_injective {ν1 ν2 : List ℕ} (h1 : IsPart ν1) (h2 : IsPart ν2)
    (h : youngDiagram ν1 h1 = youngDiagram ν2 h2) : ν1 = ν2 := by
  rw [← rowLens_youngDiagram h1, ← rowLens_youngDiagram h2, h]

/-- **Partitions are Young diagrams**: the shapes of Coq-Combi are in bijection with
Mathlib's Young diagrams. -/
def partEquivYoungDiagram : {ν : List ℕ // IsPart ν} ≃ YoungDiagram where
  toFun ν := youngDiagram ν.1 ν.2
  invFun μ := ⟨μ.rowLens, isPart_rowLens μ⟩
  left_inv ν := Subtype.ext (rowLens_youngDiagram ν.2)
  right_inv μ := youngDiagram_rowLens μ

@[simp] lemma partEquivYoungDiagram_apply (ν : {ν : List ℕ // IsPart ν}) :
    partEquivYoungDiagram ν = youngDiagram ν.1 ν.2 := rfl

@[simp] lemma partEquivYoungDiagram_symm_apply (μ : YoungDiagram) :
    (partEquivYoungDiagram.symm μ : List ℕ) = μ.rowLens := rfl

/-- The bijection between partitions and Young diagrams exchanges inclusion of shapes and
containment of Young diagrams. -/
theorem partEquivYoungDiagram_le_iff (ν1 ν2 : {ν : List ℕ // IsPart ν}) :
    partEquivYoungDiagram ν1 ≤ partEquivYoungDiagram ν2 ↔ Included ν1.1 ν2.1 :=
  youngDiagram_le_iff ν1.2 ν2.2

/-- The list-based partitions of `n` are in bijection with the Young diagrams with `n`
boxes. -/
def listPartEquivYoungDiagramCard (n : ℕ) :
    {p : List ℕ // IsPart p ∧ p.sum = n} ≃ {μ : YoungDiagram // μ.card = n} where
  toFun p := ⟨youngDiagram p.1 p.2.1, by rw [card_youngDiagram, p.2.2]⟩
  invFun μ := ⟨μ.1.rowLens, isPart_rowLens μ.1, by rw [← YoungDiagram.card_eq_sum_rowLens, μ.2]⟩
  left_inv p := Subtype.ext (rowLens_youngDiagram p.2.1)
  right_inv μ := Subtype.ext (youngDiagram_rowLens μ.1)

end Young

/-! ### Mathlib's partitions of an integer -/

namespace Nat.Partition

open List Young

variable {n : ℕ}

/-- The Young diagram of a partition of `n`. -/
def youngDiagram (p : Partition n) : YoungDiagram :=
  Young.youngDiagram p.partsList (isPart_partsList p)

@[simp] lemma rowLens_youngDiagram (p : Partition n) : p.youngDiagram.rowLens = p.partsList :=
  Young.rowLens_youngDiagram _

@[simp] lemma mem_youngDiagram (p : Partition n) (r c : ℕ) :
    (r, c) ∈ p.youngDiagram ↔ c < p.partsList.getD r 0 :=
  Young.mk_mem_youngDiagram _ r c

/-- A partition of `n` has a Young diagram with `n` boxes. -/
@[simp] theorem card_youngDiagram (p : Partition n) : p.youngDiagram.card = n := by
  rw [youngDiagram, Young.card_youngDiagram, sum_partsList]

/-- The number of rows of the Young diagram is the number of parts. -/
@[simp] theorem colLen_zero_youngDiagram (p : Partition n) :
    p.youngDiagram.colLen 0 = Multiset.card p.parts := by
  rw [youngDiagram, Young.colLen_zero_youngDiagram, length_partsList]

/-- **Conjugation of partitions is transposition of Young diagrams.** -/
@[simp] theorem youngDiagram_conj (p : Partition n) :
    p.conj.youngDiagram = p.youngDiagram.transpose := by
  rw [youngDiagram, youngDiagram, transpose_youngDiagram]
  exact youngDiagram_congr _ _ (partsList_conj p)

/-- **The partitions of `n` are the Young diagrams with `n` boxes.** -/
def equivYoungDiagramCard (n : ℕ) : Partition n ≃ {μ : YoungDiagram // μ.card = n} :=
  (listPartEquivNatPartition n).symm.trans (listPartEquivYoungDiagramCard n)

@[simp] lemma equivYoungDiagramCard_apply (p : Partition n) :
    (equivYoungDiagramCard n p : YoungDiagram) = p.youngDiagram := rfl

end Nat.Partition
