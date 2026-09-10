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
by the weakly decreasing list of its row lengths (`sh : List ℕ` with `Young.IsPart sh`),
and the box `(r, c)` belongs to that diagram when `Young.InShape sh (r, c)`, that is
`c < sh.getD r 0`.  Mathlib instead represents a Young diagram by the finite lower set of
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

* `Young.mem_youngDiagram` : the boxes of `Young.youngDiagram sh` are the boxes of `sh`.
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

variable {sh : List ℕ}

/-! ### The Young diagram of a partition -/

/-- A partition, as a weakly decreasing list, is a sorted list in Mathlib's sense. -/
lemma IsPart.sortedGE (h : IsPart sh) : sh.SortedGE :=
  ((isPart_iff_pairwise.1 h).1).sortedGE

/-- The list of row lengths of a Young diagram is a partition in the sense of Coq-Combi. -/
lemma isPart_rowLens (mu : YoungDiagram) : IsPart mu.rowLens :=
  isPart_iff_pairwise.2
    ⟨mu.rowLens_sorted.pairwise, fun hc => absurd (mu.pos_of_mem_rowLens 0 hc) (lt_irrefl 0)⟩

/-- The Young diagram of a partition given by its list of row lengths. -/
def youngDiagram (sh : List ℕ) (h : IsPart sh) : YoungDiagram :=
  YoungDiagram.ofRowLens sh h.sortedGE

/-- The Young diagram only depends on the list of row lengths. -/
lemma youngDiagram_congr {sh1 sh2 : List ℕ} (h1 : IsPart sh1) (h2 : IsPart sh2)
    (h : sh1 = sh2) : youngDiagram sh1 h1 = youngDiagram sh2 h2 := by
  subst h; rfl

/-- The boxes of `youngDiagram sh` are exactly the boxes of the shape `sh`. -/
@[simp] theorem mem_youngDiagram (h : IsPart sh) (rc : ℕ × ℕ) :
    rc ∈ youngDiagram sh h ↔ InShape sh rc := by
  rw [youngDiagram, YoungDiagram.mem_ofRowLens, InShape]
  constructor
  · rintro ⟨hlt, hc⟩
    rwa [List.getD_eq_getElem _ _ hlt]
  · intro hc
    have hlt : rc.1 < sh.length := by
      by_contra hr
      rw [List.getD_eq_default _ _ (not_lt.1 hr)] at hc
      exact absurd hc (by simp)
    exact ⟨hlt, by rwa [List.getD_eq_getElem _ _ hlt] at hc⟩

theorem mk_mem_youngDiagram (h : IsPart sh) (r c : ℕ) :
    (r, c) ∈ youngDiagram sh h ↔ c < sh.getD r 0 :=
  mem_youngDiagram h (r, c)

/-- The `i`-th row length of the Young diagram of `sh` is the `i`-th part of `sh`. -/
@[simp] theorem rowLen_youngDiagram (h : IsPart sh) (i : ℕ) :
    (youngDiagram sh h).rowLen i = sh.getD i 0 := by
  refine Nat.le_antisymm ?_ ?_
  · by_contra hc
    have hmem : (i, sh.getD i 0) ∈ youngDiagram sh h :=
      YoungDiagram.mem_iff_lt_rowLen.2 (by omega)
    rw [mk_mem_youngDiagram] at hmem
    omega
  · by_contra hc
    have hmem : (i, (youngDiagram sh h).rowLen i) ∈ youngDiagram sh h := by
      rw [mk_mem_youngDiagram]; omega
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.1 hmem) (lt_irrefl _)

/-- The list of row lengths of the Young diagram of `sh` is `sh` itself. -/
@[simp] theorem rowLens_youngDiagram (h : IsPart sh) : (youngDiagram sh h).rowLens = sh :=
  YoungDiagram.rowLens_ofRowLens_eq_self fun _ hx => h.pos_of_mem hx

/-- Conversely, the Young diagram of the row lengths of `mu` is `mu`. -/
@[simp] theorem youngDiagram_rowLens (mu : YoungDiagram) :
    youngDiagram mu.rowLens (isPart_rowLens mu) = mu :=
  YoungDiagram.ofRowLens_to_rowLens_eq_self

/-- The number of nonempty rows of the Young diagram of `sh` is the number of parts. -/
theorem colLen_zero_youngDiagram (h : IsPart sh) :
    (youngDiagram sh h).colLen 0 = sh.length := by
  rw [← YoungDiagram.length_rowLens, rowLens_youngDiagram]

/-- The `j`-th column length of the Young diagram of `sh` is the `j`-th part of the
conjugate partition. -/
@[simp] theorem colLen_youngDiagram (h : IsPart sh) (j : ℕ) :
    (youngDiagram sh h).colLen j = (conjPart sh).getD j 0 := by
  refine Nat.le_antisymm ?_ ?_
  · by_contra hc
    have hmem : ((conjPart sh).getD j 0, j) ∈ youngDiagram sh h :=
      YoungDiagram.mem_iff_lt_colLen.2 (by omega)
    rw [mk_mem_youngDiagram] at hmem
    exact absurd ((inShape_conjPart h ((conjPart sh).getD j 0) j).1 hmem) (lt_irrefl _)
  · by_contra hc
    have hmem : InShape (conjPart sh) (j, (youngDiagram sh h).colLen j) := by
      simp only [InShape]; omega
    have hin : ((youngDiagram sh h).colLen j, j) ∈ youngDiagram sh h := by
      rw [mk_mem_youngDiagram]
      exact (inShape_conjPart h _ j).2 hmem
    exact absurd (YoungDiagram.mem_iff_lt_colLen.1 hin) (lt_irrefl _)

/-- The number of boxes of the Young diagram of `sh` is the size of `sh`. -/
@[simp] theorem card_youngDiagram (h : IsPart sh) : (youngDiagram sh h).card = sh.sum :=
  YoungDiagram.card_cellsOfRowLens sh

/-- The column lengths of a Young diagram are the parts of the conjugate of its list of
row lengths. -/
theorem colLen_eq_getD_conjPart (mu : YoungDiagram) (j : ℕ) :
    mu.colLen j = (conjPart mu.rowLens).getD j 0 := by
  conv_lhs => rw [← youngDiagram_rowLens mu]
  exact colLen_youngDiagram (isPart_rowLens mu) j

/-! ### Conjugation is transposition -/

/-- **Conjugation of shapes is transposition of Young diagrams**: the Coq-Combi
`conj_part` corresponds to Mathlib's `YoungDiagram.transpose`. -/
theorem transpose_youngDiagram (h : IsPart sh) :
    (youngDiagram sh h).transpose = youngDiagram (conjPart sh) (isPart_conjPart h) := by
  ext ⟨r, c⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_transpose, Prod.swap_prod_mk,
    mk_mem_youngDiagram]
  simpa [InShape] using inShape_conjPart h c r

/-! ### Inclusion is containment -/

/-- **Inclusion of shapes is containment of Young diagrams.** -/
theorem youngDiagram_le_iff {sh1 sh2 : List ℕ} (h1 : IsPart sh1) (h2 : IsPart sh2) :
    youngDiagram sh1 h1 ≤ youngDiagram sh2 h2 ↔ Included sh1 sh2 := by
  rw [h1.included_iff_getD]
  constructor
  · intro hle i
    by_contra hc
    push Not at hc
    have hmem : (i, sh2.getD i 0) ∈ youngDiagram sh1 h1 := by
      rw [mk_mem_youngDiagram]; omega
    have := hle hmem
    rw [mk_mem_youngDiagram] at this
    omega
  · intro hall x hx
    have hx' : (x.1, x.2) ∈ youngDiagram sh1 h1 := hx
    rw [mk_mem_youngDiagram] at hx'
    exact show (x.1, x.2) ∈ youngDiagram sh2 h2 from
      (mk_mem_youngDiagram h2 x.1 x.2).2 (lt_of_lt_of_le hx' (hall x.1))

/-- Two partitions with the same Young diagram are equal. -/
theorem youngDiagram_injective {sh1 sh2 : List ℕ} (h1 : IsPart sh1) (h2 : IsPart sh2)
    (h : youngDiagram sh1 h1 = youngDiagram sh2 h2) : sh1 = sh2 := by
  rw [← rowLens_youngDiagram h1, ← rowLens_youngDiagram h2, h]

/-- **Partitions are Young diagrams**: the shapes of Coq-Combi are in bijection with
Mathlib's Young diagrams. -/
def partEquivYoungDiagram : {sh : List ℕ // IsPart sh} ≃ YoungDiagram where
  toFun sh := youngDiagram sh.1 sh.2
  invFun mu := ⟨mu.rowLens, isPart_rowLens mu⟩
  left_inv sh := Subtype.ext (rowLens_youngDiagram sh.2)
  right_inv mu := youngDiagram_rowLens mu

@[simp] lemma partEquivYoungDiagram_apply (sh : {sh : List ℕ // IsPart sh}) :
    partEquivYoungDiagram sh = youngDiagram sh.1 sh.2 := rfl

@[simp] lemma partEquivYoungDiagram_symm_apply (mu : YoungDiagram) :
    (partEquivYoungDiagram.symm mu : List ℕ) = mu.rowLens := rfl

/-- The bijection between partitions and Young diagrams exchanges inclusion of shapes and
containment of Young diagrams. -/
theorem partEquivYoungDiagram_le_iff (sh1 sh2 : {sh : List ℕ // IsPart sh}) :
    partEquivYoungDiagram sh1 ≤ partEquivYoungDiagram sh2 ↔ Included sh1.1 sh2.1 :=
  youngDiagram_le_iff sh1.2 sh2.2

/-- The list-based partitions of `n` are in bijection with the Young diagrams with `n`
boxes. -/
def listPartEquivYoungDiagramCard (n : ℕ) :
    {p : List ℕ // IsPart p ∧ p.sum = n} ≃ {mu : YoungDiagram // mu.card = n} where
  toFun p := ⟨youngDiagram p.1 p.2.1, by rw [card_youngDiagram, p.2.2]⟩
  invFun mu := ⟨mu.1.rowLens, isPart_rowLens mu.1, by rw [← YoungDiagram.card_eq_sum_rowLens, mu.2]⟩
  left_inv p := Subtype.ext (rowLens_youngDiagram p.2.1)
  right_inv mu := Subtype.ext (youngDiagram_rowLens mu.1)

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
def equivYoungDiagramCard (n : ℕ) : Partition n ≃ {mu : YoungDiagram // mu.card = n} :=
  (listPartEquivNatPartition n).symm.trans (listPartEquivYoungDiagramCard n)

@[simp] lemma equivYoungDiagramCard_apply (p : Partition n) :
    (equivYoungDiagramCard n p : YoungDiagram) = p.youngDiagram := rfl

end Nat.Partition
