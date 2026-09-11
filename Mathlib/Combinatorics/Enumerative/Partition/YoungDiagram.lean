/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.List.Multiset
public import Mathlib.Combinatorics.Enumerative.Partition.List.YoungDiagram

/-!
# Partitions of an integer and Young diagrams

`Nat.Partition n` is a multiset of positive parts summing to `n`; `YoungDiagram` is a finite
lower set of boxes.  This file relates the two: the Young diagram of a partition of `n` is the
diagram whose row lengths are the parts of the partition in decreasing order, and this is a
bijection onto the Young diagrams with `n` boxes.

## Main definitions

* `Nat.Partition.youngDiagram` : the Young diagram of a partition of `n`.
* `YoungDiagram.toNatPartition` : the partition of `μ.card` given by the row lengths of `μ`.
* `Nat.Partition.equivYoungDiagramCard` : **the partitions of `n` are the Young diagrams with
  `n` boxes**.

## Main results

* `Nat.Partition.card_youngDiagram` : the diagram of a partition of `n` has `n` boxes.
* `Nat.Partition.colLen_zero_youngDiagram` : its number of rows is the number of parts.
-/

@[expose] public section

open List Young YoungDiagram

namespace Nat.Partition

variable {n : ℕ}

/-- The Young diagram of a partition of `n`. -/
def youngDiagram (p : Partition n) : YoungDiagram :=
  ofRowLens p.partsList (isPart_partsList p).sortedGE

@[simp] lemma rowLens_youngDiagram (p : Partition n) : p.youngDiagram.rowLens = p.partsList :=
  rowLens_ofRowLens_eq_self (isPart_partsList p).2

@[simp] lemma rowLen_youngDiagram (p : Partition n) (r : ℕ) :
    p.youngDiagram.rowLen r = p.partsList.getD r 0 := by
  rw [← getD_rowLens, rowLens_youngDiagram]

@[simp] lemma mem_youngDiagram (p : Partition n) (r c : ℕ) :
    (r, c) ∈ p.youngDiagram ↔ c < p.partsList.getD r 0 :=
  mk_mem_ofRowLens (isPart_partsList p) r c

/-- A partition of `n` has a Young diagram with `n` boxes. -/
@[simp] theorem card_youngDiagram (p : Partition n) : p.youngDiagram.card = n := by
  rw [youngDiagram, card_ofRowLens_eq_sum (isPart_partsList p), sum_partsList]

/-- The number of rows of the Young diagram is the number of parts. -/
@[simp] theorem colLen_zero_youngDiagram (p : Partition n) :
    p.youngDiagram.colLen 0 = Multiset.card p.parts := by
  rw [youngDiagram, colLen_zero_ofRowLens (isPart_partsList p), length_partsList]

end Nat.Partition

namespace YoungDiagram

/-- The row lengths of a Young diagram, as a partition of its number of boxes. -/
def toNatPartition (μ : YoungDiagram) : Nat.Partition μ.card where
  parts := (μ.rowLens : Multiset ℕ)
  parts_pos hi := μ.pos_of_mem_rowLens _ (by simpa using hi)
  parts_sum := by rw [Multiset.sum_coe, ← YoungDiagram.card_eq_sum_rowLens]

@[simp] lemma parts_toNatPartition (μ : YoungDiagram) :
    μ.toNatPartition.parts = (μ.rowLens : Multiset ℕ) := rfl

@[simp] lemma partsList_toNatPartition (μ : YoungDiagram) :
    μ.toNatPartition.partsList = μ.rowLens :=
  sortDesc_coe (isPart_rowLens μ)

end YoungDiagram

namespace Nat.Partition

variable {n : ℕ}

lemma toNatPartition_youngDiagram (p : Partition n) :
    p.youngDiagram.toNatPartition.parts = p.parts := by
  rw [YoungDiagram.parts_toNatPartition, rowLens_youngDiagram, coe_partsList]

/-- **The partitions of `n` are the Young diagrams with `n` boxes.** -/
def equivYoungDiagramCard (n : ℕ) : Partition n ≃ {μ : YoungDiagram // μ.card = n} :=
  (listPartEquivNatPartition n).symm.trans (listPartEquivYoungDiagramCard n)

@[simp] lemma equivYoungDiagramCard_apply (p : Partition n) :
    (equivYoungDiagramCard n p : YoungDiagram) = p.youngDiagram := rfl

end Nat.Partition
