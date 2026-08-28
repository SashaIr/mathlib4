/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Shape.MultisetPartition
import Mathlib.Combinatorics.Young.Shape.YoungDiagram

/-!
# Partitions as multisets, as lists, and as Young diagrams

`Mathlib.Combinatorics.Young.Shape.MultisetPartition` encodes a partition of an unspecified
size as a multiset of positive integers (`MultisetPart.Partition`).  This file identifies that
encoding with the other three representations used in this library and in Mathlib: the weakly
decreasing lists of Coq-Combi, Mathlib's `Nat.Partition n`, and Mathlib's `YoungDiagram`.

## Main definitions

* `MultisetPart.Partition.partsList` : the parts, listed in decreasing order.
* `MultisetPart.equivListPart` : multiset partitions are the list partitions.
* `MultisetPart.equivYoungDiagram` : multiset partitions are the Young diagrams.
* `MultisetPart.equivNatPartition` : the multiset partitions of size `n` are
  Mathlib's partitions of `n`.
-/

namespace MultisetPart

open List

/-- The parts of a multiset partition, listed in weakly decreasing order. -/
def Partition.partsList (l : Partition) : List ℕ := sortDesc l.parts

lemma Partition.isPart_partsList (l : Partition) : IsPart l.partsList :=
  isPart_sortDesc fun _ hi => l.parts_pos hi

@[simp] lemma Partition.coe_partsList (l : Partition) :
    (l.partsList : Multiset ℕ) = l.parts := coe_sortDesc _

@[simp] lemma Partition.sum_partsList (l : Partition) : l.partsList.sum = l.size :=
  sum_sortDesc _

/-- **Multiset partitions are list partitions**: sorting the parts in decreasing order is a
bijection onto the weakly decreasing lists of positive integers. -/
def equivListPart : Partition ≃ {sh : List ℕ // IsPart sh} where
  toFun l := ⟨l.partsList, l.isPart_partsList⟩
  invFun sh := ⟨(sh.1 : Multiset ℕ), fun hi => sh.2.pos_of_mem hi⟩
  left_inv l := Partition.ext l.coe_partsList
  right_inv sh := Subtype.ext (sortDesc_coe sh.2)

@[simp] lemma equivListPart_apply (l : Partition) : (equivListPart l : List ℕ) = l.partsList :=
  rfl

@[simp] lemma equivListPart_symm_apply (sh : {sh : List ℕ // IsPart sh}) :
    (equivListPart.symm sh).parts = (sh.1 : Multiset ℕ) := rfl

/-- **Multiset partitions are Young diagrams.** -/
def equivYoungDiagram : Partition ≃ YoungDiagram :=
  equivListPart.trans partEquivYoungDiagram

@[simp] lemma equivYoungDiagram_apply (l : Partition) :
    equivYoungDiagram l = youngDiagram l.partsList l.isPart_partsList := rfl

/-- The size of a multiset partition is the number of boxes of its Young diagram. -/
lemma card_equivYoungDiagram (l : Partition) :
    (equivYoungDiagram l).card = l.size := by
  rw [equivYoungDiagram_apply, card_youngDiagram, Partition.sum_partsList]

/-- **The multiset partitions of size `n` are Mathlib's partitions of `n`.** -/
def equivNatPartition (n : ℕ) : {l : Partition // l.size = n} ≃ Nat.Partition n where
  toFun l :=
    { parts := l.1.parts
      parts_pos := fun hi => l.1.parts_pos hi
      parts_sum := l.2 }
  invFun p := ⟨⟨p.parts, fun hi => p.parts_pos hi⟩, p.parts_sum⟩
  left_inv _ := Subtype.ext (Partition.ext rfl)
  right_inv _ := Nat.Partition.ext rfl

@[simp] lemma equivNatPartition_apply (n : ℕ) (l : {l : Partition // l.size = n}) :
    (equivNatPartition n l).parts = l.1.parts := rfl

end MultisetPart
