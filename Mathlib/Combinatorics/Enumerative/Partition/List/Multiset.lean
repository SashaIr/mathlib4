/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.List.Basic

/-!
# Comparison with Mathlib's partitions

The Coq-Combi development represents an integer partition as a weakly decreasing list of positive
integers, and this is the representation used in
`Mathlib.Combinatorics.Enumerative.Partition.List.Basic`.
Mathlib instead uses a multiset of positive integers (`Nat.Partition`).

This file provides the dictionary between the two: sorting a multiset in decreasing order
is a bijection from Mathlib's partitions of `n` onto the list-based partitions of `n`.

## Main definitions

* `Young.sortDesc` : the parts of a multiset of naturals, in weakly decreasing order.
* `Nat.Partition.partsList` : the parts of a partition of `n`, as a weakly decreasing list.

## Main results

* `Young.isPart_sortDesc`, `Young.sortDesc_coe` : sorting in decreasing order produces a
  partition, and it is the identity on partitions.
* `Young.listPartEquivNatPartition` : the list-based partitions of `n` are in bijection
  with `Nat.Partition n`.
* `Nat.Partition.isPart_partsList` : the list of parts of a partition of `n` is a partition
  in the sense of the list model.
-/

@[expose] public section

namespace Young

open List

/-- The parts of a multiset of naturals, listed in weakly decreasing order. -/
def sortDesc (m : Multiset ℕ) : List ℕ := m.sort (· ≥ ·)

@[simp] lemma coe_sortDesc (m : Multiset ℕ) : (sortDesc m : Multiset ℕ) = m :=
  Multiset.sort_eq _ _

@[simp] lemma mem_sortDesc {m : Multiset ℕ} {i : ℕ} : i ∈ sortDesc m ↔ i ∈ m :=
  Multiset.mem_sort _

lemma pairwise_sortDesc (m : Multiset ℕ) : List.Pairwise (· ≥ ·) (sortDesc m) :=
  Multiset.pairwise_sort _ _

/-- Being a partition means being weakly decreasing without zero parts. -/
lemma isPart_iff_pairwise {l : List ℕ} :
    IsPart l ↔ List.Pairwise (· ≥ ·) l ∧ (0 : ℕ) ∉ l := by
  rw [isPart_iff_chain, List.isChain_iff_pairwise]

/-- Sorting a multiset of positive integers in decreasing order gives a partition. -/
lemma isPart_sortDesc {m : Multiset ℕ} (h : ∀ i ∈ m, 0 < i) : IsPart (sortDesc m) := by
  rw [isPart_iff_pairwise]
  refine ⟨pairwise_sortDesc m, fun hc => ?_⟩
  exact absurd (h 0 (mem_sortDesc.1 hc)) (lt_irrefl 0)

/-- Sorting the parts of a partition in decreasing order gives back the partition. -/
lemma sortDesc_coe {l : List ℕ} (h : IsPart l) : sortDesc (l : Multiset ℕ) = l := by
  refine List.Perm.eq_of_pairwise (le := (· ≥ ·)) (fun a b _ _ hab hba => le_antisymm hba hab)
    (pairwise_sortDesc _) ((isPart_iff_pairwise.1 h).1) ?_
  exact Quotient.exact (coe_sortDesc (l : Multiset ℕ))

@[simp] lemma sum_sortDesc (m : Multiset ℕ) : (sortDesc m).sum = m.sum := by
  conv_rhs => rw [← coe_sortDesc m]
  exact (Multiset.sum_coe _).symm

/-- Mathlib's partitions of `n` and the list-based partitions of `n` of Coq-Combi
correspond to each other by sorting the parts in decreasing order. -/
def listPartEquivNatPartition (n : ℕ) :
    {p : List ℕ // IsPart p ∧ p.sum = n} ≃ Nat.Partition n where
  toFun p :=
    { parts := (p.1 : Multiset ℕ)
      parts_pos := fun {i} hi => p.2.1.pos_of_mem hi
      parts_sum := by rw [Multiset.sum_coe]; exact p.2.2 }
  invFun q := ⟨sortDesc q.parts, isPart_sortDesc fun _ hi => q.parts_pos hi, by
    rw [sum_sortDesc, q.parts_sum]⟩
  left_inv p := Subtype.ext (sortDesc_coe p.2.1)
  right_inv q := Nat.Partition.ext (by simp)

@[simp] lemma listPartEquivNatPartition_apply {n : ℕ} (p : {p : List ℕ // IsPart p ∧ p.sum = n}) :
    (listPartEquivNatPartition n p).parts = (p.1 : Multiset ℕ) := rfl

/-- Transferring Mathlib's finiteness of the set of partitions of `n`. -/
instance fintypeListPart (n : ℕ) : Fintype {p : List ℕ // IsPart p ∧ p.sum = n} :=
  Fintype.ofEquiv _ (listPartEquivNatPartition n).symm

lemma card_listPart (n : ℕ) :
    Fintype.card {p : List ℕ // IsPart p ∧ p.sum = n} = Fintype.card (Nat.Partition n) :=
  Fintype.card_congr (listPartEquivNatPartition n)

end Young

namespace Nat.Partition

open List Young

variable {n : ℕ}

/-- The parts of a partition of `n`, listed in weakly decreasing order. -/
def partsList (p : Partition n) : List ℕ := sortDesc p.parts

lemma isPart_partsList (p : Partition n) : IsPart p.partsList :=
  isPart_sortDesc fun _ hi => p.parts_pos hi

@[simp] lemma coe_partsList (p : Partition n) : (p.partsList : Multiset ℕ) = p.parts :=
  coe_sortDesc _

@[simp] lemma sum_partsList (p : Partition n) : p.partsList.sum = n := by
  rw [partsList, sum_sortDesc, p.parts_sum]

@[simp] lemma mem_partsList {p : Partition n} {i : ℕ} : i ∈ p.partsList ↔ i ∈ p.parts :=
  mem_sortDesc

@[simp] lemma length_partsList (p : Partition n) :
    p.partsList.length = Multiset.card p.parts := by
  rw [← coe_partsList p, Multiset.coe_card]

lemma length_partsList_le (p : Partition n) : p.partsList.length ≤ n :=
  (isPart_partsList p).length_le_sum.trans (le_of_eq (sum_partsList p))

@[simp] lemma partsList_eq_nil_iff {p : Partition n} : p.partsList = [] ↔ n = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← sum_partsList p, h, List.sum_nil]
  · subst h
    exact (isPart_partsList p).eq_nil_of_sum_eq_zero (sum_partsList p)

/-- The partition of `n` whose parts are the entries of a weakly decreasing list of
positive integers summing to `n`. -/
def ofList (l : List ℕ) (h : IsPart l) (hs : l.sum = n) : Partition n :=
  listPartEquivNatPartition n ⟨l, h, hs⟩

@[simp] lemma parts_ofList {l : List ℕ} (h : IsPart l) (hs : l.sum = n) :
    (ofList l h hs).parts = (l : Multiset ℕ) := rfl

@[simp] lemma partsList_ofList {l : List ℕ} (h : IsPart l) (hs : l.sum = n) :
    (ofList l h hs).partsList = l :=
  sortDesc_coe h

/-- The partition of `n` with the single part `n` has `[n]` as its list of parts. -/
@[simp] lemma partsList_indiscrete (hn : n ≠ 0) : (indiscrete n).partsList = [n] := by
  rw [partsList, indiscrete_parts hn]
  exact sortDesc_coe (isPart_cons.2 ⟨by simpa using Nat.one_le_iff_ne_zero.2 hn, isPart_nil⟩)

lemma partsList_injective : Function.Injective (partsList : Partition n → List ℕ) := by
  intro p q h
  refine Partition.ext ?_
  rw [← coe_partsList p, ← coe_partsList q, h]

@[simp] lemma partsList_inj {p q : Partition n} : p.partsList = q.partsList ↔ p = q :=
  partsList_injective.eq_iff

@[simp] lemma ofList_partsList (p : Partition n) :
    ofList p.partsList (isPart_partsList p) (sum_partsList p) = p :=
  partsList_injective (by simp)

end Nat.Partition
