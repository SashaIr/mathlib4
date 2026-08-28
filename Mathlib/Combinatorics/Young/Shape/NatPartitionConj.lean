/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Shape.ConjugateEquiv
import Mathlib.Combinatorics.Young.Shape.NatPartition
import Mathlib.Combinatorics.Young.Shape.Dominance

/-!
# Conjugation of Mathlib's integer partitions

Transporting the conjugation of partitions of `Mathlib.Combinatorics.Young.Shape.Conjugate`
(the Lean 4 port of `conj_part` of [Coq-Combi](https://github.com/math-comp/Coq-Combi)) along the
dictionary of `Mathlib.Combinatorics.Young.Shape.NatPartition` equips Mathlib's
`Nat.Partition n` with a conjugation: the parts of `p.conj` are the column lengths of the Young
diagram of `p`.

## Main definitions

* `Nat.Partition.conj` : the conjugate partition.
* `Nat.Partition.Partdom` : the dominance order on `Nat.Partition n`.

## Main results

* `Nat.Partition.conj_conj` : conjugation is an involution.
* `Nat.Partition.card_parts_conj_le_iff`, `Nat.Partition.forall_mem_parts_conj_le_iff` :
  conjugation exchanges the number of parts and the size of the largest part.
* `Nat.Partition.conjEquivLengthLe` : the partitions of `n` with at most `k` parts are in
  bijection with the partitions of `n` whose parts are all at most `k`.
* `Nat.Partition.partdom_conj_iff` : conjugation reverses the dominance order.
-/

namespace Nat.Partition

open List

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

/-- The conjugate of a partition: the `i`-th part of `p.conj` is the number of parts of
`p` which are larger than `i`. -/
def conj (p : Partition n) : Partition n where
  parts := (conjPart p.partsList : Multiset ℕ)
  parts_pos := fun {i} hi =>
    (isPart_conjPart (isPart_partsList p)).pos_of_mem (by simpa using hi)
  parts_sum := by
    rw [Multiset.sum_coe, sum_conjPart, sum_partsList]

@[simp] lemma parts_conj (p : Partition n) :
    p.conj.parts = (conjPart p.partsList : Multiset ℕ) := rfl

@[simp] lemma partsList_conj (p : Partition n) : p.conj.partsList = conjPart p.partsList := by
  change sortDesc p.conj.parts = _
  rw [parts_conj, sortDesc_coe (isPart_conjPart (isPart_partsList p))]

/-- Conjugation is an involution. -/
@[simp] theorem conj_conj (p : Partition n) : p.conj.conj = p := by
  refine Partition.ext ?_
  rw [parts_conj, partsList_conj, conjPart_conjPart (isPart_partsList p), coe_partsList]

theorem conj_injective : Function.Injective (conj : Partition n → Partition n) :=
  Function.LeftInverse.injective conj_conj

/-- Conjugation as an involutive bijection of the partitions of `n`. -/
def conjEquiv (n : ℕ) : Partition n ≃ Partition n where
  toFun := conj
  invFun := conj
  left_inv := conj_conj
  right_inv := conj_conj

@[simp] lemma conjEquiv_apply (p : Partition n) : conjEquiv n p = p.conj := rfl

/-- The number of parts of the conjugate is the size of the largest part. -/
theorem card_parts_conj_le_iff (p : Partition n) (k : ℕ) :
    Multiset.card p.conj.parts ≤ k ↔ ∀ i ∈ p.parts, i ≤ k := by
  rw [← length_partsList, partsList_conj, length_conjPart (isPart_partsList p),
    ← (isPart_partsList p).forall_mem_le_iff]
  simp

/-- The largest part of the conjugate is the number of parts. -/
theorem forall_mem_parts_conj_le_iff (p : Partition n) (k : ℕ) :
    (∀ i ∈ p.conj.parts, i ≤ k) ↔ Multiset.card p.parts ≤ k := by
  rw [← length_partsList]
  have h := (isPart_conjPart (isPart_partsList p)).forall_mem_le_iff k
  rw [← partsList_conj] at h
  rw [show (∀ i ∈ p.conj.parts, i ≤ k) ↔ ∀ i ∈ p.conj.partsList, i ≤ k by simp, h,
    partsList_conj, headD_conjPart (isPart_partsList p)]

/-- Conjugation is a bijection between the partitions of `n` with at most `k` parts and
the partitions of `n` all of whose parts are at most `k`. -/
def conjEquivLengthLe (n k : ℕ) :
    {p : Partition n // Multiset.card p.parts ≤ k} ≃ {p : Partition n // ∀ i ∈ p.parts, i ≤ k} where
  toFun p := ⟨p.1.conj, (forall_mem_parts_conj_le_iff p.1 k).2 p.2⟩
  invFun p := ⟨p.1.conj, (card_parts_conj_le_iff p.1 k).2 p.2⟩
  left_inv p := Subtype.ext (conj_conj p.1)
  right_inv p := Subtype.ext (conj_conj p.1)

/-! ### The dominance order -/

/-- The dominance order on partitions of `n`: every partial sum of the parts of `p`, in
decreasing order, is at most the corresponding partial sum for `q`. -/
def Partdom (p q : Partition n) : Prop := List.Partdom p.partsList q.partsList

theorem partdom_refl (p : Partition n) : Partdom p p := List.Partdom.refl _

theorem Partdom.trans {p q r : Partition n} (h1 : Partdom p q) (h2 : Partdom q r) :
    Partdom p r := List.Partdom.trans h1 h2

theorem Partdom.antisymm {p q : Partition n} (h1 : Partdom p q) (h2 : Partdom q p) : p = q := by
  refine Partition.ext ?_
  rw [← coe_partsList p, ← coe_partsList q,
    List.Partdom.antisymm (isPart_partsList p) (isPart_partsList q) h1 h2]

/-- Conjugation reverses the dominance order. -/
theorem partdom_conj_iff {p q : Partition n} : Partdom q.conj p.conj ↔ Partdom p q := by
  rw [Partdom, Partdom, partsList_conj, partsList_conj]
  exact partdom_conjPart_iff (isPart_partsList p) (isPart_partsList q)
    (by rw [sum_partsList, sum_partsList])

end Nat.Partition
