/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.List.ConjugateEquiv
public import Mathlib.Combinatorics.Enumerative.Partition.List.Dominance
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram

/-!
# Conjugation and dominance for the partitions of an integer

The conjugate of a partition of `n` is defined here as the transpose of its Young diagram:
the `i`-th part of `p.conj` is the number of parts of `p` which are larger than `i`.
Through the dictionary of `Mathlib.Combinatorics.Enumerative.Partition.List.YoungDiagram`,
this is the conjugation `Young.conjPart` of the list model, which is what all the proofs go
through.  The dominance order is transported from the list model in the same way.

## Main definitions

* `Nat.Partition.conj` : the conjugate partition.
* `Nat.Partition.Partdom` : the dominance order on `Nat.Partition n`.

## Main results

* `Nat.Partition.youngDiagram_conj` : the Young diagram of the conjugate is the transpose.
* `Nat.Partition.conj_conj` : conjugation is an involution.
* `Nat.Partition.card_parts_conj_le_iff`, `Nat.Partition.forall_mem_parts_conj_le_iff` :
  conjugation exchanges the number of parts and the size of the largest part.
* `Nat.Partition.conjEquivLengthLe` : the partitions of `n` with at most `k` parts are in
  bijection with the partitions of `n` whose parts are all at most `k`.
* `Nat.Partition.partdom_conj_iff` : conjugation reverses the dominance order.
-/

@[expose] public section

open Young YoungDiagram

namespace Nat.Partition

open List

variable {n : ℕ}

/-- The conjugate of a partition: its Young diagram is the transpose of the Young diagram of
`p`, so that the `i`-th part of `p.conj` is the number of parts of `p` larger than `i`. -/
def conj (p : Partition n) : Partition n where
  parts := (p.youngDiagram.transpose.rowLens : Multiset ℕ)
  parts_pos hi := p.youngDiagram.transpose.pos_of_mem_rowLens _ (by simpa using hi)
  parts_sum := by
    rw [Multiset.sum_coe, ← YoungDiagram.card_eq_sum_rowLens, YoungDiagram.card_transpose,
      card_youngDiagram]

@[simp] lemma partsList_conj (p : Partition n) : p.conj.partsList = conjPart p.partsList := by
  have h := isPart_partsList p
  change sortDesc (p.youngDiagram.transpose.rowLens : Multiset ℕ) = _
  rw [sortDesc_coe (isPart_rowLens _), youngDiagram, transpose_ofRowLens h,
    rowLens_ofRowLens_eq_self (hw := (isPart_conjPart h).sortedGE) (isPart_conjPart h).2]

@[simp] lemma parts_conj (p : Partition n) :
    p.conj.parts = (conjPart p.partsList : Multiset ℕ) := by
  rw [← coe_partsList, partsList_conj]

/-- **Conjugation of partitions is transposition of Young diagrams.** -/
@[simp] theorem youngDiagram_conj (p : Partition n) :
    p.conj.youngDiagram = p.youngDiagram.transpose := by
  rw [youngDiagram, youngDiagram, transpose_ofRowLens (isPart_partsList p)]
  exact ofRowLens_congr (isPart_partsList p.conj) (isPart_conjPart (isPart_partsList p))
    (partsList_conj p)

/-- Conjugation is an involution. -/
@[simp] theorem conj_conj (p : Partition n) : p.conj.conj = p := by
  refine Partition.ext ?_
  rw [← coe_partsList, ← coe_partsList p, partsList_conj, partsList_conj,
    conjPart_conjPart (isPart_partsList p)]

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
def Partdom (p q : Partition n) : Prop := Young.Partdom p.partsList q.partsList

theorem partdom_refl (p : Partition n) : Partdom p p := Young.Partdom.refl _

theorem Partdom.trans {p q r : Partition n} (h1 : Partdom p q) (h2 : Partdom q r) :
    Partdom p r := Young.Partdom.trans h1 h2

theorem Partdom.antisymm {p q : Partition n} (h1 : Partdom p q) (h2 : Partdom q p) : p = q := by
  refine Partition.ext ?_
  rw [← coe_partsList p, ← coe_partsList q,
    Young.Partdom.antisymm (isPart_partsList p) (isPart_partsList q) h1 h2]

/-- Conjugation reverses the dominance order. -/
theorem partdom_conj_iff {p q : Partition n} : Partdom q.conj p.conj ↔ Partdom p q := by
  rw [Partdom, Partdom, partsList_conj, partsList_conj]
  exact partdom_conjPart_iff (isPart_partsList p) (isPart_partsList q)
    (by rw [sum_partsList, sum_partsList])

end Nat.Partition
