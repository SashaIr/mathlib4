/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.List.ConjugateEquiv
public import Mathlib.Combinatorics.Enumerative.Partition.List.Finset

/-!
# Partitions with a bounded number of parts

The partitions of `n` with at most `m` parts index the bases of the symmetric homogeneous
polynomials of degree `n` in `m` variables, so they deserve a type of their own:
`Young.PartLengthLe n m`, a subtype of `List ℕ` in the list model of partitions.

The bound is a real restriction only for `m < n`: a partition of `n` has at most `n` parts, so
for `n ≤ m` the type is just `Nat.Partition n`.  This is what `Young.natPartitionEquivPartLengthLe`
says, and what the two coercions

* `Young.PartLengthLe.toPartition`, forgetting the bound, and
* `Nat.Partition.toPartLengthLe`, taking the bound given by the size,

express in the two directions.  Together with `Young.PartLengthLe.castLe` they let a user state
and use a result about `PartLengthLe` without producing a list or a proof of a length bound.

## Main definitions

* `Young.PartLengthLe n m` : the partitions of `n` with at most `m` parts.
* `Young.PartLengthLe.toPartition`, `Nat.Partition.toPartLengthLe` : the two coercions to and
  from `Nat.Partition n`.
* `Young.natPartitionEquivPartLengthLe` : for `n ≤ m`, the two types agree.
* `Young.PartLengthLe.conj` : conjugation, a permutation of `PartLengthLe n m` for `n ≤ m`.
* `Young.partFinsetLengthLe n m` : the same partitions, as a finite set of lists.
-/

@[expose] public section

namespace Young

open List

variable {n m k : ℕ}

/-- The partitions of `n` with at most `m` parts, as a subtype of `List ℕ`.

This is the index type of the bases of the symmetric homogeneous polynomials of degree `n`
in `m` variables.  For `n ≤ m` the bound is vacuous and the type is `Nat.Partition n`, see
`Young.natPartitionEquivPartLengthLe`. -/
abbrev PartLengthLe (n m : ℕ) : Type := {μ : List ℕ // IsPart μ ∧ μ.sum = n ∧ μ.length ≤ m}

namespace PartLengthLe

lemma isPart (μ : PartLengthLe n m) : IsPart μ.1 := μ.2.1

lemma sum_eq (μ : PartLengthLe n m) : μ.1.sum = n := μ.2.2.1

lemma length_le (μ : PartLengthLe n m) : μ.1.length ≤ m := μ.2.2.2

instance : Fintype (PartLengthLe n m) :=
  Fintype.ofEquiv {q : {μ : List ℕ // IsPart μ ∧ μ.sum = n} // q.1.length ≤ m}
    { toFun := fun q => ⟨q.1.1, q.1.2.1, q.1.2.2, q.2⟩
      invFun := fun μ => ⟨⟨μ.1, μ.2.1, μ.2.2.1⟩, μ.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- A partition of `n`, given as a list, has at most `n` parts. -/
def ofList {μ : List ℕ} (hμ : IsPart μ) (hsum : μ.sum = n) : PartLengthLe n n :=
  ⟨μ, hμ, hsum, hsum ▸ hμ.length_le_sum⟩

@[simp] lemma ofList_val {μ : List ℕ} (hμ : IsPart μ) (hsum : μ.sum = n) :
    (ofList hμ hsum).1 = μ := rfl

/-- Relaxing the bound on the number of parts. -/
def castLe (h : m ≤ k) (μ : PartLengthLe n m) : PartLengthLe n k :=
  ⟨μ.1, μ.2.1, μ.2.2.1, μ.2.2.2.trans h⟩

@[simp] lemma castLe_val (h : m ≤ k) (μ : PartLengthLe n m) : (castLe h μ).1 = μ.1 := rfl

/-- The index set of the bases does not depend on the number of variables, as long as
there are at least `n` of them. -/
def equivOfLe (hm : n ≤ m) (hk : n ≤ k) : PartLengthLe n m ≃ PartLengthLe n k where
  toFun μ := ⟨μ.1, μ.2.1, μ.2.2.1, μ.2.1.length_le_sum.trans (μ.2.2.1.symm ▸ hk)⟩
  invFun μ := ⟨μ.1, μ.2.1, μ.2.2.1, μ.2.1.length_le_sum.trans (μ.2.2.1.symm ▸ hm)⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma equivOfLe_coe (hm : n ≤ m) (hk : n ≤ k) (μ : PartLengthLe n m) :
    (equivOfLe hm hk μ).1 = μ.1 := rfl

@[simp] lemma equivOfLe_symm_coe (hm : n ≤ m) (hk : n ≤ k) (μ : PartLengthLe n k) :
    ((equivOfLe hm hk).symm μ).1 = μ.1 := rfl

/-! ### The coercion to `Nat.Partition` -/

/-- Forgetting the bound on the number of parts: the underlying partition of `n`. -/
def toPartition (μ : PartLengthLe n m) : Nat.Partition n :=
  Nat.Partition.ofList μ.1 μ.2.1 μ.2.2.1

instance : CoeOut (PartLengthLe n m) (Nat.Partition n) := ⟨toPartition⟩

@[simp] lemma partsList_toPartition (μ : PartLengthLe n m) : μ.toPartition.partsList = μ.1 :=
  Nat.Partition.partsList_ofList _ _

lemma toPartition_injective : Function.Injective (toPartition : PartLengthLe n m → _) :=
  fun μ ν h => Subtype.ext <| by
    rw [← partsList_toPartition μ, ← partsList_toPartition ν, h]

@[simp] lemma toPartition_inj {μ ν : PartLengthLe n m} :
    μ.toPartition = ν.toPartition ↔ μ = ν :=
  toPartition_injective.eq_iff

end PartLengthLe

/-! ### The coercion from `Nat.Partition` -/

/-- A partition of `n` has at most `n` parts, so as soon as `n ≤ m` the partitions of `n`
with at most `m` parts are exactly the partitions of `n`. -/
def natPartitionEquivPartLengthLe (hnm : n ≤ m) : Nat.Partition n ≃ PartLengthLe n m :=
  (listPartEquivNatPartition n).symm.trans (Equiv.subtypeEquivRight fun μ =>
    ⟨fun h => ⟨h.1, h.2, h.1.length_le_sum.trans (by rw [h.2]; exact hnm)⟩,
      fun h => ⟨h.1, h.2.1⟩⟩)

@[simp] lemma coe_natPartitionEquivPartLengthLe (hnm : n ≤ m) (μ : Nat.Partition n) :
    (natPartitionEquivPartLengthLe hnm μ : List ℕ) = μ.partsList := rfl

@[simp] lemma partsList_natPartitionEquivPartLengthLe_symm (hnm : n ≤ m)
    (μ : PartLengthLe n m) :
    ((natPartitionEquivPartLengthLe hnm).symm μ).partsList = μ.1 :=
  sortDesc_coe μ.2.1

end Young

namespace Nat.Partition

open Young

variable {n : ℕ}

/-- A partition of `n` has at most `n` parts, so it is a partition of `n` of length at most `n`:
the bound given by the size.  For a larger bound, compose with `Young.PartLengthLe.castLe` or use
`Young.natPartitionEquivPartLengthLe`. -/
abbrev toPartLengthLe (μ : Nat.Partition n) : PartLengthLe n n :=
  natPartitionEquivPartLengthLe (le_refl n) μ

instance : CoeTail (Nat.Partition n) (PartLengthLe n n) := ⟨toPartLengthLe⟩

@[simp] lemma coe_toPartLengthLe (μ : Nat.Partition n) :
    (μ.toPartLengthLe : List ℕ) = μ.partsList := rfl

@[simp] lemma toPartition_toPartLengthLe (μ : Nat.Partition n) :
    μ.toPartLengthLe.toPartition = μ :=
  partsList_injective (by simp)

end Nat.Partition

namespace Young

open List

variable {n m : ℕ}

@[simp] lemma PartLengthLe.toPartLengthLe_toPartition (μ : PartLengthLe n n) :
    μ.toPartition.toPartLengthLe = μ :=
  Subtype.ext (partsList_toPartition μ)

/-! ### Conjugation -/

namespace PartLengthLe

/-- The conjugate of a partition of `n` with at most `m` parts, again as a partition of
`n` with at most `m` parts (using `n ≤ m`). -/
def conj (hnm : n ≤ m) (μ : PartLengthLe n m) : PartLengthLe n m :=
  ⟨conjPart μ.1, isPart_conjPart μ.2.1, by rw [sum_conjPart, μ.2.2.1], by
    rw [length_conjPart μ.2.1]
    exact le_trans (le_trans (headD_le_sum μ.1) (le_of_eq μ.2.2.1)) hnm⟩

@[simp] lemma conj_val (hnm : n ≤ m) (μ : PartLengthLe n m) :
    (conj hnm μ).1 = conjPart μ.1 := rfl

lemma conj_conj (hnm : n ≤ m) (μ : PartLengthLe n m) : conj hnm (conj hnm μ) = μ :=
  Subtype.ext (conjPart_conjPart μ.2.1)

/-- Conjugation is a permutation of the partitions of `n` with at most `m` parts, as soon
as `n ≤ m`. -/
def conjEquiv (hnm : n ≤ m) : PartLengthLe n m ≃ PartLengthLe n m where
  toFun := conj hnm
  invFun := conj hnm
  left_inv := conj_conj hnm
  right_inv := conj_conj hnm

@[simp] lemma conjEquiv_apply (hnm : n ≤ m) (μ : PartLengthLe n m) :
    conjEquiv hnm μ = conj hnm μ := rfl

end PartLengthLe

/-- Conjugation is a bijection between the partitions of `n` with at most `m` parts and the
partitions of `n` all of whose parts are at most `m`.  In particular these two sets of
partitions are equinumerous. -/
def conjPartEquivLengthLe (n m : ℕ) :
    PartLengthLe n m ≃ {μ : List ℕ // IsPart μ ∧ μ.sum = n ∧ ∀ i ∈ μ, i ≤ m} where
  toFun μ :=
    ⟨conjPart μ.1, isPart_conjPart μ.2.1, by rw [sum_conjPart]; exact μ.2.2.1, by
      rw [(isPart_conjPart μ.2.1).forall_mem_le_iff, headD_conjPart μ.2.1]
      exact μ.2.2.2⟩
  invFun μ :=
    ⟨conjPart μ.1, isPart_conjPart μ.2.1, by rw [sum_conjPart]; exact μ.2.2.1, by
      rw [length_conjPart μ.2.1]
      exact (μ.2.1.forall_mem_le_iff m).1 μ.2.2.2⟩
  left_inv μ := Subtype.ext (conjPart_conjPart μ.2.1)
  right_inv μ := Subtype.ext (conjPart_conjPart μ.2.1)

@[simp] lemma conjPartEquivLengthLe_apply (μ : PartLengthLe n m) :
    ((conjPartEquivLengthLe n m) μ).1 = conjPart μ.1 := rfl

/-! ### As a finite set of lists -/

/-- The partitions of `n` with at most `m` parts, as a finite set of lists. -/
noncomputable def partFinsetLengthLe (n m : ℕ) : Finset (List ℕ) :=
  Finset.univ.image (fun μ : PartLengthLe n m => μ.1)

@[simp] lemma mem_partFinsetLengthLe {l : List ℕ} :
    l ∈ partFinsetLengthLe n m ↔ IsPart l ∧ l.sum = n ∧ l.length ≤ m := by
  rw [partFinsetLengthLe, Finset.mem_image]
  refine ⟨?_, fun h => ⟨⟨l, h⟩, Finset.mem_univ _, rfl⟩⟩
  rintro ⟨μ, -, rfl⟩
  exact μ.2

lemma partFinsetLengthLe_subset_partFinset (n m : ℕ) :
    partFinsetLengthLe n m ⊆ partFinset n := by
  intro l hl
  rw [mem_partFinsetLengthLe] at hl
  exact mem_partFinset.2 ⟨hl.1, hl.2.1⟩

/-- When `n ≤ m`, every partition of `n` has at most `m` parts. -/
lemma partFinsetLengthLe_eq_partFinset (n m : ℕ) (hnm : n ≤ m) :
    partFinsetLengthLe n m = partFinset n := by
  ext l
  rw [mem_partFinsetLengthLe, mem_partFinset]
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, ?_⟩⟩
  exact le_trans (le_trans h.1.length_le_sum (le_of_eq h.2)) hnm

/-- A sum over the partitions of `n` with at most `m` parts, as a sum over
`Young.PartLengthLe n m`. -/
lemma sum_partFinset_eq_sum_partLengthLe {M : Type*} [AddCommMonoid M] (hnm : n ≤ m)
    (f : List ℕ → M) : ∑ l ∈ partFinset n, f l = ∑ μ : PartLengthLe n m, f μ.1 := by
  rw [← partFinsetLengthLe_eq_partFinset n m hnm, partFinsetLengthLe,
    Finset.sum_image fun x _ y _ h => Subtype.ext h]

end Young
