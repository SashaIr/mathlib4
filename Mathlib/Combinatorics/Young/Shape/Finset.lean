/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Shape.NatPartition

/-!
# Partitions as a finite set of lists

The partitions of `n` form a finite type; it is often more convenient to see them as a
finite set `Young.partFinset n` of lists, so that sums over partitions of various sizes
can be compared without any dependent-type juggling.  `Young.partFinsetLe N` gathers the
partitions of size at most `N`.

## Main definitions

* `Young.partFinset n` : the partitions of `n`.
* `Young.partFinsetLe N` : the partitions of size at most `N`.
-/

@[expose] public section

namespace Young

open List

/-- The partitions of `n`, as a finite set of lists. -/
noncomputable def partFinset (n : ℕ) : Finset (List ℕ) :=
  Finset.univ.image (fun p : {p : List ℕ // IsPart p ∧ p.sum = n} => p.1)

@[simp] lemma mem_partFinset {n : ℕ} {l : List ℕ} :
    l ∈ partFinset n ↔ IsPart l ∧ l.sum = n := by
  rw [partFinset, Finset.mem_image]
  refine ⟨?_, fun h => ⟨⟨l, h⟩, Finset.mem_univ _, rfl⟩⟩
  rintro ⟨q, -, rfl⟩
  exact q.2

lemma partFinset_zero : partFinset 0 = {[]} := by
  ext l
  simp only [mem_partFinset, Finset.mem_singleton]
  exact ⟨fun h => h.1.eq_nil_of_sum_eq_zero h.2, by rintro rfl; exact ⟨isPart_nil, rfl⟩⟩

lemma sum_subtype_eq_sum_partFinset {M : Type*} [AddCommMonoid M] (n : ℕ) (f : List ℕ → M) :
    ∑ p : {p : List ℕ // IsPart p ∧ p.sum = n}, f p.1 = ∑ l ∈ partFinset n, f l := by
  rw [partFinset, Finset.sum_image fun x _ y _ h => Subtype.ext h]

/-- The partitions of size at most `N`, as a finite set of lists. -/
noncomputable def partFinsetLe (N : ℕ) : Finset (List ℕ) :=
  (Finset.range (N + 1)).biUnion partFinset

@[simp] lemma mem_partFinsetLe {N : ℕ} {l : List ℕ} :
    l ∈ partFinsetLe N ↔ IsPart l ∧ l.sum ≤ N := by
  rw [partFinsetLe, Finset.mem_biUnion]
  constructor
  · rintro ⟨k, hk, hl⟩
    rw [mem_partFinset] at hl
    rw [Finset.mem_range] at hk
    exact ⟨hl.1, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨l.sum, Finset.mem_range.2 (by omega), mem_partFinset.2 ⟨h1, rfl⟩⟩

lemma sum_partFinsetLe_eq {M : Type*} [AddCommMonoid M] (N : ℕ) (f : List ℕ → M) :
    ∑ l ∈ partFinsetLe N, f l = ∑ k ∈ Finset.range (N + 1), ∑ l ∈ partFinset k, f l := by
  refine Finset.sum_biUnion fun x _ y _ hxy => ?_
  simp only [Finset.disjoint_left, mem_partFinset]
  rintro l ⟨-, rfl⟩ ⟨-, h⟩
  exact hxy h

lemma filter_partFinsetLe {N k : ℕ} (hk : k ≤ N) :
    ((partFinsetLe N).filter (fun l => l.sum = k)) = partFinset k := by
  classical
  ext l
  simp only [Finset.mem_filter, mem_partFinsetLe, mem_partFinset]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by omega⟩, h.2⟩⟩

open scoped Classical in
lemma sum_partFinset_eq_sum_partFinsetLe {M : Type*} [AddCommMonoid M] {k N : ℕ} (hk : k ≤ N)
    (f : List ℕ → M) :
    ∑ l ∈ partFinset k, f l = ∑ l ∈ partFinsetLe N, if l.sum = k then f l else 0 := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, filter_partFinsetLe hk]

end Young
