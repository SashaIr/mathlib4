/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Partitions as multisets, and the shape of a monomial

Partitions of an unspecified size, viewed as multisets of positive integers (unlike `Nat.Partition
n`, which fixes the size, and unlike the list-based partitions `List.IsPart` of
`Mathlib.Combinatorics.Young.Shape.Basic`, which are the ones used throughout the rest of the
library).

## Main definitions

* `MultisetPart.Partition` : a multiset of positive natural numbers.
* `MultisetPart.Partition.size` : the sum of the parts.
* `MultisetPart.monoDeg` : the total degree of an exponent vector.
* `MultisetPart.shape` : the partition given by the nonzero values of an exponent
  vector.
-/

namespace MultisetPart

open Finset Finsupp

/-- The total degree of a monomial exponent vector. -/
def monoDeg (d : ℕ →₀ ℕ) : ℕ := d.sum fun _ k => k

@[simp] lemma monoDeg_zero : monoDeg 0 = 0 := by simp [monoDeg]

lemma monoDeg_add (d d' : ℕ →₀ ℕ) : monoDeg (d + d') = monoDeg d + monoDeg d' := by
  simp [monoDeg, Finsupp.sum_add_index']

/-- A partition: a multiset of positive natural numbers. Its `size` is the sum of its parts. -/
@[ext]
structure Partition where
  /-- The parts of the partition. -/
  parts : Multiset ℕ
  /-- All parts are positive. -/
  parts_pos : ∀ {i}, i ∈ parts → 0 < i

namespace Partition

instance : DecidableEq Partition := fun _ _ => decidable_of_iff _ (Partition.ext_iff).symm

/-- The size (sum of the parts) of a partition. -/
def size (l : Partition) : ℕ := l.parts.sum

/-- The number of parts of a partition. -/
def length (l : Partition) : ℕ := Multiset.card l.parts

/-- The empty partition. -/
instance : Zero Partition := ⟨⟨0, by simp⟩⟩

@[simp] lemma parts_zero : (0 : Partition).parts = 0 := rfl

@[simp] lemma size_zero : (0 : Partition).size = 0 := rfl

lemma eq_zero_iff (l : Partition) : l = 0 ↔ l.parts = 0 := by
  constructor
  · rintro rfl; rfl
  · intro h; ext1; simpa using h

/-- A partition of size zero is the empty partition. -/
lemma eq_zero_of_size_eq_zero {l : Partition} (h : l.size = 0) : l = 0 := by
  rw [eq_zero_iff, ← Multiset.card_eq_zero]
  by_contra hc
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero hc)
  have h1 := l.parts_pos ha
  have h2 : a ≤ l.parts.sum := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ ha
  rw [size] at h
  omega

/-- The partition underlying a `Nat.Partition`. -/
def ofNat {n : ℕ} (l : n.Partition) : Partition := ⟨l.parts, l.parts_pos⟩

@[simp] lemma parts_ofNat {n : ℕ} (l : n.Partition) : (ofNat l).parts = l.parts := rfl

@[simp] lemma size_ofNat {n : ℕ} (l : n.Partition) : (ofNat l).size = n := l.parts_sum

lemma ofNat_injective {n : ℕ} : Function.Injective (ofNat (n := n)) := by
  intro a b h
  exact Nat.Partition.ext (congrArg parts h)

/-- Conversely, a partition of size `n` gives a `Nat.Partition n`. -/
def toNat (l : Partition) : l.size.Partition :=
  ⟨l.parts, l.parts_pos, rfl⟩

@[simp] lemma ofNat_toNat (l : Partition) : ofNat l.toNat = l := rfl

end Partition

/-- The *shape* of an exponent vector: the multiset of its nonzero values. -/
def shape (d : ℕ →₀ ℕ) : Partition :=
  ⟨d.support.val.map d, by
    intro i hi
    simp only [Multiset.mem_map, Finset.mem_val, Finsupp.mem_support_iff] at hi
    obtain ⟨a, ha, rfl⟩ := hi
    exact Nat.pos_of_ne_zero ha⟩

@[simp] lemma parts_shape (d : ℕ →₀ ℕ) : (shape d).parts = d.support.val.map d := rfl

@[simp] lemma shape_zero : shape 0 = 0 := by
  ext1; simp

lemma size_shape (d : ℕ →₀ ℕ) : (shape d).size = monoDeg d := rfl

lemma length_shape (d : ℕ →₀ ℕ) : (shape d).length = d.support.card :=
  Multiset.card_map _ _

lemma shape_eq_zero_iff {d : ℕ →₀ ℕ} : shape d = 0 ↔ d = 0 := by
  constructor
  · intro h
    have h0 : d.support.val.map d = 0 := congrArg Partition.parts h
    have hs : d.support = ∅ := by
      rw [Multiset.map_eq_zero] at h0
      exact Finset.val_eq_zero.1 h0
    ext a
    have : a ∉ d.support := by simp [hs]
    simpa using Finsupp.notMem_support_iff.1 this
  · rintro rfl; simp

end MultisetPart
