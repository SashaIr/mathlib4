/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Data.List.Permutation
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.Young.Shape.NatPartitionConj
import Mathlib.Combinatorics.Young.RobinsonSchensted.Bijection

/-!
# Counting with the Robinson–Schensted correspondence

The Robinson–Schensted correspondence of
`Mathlib.Combinatorics.Young.RobinsonSchensted.Bijection` is a bijection between words and
pairs consisting of an insertion tableau and a standard recording tableau of the same shape.
Restricted to standard words of length `n` it becomes a bijection with the pairs of standard
tableaux of the same shape with `n` boxes.  Since there are `n!` standard words of length `n`, this
is the classical enumeration

`#{(P, Q) : P, Q standard tableaux of the same shape with n boxes} = n!`

which is the counting form of the identity `∑_λ (f^λ)² = n!`.

## Main results

* `List.card_stdWord` : there are `n!` standard words of length `n`.
* `List.RS_RSQ_bijOn_stdWord` : the Robinson–Schensted correspondence restricted to
  standard words of length `n`.
* `List.card_stdTabPair` : there are `n!` pairs of standard tableaux of the same shape
  with `n` boxes.
* `List.sum_sq_numStdTab` : `∑_λ (f^λ)² = n!`, the sum being over the partitions `λ`
  of `n` and `f^λ` denoting the number of standard tableaux of shape `λ`.
-/

namespace List

open List

/-! ### Standard words of a given length -/

lemma isStd_and_length_iff_perm_range {w : List ℕ} {n : ℕ} :
    (IsStd w ∧ w.length = n) ↔ w.Perm (List.range n) := by
  constructor
  · rintro ⟨hstd, rfl⟩
    exact hstd
  · intro h
    have hlen : w.length = n := by
      rw [h.length_eq, List.length_range]
    exact ⟨by rw [IsStd, hlen]; exact h, hlen⟩

/-- The set of standard words of length `n` is the set of permutations of `range n`. -/
lemma setOf_stdWord (n : ℕ) :
    {w : List ℕ | IsStd w ∧ w.length = n} = ↑(List.range n).permutations.toFinset := by
  ext w
  simp [isStd_and_length_iff_perm_range, List.mem_permutations]

/-- There are `n!` standard words of length `n`. -/
theorem card_stdWord (n : ℕ) :
    Nat.card {w : List ℕ | IsStd w ∧ w.length = n} = Nat.factorial n := by
  rw [setOf_stdWord n, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (List.nodup_permutations _ List.nodup_range),
    List.length_permutations, List.length_range]

/-! ### Pairs of standard tableaux -/

/-- The set of pairs of standard tableaux of the same shape with `n` boxes. -/
def stdTabPair (n : ℕ) : Set (List (List ℕ) × List (List ℕ)) :=
  {p | IsStdTab p.1 ∧ IsStdTab p.2 ∧ shape p.1 = shape p.2 ∧ sizeTab p.1 = n}

/-- The Robinson–Schensted correspondence is a bijection between the standard words of
length `n` and the pairs of standard tableaux of the same shape with `n` boxes. -/
theorem RS_RSQ_bijOn_stdWord (n : ℕ) :
    Set.BijOn (fun w : List ℕ => (RS w, RSQ w)) {w : List ℕ | IsStd w ∧ w.length = n}
      (stdTabPair n) := by
  have hbij := RS_RSQ_bijOn_isStd
  refine ⟨?_, ?_, ?_⟩
  · rintro w ⟨hstd, hlen⟩
    obtain ⟨h1, h2, h3⟩ := hbij.mapsTo hstd
    exact ⟨h1, h2, h3, by rw [sizeTab_RS, hlen]⟩
  · exact hbij.injOn.mono fun w hw => hw.1
  · rintro p ⟨h1, h2, h3, h4⟩
    obtain ⟨w, hw, hfw⟩ := hbij.surjOn ⟨h1, h2, h3⟩
    have hlen : w.length = n := by
      have : RS w = p.1 := congrArg Prod.fst hfw
      rw [← sizeTab_RS w, this, h4]
    exact ⟨w, ⟨hw, hlen⟩, hfw⟩

/-- There are `n!` pairs of standard tableaux of the same shape with `n` boxes; this is
the counting form of the identity `∑_λ (f^λ)² = n!`. -/
theorem card_stdTabPair (n : ℕ) : Nat.card (stdTabPair n) = Nat.factorial n := by
  rw [← card_stdWord n]
  exact (Nat.card_congr (RS_RSQ_bijOn_stdWord n).equiv).symm

/-! ### The identity `∑_λ (f^λ)² = n!` -/

/-- The number `f^sh` of standard tableaux of shape `sh`. -/
noncomputable def numStdTab (sh : List ℕ) : ℕ :=
  Nat.card {Q : List (List ℕ) // IsStdTab Q ∧ shape Q = sh}

instance finite_stdTabPair (n : ℕ) : Finite (stdTabPair n) := by
  have h : Finite {w : List ℕ | IsStd w ∧ w.length = n} := by
    rw [setOf_stdWord n]; infer_instance
  exact Finite.of_equiv _ (RS_RSQ_bijOn_stdWord n).equiv

/-- The common shape of a pair of standard tableaux, as a partition of `n`. -/
def shapePartition (n : ℕ) (p : stdTabPair n) : Nat.Partition n :=
  listPartEquivNatPartition n ⟨shape p.1.1, isPart_shape p.2.1.1, p.2.2.2.2⟩

lemma partsList_shapePartition (n : ℕ) (p : stdTabPair n) :
    (shapePartition n p).partsList = shape p.1.1 :=
  sortDesc_coe (isPart_shape p.2.1.1)

/-- The pairs of standard tableaux of the same shape with `n` boxes and prescribed shape
`lam` are the pairs of standard tableaux of shape `lam`. -/
def stdTabPairFiberEquiv (n : ℕ) (lam : Nat.Partition n) :
    {p : stdTabPair n // shapePartition n p = lam} ≃
      {Q : List (List ℕ) // IsStdTab Q ∧ shape Q = lam.partsList} ×
        {Q : List (List ℕ) // IsStdTab Q ∧ shape Q = lam.partsList} where
  toFun p :=
    have h1 : shape p.1.1.1 = lam.partsList := by
      rw [← partsList_shapePartition n p.1, p.2]
    (⟨p.1.1.1, p.1.2.1, h1⟩, ⟨p.1.1.2, p.1.2.2.1, by rw [← p.1.2.2.2.1, h1]⟩)
  invFun q :=
    ⟨⟨(q.1.1, q.2.1), q.1.2.1, q.2.2.1, by rw [q.1.2.2, q.2.2.2], by
        change (shape q.1.1).sum = n
        rw [q.1.2.2, Nat.Partition.sum_partsList]⟩,
      Nat.Partition.ext (by
        change ((shape q.1.1 : List ℕ) : Multiset ℕ) = lam.parts
        rw [q.1.2.2, Nat.Partition.coe_partsList])⟩
  left_inv p := rfl
  right_inv q := rfl

/-- The number of standard tableaux of shape `sh` squared, summed over all partitions of
`n`, is `n!`. -/
theorem sum_sq_numStdTab (n : ℕ) :
    ∑ lam : Nat.Partition n, (numStdTab lam.partsList) ^ 2 = Nat.factorial n := by
  have h1 : Nat.card (stdTabPair n) = ∑ lam : Nat.Partition n,
      Nat.card {p : stdTabPair n // shapePartition n p = lam} := by
    rw [← Nat.card_sigma]
    exact (Nat.card_congr (Equiv.sigmaFiberEquiv (shapePartition n))).symm
  rw [← card_stdTabPair n, h1]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [Nat.card_congr (stdTabPairFiberEquiv n lam), Nat.card_prod, numStdTab, sq]

end List
