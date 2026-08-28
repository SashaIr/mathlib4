/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Combinatorics.Young.Shape.Finset

/-!
# Cycle types of permutations

This file ports the part of Coq-Combi's `SymGroup/cycletype.v` and `MPoly/permcent.v`
dealing with the cycle type of a permutation of `Fin n`, seen as an integer partition of
`n` in the list-based representation used throughout this development, and with the
cardinality of the conjugacy classes.

Mathlib records the cycle type of a permutation as the multiset `Equiv.Perm.cycleType` of
the lengths of its nontrivial cycles; adding the fixed points as parts equal to `1` gives a
partition of `n` (`Equiv.Perm.partition`).  Sorting it decreasingly gives the list-based
partition `Equiv.Perm.cycleTypeList`.

## Main definitions

* `Equiv.Perm.cycleTypeList σ` : the cycle type of `σ : Equiv.Perm (Fin n)`, as a weakly
  decreasing list of positive integers summing to `n`.
* `List.zcard l` : the integer `z_λ = ∏_i i ^ m_i · m_i !`, where `m_i` is the number of
  parts of `λ` equal to `i`; it is the cardinality of the centralizer of a permutation of
  cycle type `λ`.

## Main results

* `Equiv.Perm.isPart_cycleTypeList`, `Equiv.Perm.sum_cycleTypeList` : the cycle type is a partition
  of `n`.
* `Equiv.Perm.cycleTypeList_eq_iff_isConj` : two permutations are conjugate if and only if they
  have the same cycle type.
* `Equiv.Perm.exists_cycleTypeList_eq` : every partition of `n` is the cycle type of some
  permutation.
* `Equiv.Perm.card_cycleTypeList_mul_zcard` : the number of permutations of `Fin n` of cycle
  type `λ`, times `z_λ`, is `n !`.
* `Equiv.Perm.sum_one_div_zcard` : `∑_{λ ⊢ n} 1 / z_λ = 1`.
-/

open Equiv Finset Nat List

namespace Equiv.Perm


variable {n : ℕ}

/-- The cycle type of a permutation of `Fin n`, as a weakly decreasing list of positive
integers: the lengths of the nontrivial cycles together with a part `1` for each fixed
point.  This is the list-based form of Mathlib's `Equiv.Perm.partition`. -/
noncomputable def cycleTypeList (σ : Perm (Fin n)) : List ℕ := sortDesc σ.partition.parts

lemma coe_cycleTypeList (σ : Perm (Fin n)) :
    (cycleTypeList σ : Multiset ℕ) = σ.partition.parts :=
  coe_sortDesc _

/-- The cycle type of a permutation is a partition. -/
lemma isPart_cycleTypeList (σ : Perm (Fin n)) : IsPart (cycleTypeList σ) :=
  isPart_sortDesc fun _ hi => σ.partition.parts_pos hi

/-- The cycle type of a permutation of `Fin n` is a partition of `n`. -/
@[simp] lemma sum_cycleTypeList (σ : Perm (Fin n)) : (cycleTypeList σ).sum = n := by
  rw [cycleTypeList, sum_sortDesc, σ.partition.parts_sum, Fintype.card_fin]

lemma cycleTypeList_mem_partFinset (σ : Perm (Fin n)) : cycleTypeList σ ∈ partFinset n :=
  mem_partFinset.2 ⟨isPart_cycleTypeList σ, sum_cycleTypeList σ⟩

/-- Two permutations are conjugate if and only if they have the same cycle type. -/
lemma cycleTypeList_eq_iff_isConj {σ τ : Perm (Fin n)} :
    cycleTypeList σ = cycleTypeList τ ↔ IsConj σ τ := by
  rw [partition_eq_of_isConj]
  refine ⟨fun h => Nat.Partition.ext ?_, fun h => by rw [cycleTypeList, cycleTypeList, h]⟩
  rw [← coe_cycleTypeList, ← coe_cycleTypeList, h]

end Equiv.Perm

namespace List

/-- The parts of a list that are at least `2`: for a cycle type, the lengths of the
nontrivial cycles, i.e. Mathlib's `Equiv.Perm.cycleType`. -/
noncomputable def bigParts (l : List ℕ) : Multiset ℕ := (l : Multiset ℕ).filter (2 ≤ ·)

lemma two_le_of_mem_bigParts {l : List ℕ} {a : ℕ} (ha : a ∈ bigParts l) : 2 ≤ a :=
  (Multiset.mem_filter.1 ha).2

lemma coe_eq_bigParts_add_replicate {l : List ℕ} (h : IsPart l) :
    (l : Multiset ℕ) = bigParts l + Multiset.replicate (l.count 1) 1 := by
  conv_lhs => rw [← Multiset.filter_add_not (2 ≤ ·) (l : Multiset ℕ)]
  congr 1
  have hfil : (Multiset.filter (fun a => ¬ 2 ≤ a) (l : Multiset ℕ)) =
      Multiset.filter (fun a => a = 1) (l : Multiset ℕ) := by
    refine Multiset.filter_congr fun a ha => ?_
    have := h.pos_of_mem (by simpa using ha)
    omega
  rw [hfil, Multiset.filter_eq']
  simp

lemma sum_bigParts_add_count_one {l : List ℕ} (h : IsPart l) :
    (bigParts l).sum + l.count 1 = l.sum := by
  have := congrArg Multiset.sum (coe_eq_bigParts_add_replicate h)
  simpa [Multiset.sum_replicate] using this.symm

end List

namespace Equiv.Perm

variable {n : ℕ}

/-- A permutation of `Fin n` has cycle type the partition `l` exactly when Mathlib's
`cycleType` is the multiset of the parts of `l` that are at least `2`. -/
lemma cycleTypeList_eq_iff {σ : Perm (Fin n)} {l : List ℕ} (hl : IsPart l) (hn : l.sum = n) :
    cycleTypeList σ = l ↔ σ.cycleType = bigParts l := by
  constructor
  · rintro rfl
    rw [bigParts, coe_cycleTypeList, filter_parts_partition_eq_cycleType]
  · intro h
    have hsupp : #σ.support = (bigParts l).sum := by
      rw [← sum_cycleType, h]
    have hpart : σ.partition.parts = (l : Multiset ℕ) := by
      rw [parts_partition, h, coe_eq_bigParts_add_replicate hl, hsupp, Fintype.card_fin]
      congr 2
      have := sum_bigParts_add_count_one hl
      omega
    rw [cycleTypeList, hpart, sortDesc_coe hl]

/-- Every partition of `n` is the cycle type of a permutation of `Fin n`. -/
lemma exists_cycleTypeList_eq {l : List ℕ} (hl : IsPart l) (hn : l.sum = n) :
    ∃ σ : Perm (Fin n), cycleTypeList σ = l := by
  have hsum : (bigParts l).sum ≤ Fintype.card (Fin n) := by
    have := sum_bigParts_add_count_one hl
    rw [Fintype.card_fin]
    omega
  obtain ⟨σ, hσ⟩ := (exists_with_cycleType_iff (Fin n)).2
    ⟨hsum, fun a ha => two_le_of_mem_bigParts ha⟩
  exact ⟨σ, (cycleTypeList_eq_iff hl hn).2 hσ⟩

end Equiv.Perm

namespace List

/-- `z_λ = ∏_i i ^ m_i · m_i !`, where `m_i` is the number of parts of `λ` equal to `i`.
It is the cardinality of the centralizer of a permutation of cycle type `λ`. -/
noncomputable def zcard (l : List ℕ) : ℕ :=
  ∏ i ∈ l.toFinset, i ^ l.count i * Nat.factorial (l.count i)

lemma zcard_pos {l : List ℕ} (h : IsPart l) : 0 < zcard l := by
  refine Finset.prod_pos fun i hi => ?_
  have hi' : 0 < i := h.pos_of_mem (List.mem_toFinset.1 hi)
  exact Nat.mul_pos (pow_pos hi' _) (Nat.factorial_pos _)

/-- Splitting off the parts equal to `1` from `z_λ`. -/
lemma zcard_eq (l : List ℕ) (hl : IsPart l) :
    zcard l = Nat.factorial (l.count 1) * (bigParts l).prod *
      ∏ j ∈ (bigParts l).toFinset, Nat.factorial ((bigParts l).count j) := by
  classical
  have hcount : ∀ i, 2 ≤ i → (bigParts l).count i = l.count i := by
    intro i hi
    rw [bigParts, Multiset.count_filter_of_pos hi, Multiset.coe_count]
  have hbig : (bigParts l).toFinset = l.toFinset.erase 1 := by
    ext i
    simp only [Multiset.mem_toFinset, bigParts, Multiset.mem_filter, Finset.mem_erase,
      List.mem_toFinset, Multiset.mem_coe]
    constructor
    · rintro ⟨hmem, h2⟩; exact ⟨by omega, hmem⟩
    · rintro ⟨hne, hmem⟩
      have := hl.pos_of_mem hmem
      exact ⟨hmem, by omega⟩
  have hsplit : zcard l = (1 ^ l.count 1 * Nat.factorial (l.count 1)) *
      ∏ i ∈ l.toFinset.erase 1, i ^ l.count i * Nat.factorial (l.count i) := by
    by_cases h1 : (1 : ℕ) ∈ l.toFinset
    · exact (Finset.mul_prod_erase _ _ h1).symm
    · have : l.count 1 = 0 := by
        simpa [List.count_eq_zero] using (fun hc => h1 (List.mem_toFinset.2 hc))
      rw [Finset.erase_eq_of_notMem h1, this]
      simp [zcard]
  rw [hsplit, hbig, one_pow, one_mul, Finset.prod_multiset_count (bigParts l), hbig, mul_assoc,
    ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun i hi => ?_)
  have h2 : 2 ≤ i := by
    have hmem : i ∈ (bigParts l).toFinset := by rw [hbig]; exact hi
    exact two_le_of_mem_bigParts (Multiset.mem_toFinset.1 hmem)
  rw [hcount i h2]

end List

namespace Equiv.Perm

variable {n : ℕ}

/-- **The number of permutations of a given cycle type.**  The permutations of `Fin n`
with cycle type the partition `λ` of `n` number `n ! / z_λ`. -/
theorem card_cycleTypeList_mul_zcard {l : List ℕ} (hl : IsPart l) (hn : l.sum = n) :
    #{σ : Perm (Fin n) | cycleTypeList σ = l} * zcard l = n ! := by
  have hset : ({σ : Perm (Fin n) | cycleTypeList σ = l} : Finset (Perm (Fin n))) =
      ({σ : Perm (Fin n) | σ.cycleType = bigParts l} : Finset (Perm (Fin n))) :=
    Finset.filter_congr fun σ _ => by
      simpa using cycleTypeList_eq_iff hl hn
  have hsum : (bigParts l).sum ≤ Fintype.card (Fin n) := by
    have := sum_bigParts_add_count_one hl
    rw [Fintype.card_fin]
    omega
  have hmain := card_of_cycleType_mul_eq (Fin n) (bigParts l)
  rw [if_pos ⟨hsum, fun a ha => two_le_of_mem_bigParts ha⟩] at hmain
  have hcnt : Fintype.card (Fin n) - (bigParts l).sum = l.count 1 := by
    have := sum_bigParts_add_count_one hl
    rw [Fintype.card_fin]
    omega
  rw [hset, zcard_eq l hl, ← hcnt, hmain, Fintype.card_fin]

/-- The classical identity `∑_{λ ⊢ n} 1 / z_λ = 1`. -/
theorem sum_one_div_zcard (n : ℕ) : ∑ l ∈ partFinset n, (1 : ℚ) / zcard l = 1 := by
  have hcard : ∑ l ∈ partFinset n, #{σ : Perm (Fin n) | cycleTypeList σ = l} = n ! := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun σ _ => cycleTypeList_mem_partFinset σ),
      Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have key : ∀ l ∈ partFinset n,
      ((#{σ : Perm (Fin n) | cycleTypeList σ = l} : ℚ)) = (n ! : ℚ) / zcard l := by
    intro l hl
    rw [mem_partFinset] at hl
    have hz : (zcard l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (zcard_pos hl.1).ne'
    rw [eq_div_iff hz]
    exact_mod_cast card_cycleTypeList_mul_zcard hl.1 hl.2
  have hcast : ∑ l ∈ partFinset n, ((#{σ : Perm (Fin n) | cycleTypeList σ = l} : ℕ) : ℚ)
      = (n ! : ℚ) := by
    rw [← Nat.cast_sum, hcard]
  have hexp : ∑ l ∈ partFinset n, (n ! : ℚ) / zcard l = (n ! : ℚ) :=
    (Finset.sum_congr rfl fun l hl => (key l hl).symm).trans hcast
  have hfac : (n ! : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  refine mul_left_cancel₀ hfac ?_
  rw [mul_one, Finset.mul_sum]
  exact (Finset.sum_congr rfl fun l _ => mul_one_div _ _).trans hexp

/-- The number of parts equal to `1` of the cycle type is the number of fixed points. -/
lemma count_one_cycleTypeList (σ : Perm (Fin n)) :
    (cycleTypeList σ).count 1 = Fintype.card (Fin n) - σ.cycleType.sum := by
  have hb : bigParts (cycleTypeList σ) = σ.cycleType :=
    ((cycleTypeList_eq_iff (isPart_cycleTypeList σ) (sum_cycleTypeList σ)).1 rfl).symm
  have h := sum_bigParts_add_count_one (isPart_cycleTypeList σ)
  rw [hb, sum_cycleTypeList] at h
  rw [Fintype.card_fin]
  omega

/-- **`z_λ` is the order of the centralizer** of a permutation of cycle type `λ`. -/
theorem nat_card_centralizer_eq_zcard (σ : Perm (Fin n)) :
    Nat.card (Subgroup.centralizer {σ}) = zcard (cycleTypeList σ) := by
  have hb : bigParts (cycleTypeList σ) = σ.cycleType :=
    ((cycleTypeList_eq_iff (isPart_cycleTypeList σ) (sum_cycleTypeList σ)).1 rfl).symm
  rw [Equiv.Perm.nat_card_centralizer σ, zcard_eq _ (isPart_cycleTypeList σ), hb,
    count_one_cycleTypeList σ]

/-- The cycle type of a conjugacy class of permutations. -/
noncomputable def classCycleType (c : ConjClasses (Perm (Fin n))) : List ℕ :=
  Quotient.liftOn c cycleTypeList fun _ _ h => cycleTypeList_eq_iff_isConj.2 h

@[simp] lemma classCycleType_mk (σ : Perm (Fin n)) :
    classCycleType (ConjClasses.mk σ) = cycleTypeList σ := rfl

/-- **The conjugacy classes of the symmetric group are indexed by the partitions**: two
permutations are conjugate exactly when they have the same cycle type, and every partition
occurs. -/
noncomputable def conjClassesEquivPart (n : ℕ) :
    ConjClasses (Perm (Fin n)) ≃ {l : List ℕ // IsPart l ∧ l.sum = n} := by
  refine Equiv.ofBijective
    (fun c => ⟨classCycleType c, ?_⟩) ⟨?_, ?_⟩
  · obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective c
    exact ⟨isPart_cycleTypeList σ, sum_cycleTypeList σ⟩
  · intro c d h
    obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective c
    obtain ⟨τ, rfl⟩ := ConjClasses.mk_surjective d
    have hst : cycleTypeList σ = cycleTypeList τ := congrArg Subtype.val h
    exact ConjClasses.mk_eq_mk_iff_isConj.2 (cycleTypeList_eq_iff_isConj.1 hst)
  · rintro ⟨l, hl, hn⟩
    obtain ⟨σ, hσ⟩ := exists_cycleTypeList_eq hl hn
    exact ⟨ConjClasses.mk σ, Subtype.ext hσ⟩

/-- The number of conjugacy classes of the symmetric group on `n` letters is the number of
partitions of `n`. -/
theorem nat_card_conjClasses_perm (n : ℕ) :
    Nat.card (ConjClasses (Perm (Fin n))) = Nat.card (Nat.Partition n) :=
  Nat.card_congr ((conjClassesEquivPart n).trans (listPartEquivNatPartition n))

end Equiv.Perm
