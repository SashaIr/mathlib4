/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.SetPartition.Bell
public import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# The Stirling numbers of the second kind count set partitions

Ported from the Coq-Combi development (`Combi/set_partition.v`).

## Main results

* `Finpartition.sum_choose_stirlingSecond` : the binomial recursion
  `S(n+1, k+1) = ∑_j C(n, j) · S(n-j, k)`, obtained by splitting off the block containing
  a fixed element.
* `Finpartition.card_finpartition_card_parts` : the number of set partitions of a finite set of
  cardinality `n` into exactly `k` blocks is `Nat.stirlingSecond n k`.  (Mathlib defines
  `Nat.stirlingSecond` by its recursion only.)
* `Finpartition.stirlingSecond_eq_sum_multiset_bell` : the expansion of `Nat.stirlingSecond n k`
  as a sum over the partitions of `n` with `k` parts.
-/

@[expose] public section

namespace Finpartition

open Finset

/-! ### A binomial recursion for the Stirling numbers of the second kind -/

/-- Splitting off the block containing a fixed element gives
`S(n+1, k+1) = ∑_j C(n, j) · S(n-j, k)`. -/
lemma sum_choose_stirlingSecond (n : ℕ) : ∀ k : ℕ,
    ∑ j ∈ Finset.range (n + 1), n.choose j * Nat.stirlingSecond (n - j) k
      = Nat.stirlingSecond (n + 1) (k + 1) := by
  induction n with
  | zero => intro k; simp [Nat.stirlingSecond_succ_succ]
  | succ n ih =>
    intro k
    have hA : ∑ i ∈ Finset.range (n + 1), n.choose (i + 1) * Nat.stirlingSecond (n - i) k
        = ∑ i ∈ Finset.range n, n.choose (i + 1) * Nat.stirlingSecond (n - i) k := by
      rw [Finset.sum_range_succ, Nat.choose_succ_self, zero_mul, add_zero]
    have hLHS : ∑ j ∈ Finset.range (n + 2), (n + 1).choose j * Nat.stirlingSecond (n + 1 - j) k
        = (∑ i ∈ Finset.range (n + 1), n.choose i * Nat.stirlingSecond (n - i) k)
          + (∑ i ∈ Finset.range (n + 1), n.choose (i + 1) * Nat.stirlingSecond (n - i) k)
          + Nat.stirlingSecond (n + 1) k := by
      rw [Finset.sum_range_succ' (fun j => (n + 1).choose j * Nat.stirlingSecond (n + 1 - j) k)
        (n + 1)]
      simp only [Nat.choose_succ_succ, Nat.succ_sub_succ, Nat.choose_zero_right, one_mul,
        Nat.sub_zero, add_mul]
      rw [Finset.sum_add_distrib]
    have hU : ∑ j ∈ Finset.range (n + 1), n.choose j * Nat.stirlingSecond (n + 1 - j) k
        = (∑ i ∈ Finset.range n, n.choose (i + 1) * Nat.stirlingSecond (n - i) k)
          + Nat.stirlingSecond (n + 1) k := by
      rw [Finset.sum_range_succ' (fun j => n.choose j * Nat.stirlingSecond (n + 1 - j) k) n]
      simp only [Nat.succ_sub_succ, Nat.choose_zero_right, one_mul, Nat.sub_zero]
    rw [hLHS, hA, add_assoc, ← hU]
    cases k with
    | zero =>
      have hU0 : ∑ j ∈ Finset.range (n + 1), n.choose j * Nat.stirlingSecond (n + 1 - j) 0 = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have hrw : n + 1 - j = (n - j) + 1 := by omega
        rw [hrw, Nat.stirlingSecond_succ_zero, mul_zero]
      rw [hU0, add_zero, ih 0]
      simp [Nat.stirlingSecond_succ_succ]
    | succ k =>
      have hUval : ∑ j ∈ Finset.range (n + 1), n.choose j * Nat.stirlingSecond (n + 1 - j) (k + 1)
          = (k + 1) * (∑ i ∈ Finset.range (n + 1), n.choose i * Nat.stirlingSecond (n - i) (k + 1))
            + ∑ i ∈ Finset.range (n + 1), n.choose i * Nat.stirlingSecond (n - i) k := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have hrw : n + 1 - j = (n - j) + 1 := by omega
        rw [hrw, Nat.stirlingSecond_succ_succ]
        ring
      rw [hUval, ih (k + 1), ih k, Nat.stirlingSecond_succ_succ (n + 1) (k + 1)]
      ring

/-! ### Counting set partitions with a prescribed number of blocks -/

variable {α : Type*} [DecidableEq α]

/-- The set partitions of `s` with `k + 1` blocks in which the block of `a` is `B`
correspond to the set partitions of `s \ B` with `k` blocks. -/
lemma card_filter_part_eq_card {s : Finset α} {a : α} (ha : a ∈ s) {B : Finset α}
    (haB : a ∈ B) (hBs : B ⊆ s) (k : ℕ) :
    (Finset.univ.filter fun P : Finpartition s => P.part a = B ∧ P.parts.card = k + 1).card
      = (Finset.univ.filter fun Q : Finpartition (s \ B) => Q.parts.card = k).card := by
  classical
  have hBne : B ≠ ⊥ := fun h => by
    rw [h] at haB
    exact absurd haB (Finset.notMem_empty a)
  have hdis : Disjoint (s \ B) B := Finset.sdiff_disjoint
  have hsup : (s \ B) ⊔ B = s := Finset.sdiff_union_of_subset hBs
  have hBQ : ∀ Q : Finpartition (s \ B), B ∉ Q.parts := by
    intro Q hmem
    exact (Finset.mem_sdiff.1 (Q.subset hmem haB)).2 haB
  have hextend : ∀ Q : Finpartition (s \ B), (Q.extend hBne hdis hsup).part a = B := fun Q =>
    Finpartition.part_eq_of_mem _
      (by rw [Finpartition.extend_parts]; exact Finset.mem_insert_self _ _) haB
  refine Finset.card_bij' (fun P _ => P.avoid B) (fun Q _ => Q.extend hBne hdis hsup)
    (fun P hP => ?_) (fun Q hQ => ?_) (fun P hP => ?_) (fun Q hQ => ?_)
  · simp only [Finset.mem_filter] at hP ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hBmem : B ∈ P.parts := hP.2.1 ▸ (P.part_mem).2 ha
    rw [parts_avoid_of_mem P hBmem, Finset.card_erase_of_mem hBmem, hP.2.2]
    omega
  · simp only [Finset.mem_filter] at hQ ⊢
    exact ⟨Finset.mem_univ _, hextend Q, by
      rw [Finpartition.card_extend, hQ.2]⟩
  · simp only [Finset.mem_filter] at hP
    have hBmem : B ∈ P.parts := hP.2.1 ▸ (P.part_mem).2 ha
    refine Finpartition.ext ?_
    rw [Finpartition.extend_parts, parts_avoid_of_mem P hBmem, Finset.insert_erase hBmem]
  · refine Finpartition.ext ?_
    rw [parts_avoid_of_mem _ (by rw [Finpartition.extend_parts]; exact Finset.mem_insert_self _ _),
      Finpartition.extend_parts, Finset.erase_insert (hBQ Q)]

private theorem card_finpartition_card_parts_aux :
    ∀ (n : ℕ) (s : Finset α), s.card = n → ∀ k : ℕ,
      (Finset.univ.filter fun P : Finpartition s => P.parts.card = k).card
        = Nat.stirlingSecond n k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs k
    classical
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hsempty : s = ∅ := Finset.card_eq_zero.1 hs
      subst hsempty
      have hall : ∀ P : Finpartition (∅ : Finset α), P.parts = ∅ := fun P =>
        Finpartition.parts_eq_empty_iff.2 rfl
      cases k with
      | zero =>
        have hfil : (Finset.univ.filter fun P : Finpartition (∅ : Finset α) => P.parts.card = 0)
            = Finset.univ :=
          Finset.filter_true_of_mem fun P _ => by rw [hall P, Finset.card_empty]
        rw [hfil, Finset.card_univ, card_finpartition]
        simp
      | succ k =>
        have hfil : (Finset.univ.filter fun P : Finpartition (∅ : Finset α) =>
            P.parts.card = k + 1) = ∅ :=
          Finset.filter_false_of_mem fun P _ => by rw [hall P, Finset.card_empty]; omega
        rw [hfil]
        simp
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨a, ha⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
    have hsne : s ≠ ⊥ := by
      intro h
      rw [h] at hs
      simp at hs
    cases k with
    | zero =>
      have hfil : (Finset.univ.filter fun P : Finpartition s => P.parts.card = 0) = ∅ := by
        refine Finset.filter_false_of_mem fun P _ => ?_
        have h2 : 0 < P.parts.card := Finset.card_pos.2 (Finpartition.parts_nonempty P hsne)
        omega
      rw [hfil]
      simp
    | succ k =>
      set blocks := s.powerset.filter fun B => a ∈ B with hblocks
      have hmemb : ∀ B ∈ blocks, a ∈ B ∧ B ⊆ s := by
        intro B hB
        simp only [hblocks, Finset.mem_filter, Finset.mem_powerset] at hB
        exact ⟨hB.2, hB.1⟩
      have hcov : (Finset.univ.filter fun P : Finpartition s => P.parts.card = k + 1)
          = blocks.biUnion fun B =>
              Finset.univ.filter fun P : Finpartition s => P.part a = B ∧ P.parts.card = k + 1 := by
        apply Finset.Subset.antisymm
        · intro P hP
          simp only [Finset.mem_filter] at hP
          refine Finset.mem_biUnion.2 ⟨P.part a, ?_, ?_⟩
          · simp only [hblocks, Finset.mem_filter, Finset.mem_powerset]
            exact ⟨Finpartition.part_subset P a, (P.mem_part_self).2 ha⟩
          · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, hP.2⟩
        · intro P hP
          obtain ⟨B, -, hPB⟩ := Finset.mem_biUnion.1 hP
          simp only [Finset.mem_filter] at hPB ⊢
          exact ⟨Finset.mem_univ _, hPB.2.2⟩
      have hpwd : (↑blocks : Set (Finset α)).PairwiseDisjoint
          fun B => Finset.univ.filter fun P : Finpartition s =>
            P.part a = B ∧ P.parts.card = k + 1 := by
        intro B _ C _ hBC
        refine Finset.disjoint_left.2 fun P hPB hPC => ?_
        simp only [Finset.mem_filter] at hPB hPC
        exact hBC (hPB.2.1.symm.trans hPC.2.1)
      have hterm : ∀ B ∈ blocks,
          (Finset.univ.filter fun P : Finpartition s =>
              P.part a = B ∧ P.parts.card = k + 1).card
            = Nat.stirlingSecond (m + 1 - B.card) k := by
        intro B hB
        obtain ⟨haB, hBs⟩ := hmemb B hB
        have hcards : (s \ B).card = m + 1 - B.card := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.2 hBs, hs]
        have hBpos : 0 < B.card := Finset.card_pos.2 ⟨a, haB⟩
        have hlt : (s \ B).card < m + 1 := by rw [hcards]; omega
        rw [card_filter_part_eq_card ha haB hBs k, ih _ hlt _ rfl, hcards]
      rw [hcov, Finset.card_biUnion hpwd, Finset.sum_congr rfl hterm]
      have hcarderase : (s.erase a).card = m := by
        rw [Finset.card_erase_of_mem ha, hs]
        omega
      have hreindex : ∑ B ∈ blocks, Nat.stirlingSecond (m + 1 - B.card) k
          = ∑ C ∈ (s.erase a).powerset, Nat.stirlingSecond (m - C.card) k := by
        refine Finset.sum_bij' (fun B _ => B.erase a) (fun C _ => insert a C) ?_ ?_ ?_ ?_ ?_
        · intro B hB
          obtain ⟨haB, hBs⟩ := hmemb B hB
          exact Finset.mem_powerset.2 (Finset.erase_subset_erase a hBs)
        · intro C hC
          simp only [hblocks, Finset.mem_filter, Finset.mem_powerset]
          refine ⟨?_, Finset.mem_insert_self _ _⟩
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact ha
          · exact Finset.mem_of_mem_erase (Finset.mem_powerset.1 hC hx)
        · intro B hB
          exact Finset.insert_erase (hmemb B hB).1
        · intro C hC
          exact Finset.erase_insert fun h => (Finset.mem_erase.1 (Finset.mem_powerset.1 hC h)).1 rfl
        · intro B hB
          obtain ⟨haB, -⟩ := hmemb B hB
          have hc : B.card = (B.erase a).card + 1 := by
            rw [Finset.card_erase_of_mem haB]
            have := Finset.card_pos.2 (⟨a, haB⟩ : B.Nonempty)
            omega
          change Nat.stirlingSecond (m + 1 - B.card) k = Nat.stirlingSecond (m - (B.erase a).card) k
          rw [hc]
          congr 1
          omega
      rw [hreindex, Finset.sum_powerset, hcarderase]
      rw [← sum_choose_stirlingSecond m k]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_congr rfl (fun C hC => by
        rw [(Finset.mem_powersetCard.1 hC).2] : ∀ C ∈ Finset.powersetCard j (s.erase a),
          Nat.stirlingSecond (m - C.card) k = Nat.stirlingSecond (m - j) k), Finset.sum_const,
        Finset.card_powersetCard, hcarderase, smul_eq_mul]

/-- **The Stirling numbers of the second kind count set partitions**: a finite set `s` has
exactly `Nat.stirlingSecond |s| k` set partitions into `k` blocks. -/
theorem card_finpartition_card_parts (s : Finset α) (k : ℕ) :
    (Finset.univ.filter fun P : Finpartition s => P.parts.card = k).card
      = Nat.stirlingSecond s.card k :=
  card_finpartition_card_parts_aux s.card s rfl k

/-! ### The Stirling numbers as a sum of refined Bell numbers -/

lemma card_partShape {s : Finset α} (P : Finpartition s) :
    Multiset.card (partShape P) = P.parts.card := by
  rw [partShape, Multiset.card_map]
  rfl

/-- Every set partition of `Fin n` has, as its multiset of block sizes, a partition of the
integer `n`. -/
lemma exists_natPartition_partShape {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    ∃ p : n.Partition, partShape P = p.parts := by
  have hs : (Finset.univ : Finset (Fin n)).card = n := by simp
  refine ⟨⟨partShape P, ?_, ?_⟩, rfl⟩
  · intro i hi
    obtain ⟨B, hB, rfl⟩ := Multiset.mem_map.1 hi
    exact Finset.card_pos.2 (P.nonempty_of_mem_parts hB)
  · exact (Finpartition.sum_card_parts P).trans hs

/-- **The Stirling numbers of the second kind as a sum of refined Bell numbers**: grouping
the set partitions into `k` blocks by their multiset of block sizes. -/
theorem stirlingSecond_eq_sum_multiset_bell (n k : ℕ) :
    Nat.stirlingSecond n k
      = ∑ p ∈ Finset.univ.filter (fun p : Nat.Partition n => Multiset.card p.parts = k),
          Multiset.bell p.parts := by
  classical
  have hs : (Finset.univ : Finset (Fin n)).card = n := by simp
  have h1 : Nat.stirlingSecond n k
      = (Finset.univ.filter fun P : Finpartition (Finset.univ : Finset (Fin n)) =>
          P.parts.card = k).card := by
    rw [card_finpartition_card_parts, hs]
  rw [h1]
  have hcov : (Finset.univ.filter fun P : Finpartition (Finset.univ : Finset (Fin n)) =>
        P.parts.card = k)
      = (Finset.univ.filter fun p : Nat.Partition n => Multiset.card p.parts = k).biUnion
        fun p => shapeParts (Finset.univ : Finset (Fin n)) p.parts := by
    apply Finset.Subset.antisymm
    · intro P hP
      simp only [Finset.mem_filter] at hP
      obtain ⟨p, hp⟩ := exists_natPartition_partShape P
      refine Finset.mem_biUnion.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩,
        mem_shapeParts.2 hp⟩
      rw [← hp, card_partShape, hP.2]
    · intro P hP
      obtain ⟨p, hp, hPp⟩ := Finset.mem_biUnion.1 hP
      simp only [Finset.mem_filter] at hp ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← card_partShape, mem_shapeParts.1 hPp, hp.2]
  have hdisj : (↑(Finset.univ.filter fun p : Nat.Partition n => Multiset.card p.parts = k) :
        Set (Nat.Partition n)).PairwiseDisjoint
      (fun p => shapeParts (Finset.univ : Finset (Fin n)) p.parts) := by
    intro p _ q _ hpq
    refine Finset.disjoint_left.2 fun P hPp hPq => ?_
    exact hpq (Nat.Partition.ext ((mem_shapeParts.1 hPp).symm.trans (mem_shapeParts.1 hPq)))
  rw [hcov, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl fun (p : Nat.Partition n) _ =>
    card_shapeParts (Finset.univ : Finset (Fin n)) p.parts
      (fun h => absurd (p.parts_pos h) (lt_irrefl 0)) (by rw [p.parts_sum, hs])

end Finpartition
