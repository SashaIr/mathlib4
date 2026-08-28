/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.SetPartition.Basic

/-!
# The Bell numbers count set partitions

Ported from the Coq-Combi development (`Combi/set_partition.v`).

## Main results

* `Finpartition.card_finpartition` : the number of set partitions of a finite set of
  cardinality `n` is `Nat.bell n`.  (Mathlib defines `Nat.bell` by its recursion and
  leaves the combinatorial interpretation as an open TODO.)
* `Finpartition.nat_bell_eq_sum_multiset_bell` : `Nat.bell n` is the sum of `Multiset.bell p`
  over the partitions `p` of `n`.
-/

namespace Finpartition

open Finset

variable {α : Type*} [DecidableEq α]

/-- Removing a part `B` from a finite partition, in the sense of `Finpartition.avoid`,
just erases `B` from the set of parts. -/
lemma parts_avoid_of_mem {s : Finset α} (P : Finpartition s) {B : Finset α}
    (hB : B ∈ P.parts) : (P.avoid B).parts = P.parts.erase B := by
  ext C
  rw [Finpartition.mem_avoid, Finset.mem_erase]
  constructor
  · rintro ⟨d, hd, hdB, rfl⟩
    have hdne : d ≠ B := by rintro rfl; exact hdB le_rfl
    have hdis : Disjoint d B := P.disjoint hd hB hdne
    rw [Finset.sdiff_eq_self_iff_disjoint.2 hdis]
    exact ⟨hdne, hd⟩
  · rintro ⟨hCB, hC⟩
    have hdis : Disjoint C B := P.disjoint hC hB hCB
    refine ⟨C, hC, fun hle => P.ne_empty hC (hdis.eq_bot_of_le hle),
      Finset.sdiff_eq_self_iff_disjoint.2 hdis⟩

/-- The set partitions of `s` in which the part of `a` is a fixed block `B` correspond to
the set partitions of `s \ B`. -/
lemma card_filter_part_eq {s : Finset α} {a : α} (ha : a ∈ s) {B : Finset α}
    (haB : a ∈ B) (hBs : B ⊆ s) :
    (Finset.univ.filter fun P : Finpartition s => P.part a = B).card
      = Fintype.card (Finpartition (s \ B)) := by
  classical
  have hBne : B ≠ ⊥ := fun h => by
    rw [h] at haB
    exact absurd haB (Finset.notMem_empty a)
  have hdis : Disjoint (s \ B) B := Finset.sdiff_disjoint
  have hsup : (s \ B) ⊔ B = s := Finset.sdiff_union_of_subset hBs
  rw [← Finset.card_univ]
  refine Finset.card_bij' (fun P _ => P.avoid B) (fun Q _ => Q.extend hBne hdis hsup)
    (fun _ _ => Finset.mem_univ _) (fun Q _ => ?_) ?_ ?_
  · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    exact Finpartition.part_eq_of_mem _
      (by rw [Finpartition.extend_parts]; exact Finset.mem_insert_self _ _) haB
  · intro P hP
    simp only [Finset.mem_filter] at hP
    have hBmem : B ∈ P.parts := hP.2 ▸ (P.part_mem).2 ha
    refine Finpartition.ext ?_
    rw [Finpartition.extend_parts, parts_avoid_of_mem P hBmem, Finset.insert_erase hBmem]
  · intro Q _
    have hBQ : B ∉ Q.parts := by
      intro hmem
      have := Q.subset hmem haB
      exact (Finset.mem_sdiff.1 this).2 haB
    refine Finpartition.ext ?_
    rw [parts_avoid_of_mem _ (by rw [Finpartition.extend_parts]; exact Finset.mem_insert_self _ _),
      Finpartition.extend_parts, Finset.erase_insert hBQ]

/-- **The Bell numbers count set partitions.** -/
theorem card_finpartition_aux :
    ∀ (n : ℕ) (s : Finset α), s.card = n → Fintype.card (Finpartition s) = Nat.bell n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    classical
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hsempty : s = ∅ := Finset.card_eq_zero.1 hs
      subst hsempty
      rw [Nat.bell_zero]
      refine Fintype.card_eq_one_iff.2 ⟨⊥, fun P => Finpartition.ext ?_⟩
      rw [Finpartition.parts_eq_empty_iff.2 rfl, Finpartition.parts_eq_empty_iff.2 rfl]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨a, ha⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
    set blocks := s.powerset.filter fun B => a ∈ B with hblocks
    have hcov : (Finset.univ : Finset (Finpartition s))
        = blocks.biUnion fun B => Finset.univ.filter fun P => P.part a = B := by
      apply Finset.Subset.antisymm
      · intro P _
        refine Finset.mem_biUnion.2 ⟨P.part a, ?_, ?_⟩
        · simp only [hblocks, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finpartition.part_subset P a, (P.mem_part_self).2 ha⟩
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
      · exact fun P _ => Finset.mem_univ _
    have hpwd : ∀ B ∈ blocks, ∀ C ∈ blocks, B ≠ C →
        Disjoint (Finset.univ.filter fun P : Finpartition s => P.part a = B)
          (Finset.univ.filter fun P : Finpartition s => P.part a = C) := by
      intro B _ C _ hBC
      refine Finset.disjoint_left.2 fun P hPB hPC => ?_
      simp only [Finset.mem_filter] at hPB hPC
      exact hBC (hPB.2.symm.trans hPC.2)
    have hmemb : ∀ B ∈ blocks, a ∈ B ∧ B ⊆ s := by
      intro B hB
      simp only [hblocks, Finset.mem_filter, Finset.mem_powerset] at hB
      exact ⟨hB.2, hB.1⟩
    have hterm : ∀ B ∈ blocks,
        (Finset.univ.filter fun P : Finpartition s => P.part a = B).card
          = Nat.bell (m + 1 - B.card) := by
      intro B hB
      obtain ⟨haB, hBs⟩ := hmemb B hB
      have hcards : (s \ B).card = m + 1 - B.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.2 hBs, hs]
      have hBpos : 0 < B.card := Finset.card_pos.2 ⟨a, haB⟩
      have hlt : (s \ B).card < m + 1 := by rw [hcards]; omega
      rw [card_filter_part_eq ha haB hBs, ih _ hlt _ rfl, hcards]
    rw [← Finset.card_univ, hcov, Finset.card_biUnion hpwd, Finset.sum_congr rfl hterm]
    -- reindex the blocks containing `a` by the subsets of `s.erase a`
    have hcarderase : (s.erase a).card = m := by
      rw [Finset.card_erase_of_mem ha, hs]
      omega
    have hreindex : ∑ B ∈ blocks, Nat.bell (m + 1 - B.card)
        = ∑ C ∈ (s.erase a).powerset, Nat.bell (m - C.card) := by
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
        change Nat.bell (m + 1 - B.card) = Nat.bell (m - (B.erase a).card)
        rw [hc]
        congr 1
        omega
    rw [hreindex, Finset.sum_powerset, hcarderase, Nat.bell_succ,
      Fin.sum_univ_eq_sum_range (fun i => Nat.choose m i * Nat.bell (m - i)) (m + 1)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl (fun C hC => by
      rw [(Finset.mem_powersetCard.1 hC).2] : ∀ C ∈ Finset.powersetCard j (s.erase a),
        Nat.bell (m - C.card) = Nat.bell (m - j)), Finset.sum_const,
      Finset.card_powersetCard, hcarderase, smul_eq_mul]

/-- **The Bell numbers count set partitions**: a finite set `s` has `Nat.bell |s|` set
partitions. -/
theorem card_finpartition (s : Finset α) :
    Fintype.card (Finpartition s) = Nat.bell s.card :=
  card_finpartition_aux s.card s rfl

/-- **The Bell number is the sum of the refined Bell numbers.**  The number of set
partitions of an `n`-element set is the sum, over the partitions `p` of the integer `n`,
of the number `Multiset.bell p.parts` of set partitions with block sizes `p`. -/
theorem nat_bell_eq_sum_multiset_bell (n : ℕ) :
    Nat.bell n = ∑ p : n.Partition, Multiset.bell p.parts := by
  classical
  have hs : (Finset.univ : Finset (Fin n)).card = n := by simp
  have h1 : Nat.bell n = Fintype.card (Finpartition (Finset.univ : Finset (Fin n))) := by
    rw [card_finpartition, hs]
  rw [h1, ← Finset.card_univ]
  have hshape : ∀ P : Finpartition (Finset.univ : Finset (Fin n)),
      ∃ p : n.Partition, partShape P = p.parts := by
    intro P
    refine ⟨⟨partShape P, ?_, ?_⟩, rfl⟩
    · intro i hi
      obtain ⟨B, hB, rfl⟩ := Multiset.mem_map.1 hi
      exact Finset.card_pos.2 (P.nonempty_of_mem_parts hB)
    · exact (Finpartition.sum_card_parts P).trans hs
  have hcov : (Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin n))))
      = (Finset.univ : Finset (Nat.Partition n)).biUnion
        fun p => shapeParts (Finset.univ : Finset (Fin n)) p.parts := by
    apply Finset.Subset.antisymm
    · intro P _
      obtain ⟨p, hp⟩ := hshape P
      exact Finset.mem_biUnion.2 ⟨p, Finset.mem_univ _, mem_shapeParts.2 hp⟩
    · exact fun P _ => Finset.mem_univ _
  have hdisj : (↑(Finset.univ : Finset (Nat.Partition n)) :
        Set (Nat.Partition n)).PairwiseDisjoint
      (fun p => shapeParts (Finset.univ : Finset (Fin n)) p.parts) := by
    intro p _ q _ hpq
    refine Finset.disjoint_left.2 fun P hPp hPq => ?_
    exact hpq (Nat.Partition.ext ((mem_shapeParts.1 hPp).symm.trans (mem_shapeParts.1 hPq)))
  rw [hcov, Finset.card_biUnion (M := Finpartition (Finset.univ : Finset (Fin n)))
    (t := fun p : Nat.Partition n => shapeParts (Finset.univ : Finset (Fin n)) p.parts) hdisj]
  exact Finset.sum_congr (rfl : (Finset.univ : Finset (Nat.Partition n)) = Finset.univ)
    fun (p : Nat.Partition n) _ =>
    card_shapeParts (Finset.univ : Finset (Fin n)) p.parts
      (fun h => absurd (p.parts_pos h) (lt_irrefl 0)) (by rw [p.parts_sum, hs])

end Finpartition
