/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.Probability.Process.Filtration

/-!
# Filtration built from the finite partitions of a countably generated measurable space

In a countably generated measurable space `α`, we can  build a sequence of finer and finer finite
measurable partitions of the space such that the measurable space is generated by the union of all
partitions.
This sequence of partitions is defined in `MeasureTheory.MeasurableSpace.CountablyGenerated`.

Here, we build the filtration of the measurable spaces generated by `countablePartition α n` for all
`n : ℕ`, which we call `partitionFiltration α`.
Since each measurable space in the filtration is finite, we can easily build measurable functions on
those spaces. By building a martingale with respect to `partitionFiltration α` and using the
martingale convergence theorems, we can define a measurable function on `α`.

## Main definitions

* `ProbabilityTheory.partitionFiltration`: A filtration built from the measurable spaces generated
  by `countablePartition α n` for all `n : ℕ`.

## Main statements

* `ProbabilityTheory.iSup_partitionFiltration`: `⨆ n, partitionFiltration α n` is the measurable
  space on `α`.

-/

open MeasureTheory MeasurableSpace

namespace ProbabilityTheory

variable {α : Type*} [MeasurableSpace α] [CountablyGenerated α]

/-- A filtration built from the measurable spaces generated by `countablePartition α n` for
all `n : ℕ`. -/
def partitionFiltration (α : Type*) [m : MeasurableSpace α] [CountablyGenerated α] :
    Filtration ℕ m where
  seq := fun n ↦ generateFrom <| countablePartition α n
  mono' := monotone_nat_of_le_succ (generateFrom_countablePartition_le_succ _)
  le' := generateFrom_countablePartition_le α

lemma measurableSet_partitionFiltration_of_mem_countablePartition (n : ℕ) {s : Set α}
    (hs : s ∈ countablePartition α n) :
    MeasurableSet[partitionFiltration α n] s :=
  measurableSet_generateFrom hs

lemma measurableSet_partitionFiltration_partitionSet (n : ℕ) (t : α) :
    MeasurableSet[partitionFiltration α n] (partitionSet n t) :=
  measurableSet_partitionFiltration_of_mem_countablePartition n (partitionSet_mem n t)

lemma measurable_partitionSet_aux (n : ℕ) (m : MeasurableSpace (countablePartition α n)) :
    @Measurable α (countablePartition α n) (partitionFiltration α n) m
      (fun c : α ↦ ⟨partitionSet n c, partitionSet_mem n c⟩) := by
  refine @measurable_to_countable' (countablePartition α n) α m _
    (partitionFiltration α n) _ (fun t ↦ ?_)
  rcases t with ⟨t, ht⟩
  suffices MeasurableSet[partitionFiltration α n] {x | partitionSet n x = t} by
    convert this
    ext x
    simp
  have : {x | partitionSet n x = t} = t := by
    ext x
    rw [Set.mem_setOf_eq, ← partitionSet_eq_iff x ht]
  rw [this]
  exact measurableSet_partitionFiltration_of_mem_countablePartition _ ht

lemma measurable_partitionFiltration_partitionSet (α : Type*)
    [MeasurableSpace α] [CountablyGenerated α] (n : ℕ) :
    Measurable[partitionFiltration α n] (partitionSet n) :=
  measurable_subtype_coe.comp (measurable_partitionSet_aux _ _)

lemma measurable_partitionSet (α : Type*) [MeasurableSpace α] [CountablyGenerated α] (n : ℕ) :
    Measurable (partitionSet (α := α) n) :=
  (measurable_partitionFiltration_partitionSet α n).mono ((partitionFiltration α).le n) le_rfl

lemma iSup_partitionFiltration (α : Type*) [m : MeasurableSpace α] [CountablyGenerated α] :
    ⨆ n, partitionFiltration α n = m := by
  conv_rhs => rw [← generateFrom_iUnion_countablePartition α]
  rw [← iSup_generateFrom]
  rfl

end ProbabilityTheory
