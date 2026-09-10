/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.ErdosSzekeresList
public import Mathlib.Data.Finset.Sort

/-!
# Erdős–Szekeres theorem

This file proves Theorem 73 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/), also
known as the Erdős–Szekeres theorem: given a sequence of more than `r * s` distinct
values, there is an increasing sequence of length longer than `r` or a decreasing sequence of length
longer than `s`.

The combinatorial content is `List.erdos_szekeres`, in
`Mathlib/Combinatorics/ErdosSzekeresList.lean`: a list of more than `r * s` entries has a weakly
increasing sublist of more than `r` entries, or a strictly decreasing sublist of more than `s`
entries — no injectivity assumption there.  Here that statement is transported to a finite
linearly ordered type `α` and an injective `f : α → β`, by applying it to the list of the elements
of `α` in increasing order, mapped by `f`: a sublist of that list is the image of a sublist `u` of
the sorted list, which is strictly increasing, and the injectivity of `f` upgrades the weakly
increasing chain of values to a strictly increasing one.

## Tags

sequences, increasing, decreasing, Ramsey, Erdos-Szekeres, Erdős–Szekeres, Erdős-Szekeres
-/

@[expose] public section

open Function Finset

namespace Theorems100

variable {α β : Type*} [LinearOrder α] [LinearOrder β] {f : α → β}

/-- If the entries of `l` increase and the values of `f` on them do not decrease, then `f` is
strictly monotone on the elements of `l`, provided `f` is injective. -/
private lemma strictMonoOn_of_pairwise (hinj : Injective f) {l : List α}
    (hlt : l.Pairwise (· < ·)) (hle : l.Pairwise fun a b => f a ≤ f b) :
    StrictMonoOn f {x | x ∈ l} := by
  intro a ha b hb hab
  simp only [Set.mem_ofPred_eq] at ha hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  rcases lt_trichotomy i j with h | rfl | h
  · exact lt_of_le_of_ne (List.pairwise_iff_getElem.1 hle i j hi hj h)
      fun e => absurd (hinj e) hab.ne
  · exact absurd rfl hab.ne
  · exact absurd (List.pairwise_iff_getElem.1 hlt j i hj hi h) (asymm hab)

/-- If the entries of `l` increase and the values of `f` on them decrease, then `f` is strictly
antitone on the elements of `l`. -/
private lemma strictAntiOn_of_pairwise {l : List α}
    (hlt : l.Pairwise (· < ·)) (hgt : l.Pairwise fun a b => f b < f a) :
    StrictAntiOn f {x | x ∈ l} := by
  intro a ha b hb hab
  simp only [Set.mem_ofPred_eq] at ha hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  rcases lt_trichotomy i j with h | rfl | h
  · exact List.pairwise_iff_getElem.1 hgt i j hi hj h
  · exact absurd rfl hab.ne
  · exact absurd (List.pairwise_iff_getElem.1 hlt j i hj hi h) (asymm hab)

/--
**Erdős–Szekeres Theorem**: Given a sequence of more than `r * s` distinct values, there is an
increasing sequence of length longer than `r` or a decreasing sequence of length longer than `s`.

This is the list statement `List.erdos_szekeres` applied to the elements of `α` listed in
increasing order.
-/
theorem erdos_szekeres [Fintype α] {r s : ℕ} {f : α → β} (hn : r * s < Fintype.card α)
    (hf : Injective f) :
    (∃ t : Finset α, r < #t ∧ StrictMonoOn f t) ∨
      ∃ t : Finset α, s < #t ∧ StrictAntiOn f t := by
  classical
  set L : List α := (univ : Finset α).sort (· ≤ ·) with hL
  have hsorted : L.Pairwise (· < ·) :=
    (List.pairwise_and_iff.2 ⟨Finset.pairwise_sort _ _, Finset.sort_nodup _ _⟩).imp
      lt_iff_le_and_ne.2
  have hlen : (L.map f).length = Fintype.card α := by simp [hL]
  obtain ⟨t, hsub, hchain, hcard⟩ | ⟨t, hsub, hchain, hcard⟩ :=
    List.erdos_szekeres r s (L.map f) (by rw [hlen]; exact hn)
  · obtain ⟨u, husub, rfl⟩ := List.sublist_map_iff.1 hsub
    have hu : u.Pairwise (· < ·) := hsorted.sublist husub
    refine Or.inl ⟨u.toFinset, ?_, ?_⟩
    · rw [List.toFinset_card_of_nodup (hu.imp ne_of_lt)]
      simpa using hcard
    · rw [List.coe_toFinset]
      refine strictMonoOn_of_pairwise hf hu ?_
      have := List.isChain_iff_pairwise.1 hchain
      rwa [List.pairwise_map] at this
  · obtain ⟨u, husub, rfl⟩ := List.sublist_map_iff.1 hsub
    have hu : u.Pairwise (· < ·) := hsorted.sublist husub
    refine Or.inr ⟨u.toFinset, ?_, ?_⟩
    · rw [List.toFinset_card_of_nodup (hu.imp ne_of_lt)]
      simpa using hcard
    · rw [List.coe_toFinset]
      refine strictAntiOn_of_pairwise hu ?_
      have := List.isChain_iff_pairwise.1 hchain
      rwa [List.pairwise_map] at this

end Theorems100
