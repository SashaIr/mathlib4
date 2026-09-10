/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.RobinsonSchensted.Counting
public import Mathlib.Combinatorics.Young.Tableau.Restrict

/-!
# The branching rule for standard Young tableaux

Removing the box containing the largest letter of a standard tableau of shape `η` gives a
standard tableau whose shape is `η` with a removable corner removed.  This is the
*branching rule*

`f^η = ∑_{r a removable corner of η} f^{η - r}`

for the number `f^η = numStdTab η` of standard tableaux of shape `η`.  It is the
combinatorial input of the hook length formula.

The proof identifies standard tableaux of shape `η` with the tableaux counted by the Kostka number
`K_{η, (1, …, 1)}` and specialises the recursion on the largest letter `Young.kostkaNum_succ` of
`Mathlib.Combinatorics.Young.Tableau.Restrict`: a horizontal strip of size one is exactly a
removable corner.

## Main results

* `Young.numStdTab_eq_kostkaNum` : standard tableaux of shape `μ` are the tableaux of shape
  `μ` with letters `< |μ|` and content `(1, …, 1)`.
* `Young.horizStrip_decrNth` : removing a removable corner gives a horizontal strip.
* `Young.exists_remCorner_of_included_succ` : conversely, a partition contained in `η` with
  one box less is `η` with a removable corner removed.
* `Young.numStdTab_branching` : the branching rule.
-/

@[expose] public section

namespace Young

open List

/-! ### Standard tableaux as tableaux with content `(1, …, 1)` -/

/-- The reading word of a tableau is a permutation of the concatenation of its rows. -/
lemma perm_toWord_flatten (t : List (List ℕ)) : (toWord t).Perm t.flatten :=
  (List.reverse_perm t).flatten

/-- The tableaux of shape `μ` with letters `< |μ|` in which every letter occurs exactly
once are the standard tableaux of shape `μ`. -/
lemma tabSet_one (μ : List ℕ) :
    tabSet μ.sum μ (fun _ => 1) = {P | IsStdTab P ∧ shape P = μ} := by
  ext P
  simp only [tabSet, Set.mem_ofPred_eq, IsStdTab]
  constructor
  · rintro ⟨htab, hμ, hlt, hcount⟩
    refine ⟨⟨htab, ?_⟩, hμ⟩
    have hlen : (toWord P).length = μ.sum := by
      rw [length_toWord, sizeTab, hμ]
    rw [IsStd, hlen, List.perm_iff_count]
    intro a
    rw [(perm_toWord_flatten P).count_eq, List.count_range]
    by_cases ha : a < μ.sum
    · rw [ite_eq_left ha]; exact hcount a ha
    · rw [ite_eq_right ha]
      exact List.count_eq_zero_of_not_mem fun hmem => ha (hlt a hmem)
  · rintro ⟨⟨htab, hstd⟩, hμ⟩
    have hlen : (toWord P).length = μ.sum := by
      rw [length_toWord, sizeTab, hμ]
    rw [IsStd, hlen, List.perm_iff_count] at hstd
    have hcount : ∀ a, P.flatten.count a = if a < μ.sum then 1 else 0 := fun a => by
      rw [← (perm_toWord_flatten P).count_eq, hstd a, List.count_range]
    refine ⟨htab, hμ, fun x hx => ?_, fun i hi => by rw [hcount i, ite_eq_left hi]⟩
    by_contra hxlt
    have hx0 := hcount x
    rw [ite_eq_right hxlt] at hx0
    exact absurd hx0 (by simp [List.count_eq_zero, hx])

/-- The number of standard tableaux of shape `μ` is the Kostka number
`K_{μ, (1, …, 1)}`. -/
theorem numStdTab_eq_kostkaNum (μ : List ℕ) :
    numStdTab μ = kostkaNum μ.sum μ (fun _ => 1) := by
  rw [numStdTab, kostkaNum, tabSet_one]
  rfl

/-! ### Horizontal strips of size one -/

/-- Removing a removable corner from a partition gives a horizontal strip. -/
lemma horizStrip_decrNth {η : List ℕ} {r : ℕ} (hη : IsPart η) (hc : IsRemCorner η r) :
    HorizStrip η (decrNth η r) := by
  refine ⟨included_decrNth η r, fun i => ?_⟩
  rcases eq_or_ne i r with rfl | h
  · rw [getD_decrNth_self]
    rw [IsRemCorner] at hc
    omega
  · rw [getD_decrNth_of_ne hη hc (Ne.symm h)]
    exact hη.getD_antitone (Nat.le_succ i)

/-- A partition contained in `η` and having one box less is `η` with a removable corner
removed. -/
lemma exists_remCorner_of_included_succ {η ν : List ℕ} (hη : IsPart η) (hν : IsPart ν)
    (hinc : Included ν η) (hsum : η.sum = ν.sum + 1) :
    ∃ r, IsRemCorner η r ∧ ν = decrNth η r := by
  classical
  set L := η.length with hL
  have hle : ∀ i, ν.getD i 0 ≤ η.getD i 0 := hinc.getD_le
  have h1 : η.sum = ∑ i ∈ Finset.range L, η.getD i 0 := sum_eq_sum_range η le_rfl
  have h2 : ν.sum = ∑ i ∈ Finset.range L, ν.getD i 0 := sum_eq_sum_range ν hinc.length_le
  set d : ℕ → ℕ := fun i => η.getD i 0 - ν.getD i 0 with hd
  have hsplit : ∑ i ∈ Finset.range L, η.getD i 0
      = (∑ i ∈ Finset.range L, ν.getD i 0) + ∑ i ∈ Finset.range L, d i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by have := hle i; simp only [hd]; omega
  have hdsum : ∑ i ∈ Finset.range L, d i = 1 := by
    rw [h1, h2] at hsum
    omega
  obtain ⟨r, hrmem, hr0⟩ : ∃ r ∈ Finset.range L, d r ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_congr rfl fun i hi => hcon i hi] at hdsum
    simp at hdsum
  have hsplit2 : d r + ∑ i ∈ (Finset.range L).erase r, d i = 1 := by
    rw [Finset.add_sum_erase _ _ hrmem]
    exact hdsum
  have hdr : d r = 1 := by omega
  have hzero : ∀ i, i ≠ r → d i = 0 := by
    intro i hi
    rcases lt_or_ge i L with hiL | hiL
    · have hmem : i ∈ (Finset.range L).erase r := Finset.mem_erase.2 ⟨hi, Finset.mem_range.2 hiL⟩
      have hsum0 : ∑ i ∈ (Finset.range L).erase r, d i = 0 := by omega
      exact (Finset.sum_eq_zero_iff.1 hsum0) i hmem
    · have : η.getD i 0 = 0 := List.getD_eq_default _ _ hiL
      simp only [hd, this]
      omega
  have hne : ∀ i, i ≠ r → ν.getD i 0 = η.getD i 0 := by
    intro i hi
    have := hzero i hi
    have := hle i
    simp only [hd] at *
    omega
  have hrval : ν.getD r 0 + 1 = η.getD r 0 := by
    have := hle r
    simp only [hd] at hdr
    omega
  have hcorner : IsRemCorner η r := by
    rw [IsRemCorner, ← hne (r + 1) (by omega)]
    calc ν.getD (r + 1) 0 ≤ ν.getD r 0 := hν.getD_antitone (Nat.le_succ r)
      _ < η.getD r 0 := by omega
  refine ⟨r, hcorner, hν.ext_getD (isPart_decrNth hη hcorner) fun i => ?_⟩
  rcases eq_or_ne i r with rfl | hi
  · rw [getD_decrNth_self]
    omega
  · rw [getD_decrNth_of_ne hη hcorner (Ne.symm hi)]
    exact hne i hi

/-- A removable corner is a row of the partition. -/
lemma IsRemCorner.lt_length {η : List ℕ} {r : ℕ} (hc : IsRemCorner η r) : r < η.length := by
  by_contra h
  rw [IsRemCorner, List.getD_eq_default _ _ (not_lt.1 h)] at hc
  omega

/-! ### The branching rule -/

open Classical in
/-- **The branching rule for standard tableaux**: the number of standard tableaux of shape
`η` is the sum of the numbers of standard tableaux of the shapes obtained by removing a
removable corner of `η`. -/
theorem numStdTab_branching {η : List ℕ} (hη : IsPart η) {n N : ℕ} (hsum : η.sum = n + 1)
    (hN : η.length ≤ N) :
    numStdTab η
      = ∑ r ∈ Finset.range N, if IsRemCorner η r then numStdTab (decrNth η r) else 0 := by
  classical
  have hkos : numStdTab η
      = ∑ ν : {p : List ℕ // IsPart p ∧ p.sum = n},
          if HorizStrip η ν.1 then numStdTab ν.1 else 0 := by
    rw [numStdTab_eq_kostkaNum, hsum,
      kostkaNum_succ (N := n) (c := fun _ => 1) (m := n) hη (by simp [hsum])]
    refine Finset.sum_congr rfl fun ν _ => ?_
    by_cases h : HorizStrip η ν.1
    · rw [ite_eq_left h, ite_eq_left h, numStdTab_eq_kostkaNum, ν.2.2]
    · rw [ite_eq_right h, ite_eq_right h]
  rw [hkos, ← Finset.sum_filter, ← Finset.sum_filter]
  refine (Finset.sum_bij
    (fun (r : ℕ) (hr : r ∈ (Finset.range N).filter (IsRemCorner η)) =>
      (⟨decrNth η r, isPart_decrNth hη (Finset.mem_filter.1 hr).2, by
        rw [sum_decrNth hη (Finset.mem_filter.1 hr).2, hsum]
        omega⟩ :
        {p : List ℕ // IsPart p ∧ p.sum = n}))
    (fun r hr => Finset.mem_filter.2 ⟨Finset.mem_univ _,
      horizStrip_decrNth hη (Finset.mem_filter.1 hr).2⟩)
    ?_ ?_ (fun r _ => rfl)).symm
  · intro r hr r' hr' heq
    have hc : IsRemCorner η r := (Finset.mem_filter.1 hr).2
    have hc' : IsRemCorner η r' := (Finset.mem_filter.1 hr').2
    have heq' : decrNth η r = decrNth η r' := congrArg Subtype.val heq
    by_contra hne
    have h1 : (decrNth η r).getD r 0 = η.getD r 0 - 1 := getD_decrNth_self η r
    have h2 : (decrNth η r').getD r 0 = η.getD r 0 :=
      getD_decrNth_of_ne hη hc' fun h => hne h.symm
    rw [heq', h2] at h1
    rw [IsRemCorner] at hc
    omega
  · intro ν hν
    have hstrip : HorizStrip η ν.1 := (Finset.mem_filter.1 hν).2
    obtain ⟨r, hc, hr⟩ := exists_remCorner_of_included_succ hη ν.2.1 hstrip.included
      (by rw [hsum, ν.2.2])
    exact ⟨r, Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_of_lt_of_le hc.lt_length hN), hc⟩,
      Subtype.ext hr.symm⟩

end Young
