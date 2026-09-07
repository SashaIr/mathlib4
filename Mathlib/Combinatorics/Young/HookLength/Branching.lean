/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Tableau.Restrict
import Mathlib.Combinatorics.Young.RobinsonSchensted.Counting

/-!
# The branching rule for standard Young tableaux

Removing the box containing the largest letter of a standard tableau of shape `lam` gives a
standard tableau whose shape is `lam` with a removable corner removed.  This is the
*branching rule*

`f^lam = ∑_{r a removable corner of lam} f^{lam - r}`

for the number `f^lam = numStdTab lam` of standard tableaux of shape `lam`.  It is the
combinatorial input of the hook length formula.

The proof identifies standard tableaux of shape `lam` with the tableaux counted by the Kostka number
`K_{lam, (1, …, 1)}` and specialises the recursion on the largest letter `List.kostkaNum_succ` of
`Mathlib.Combinatorics.Young.Tableau.Restrict`: a horizontal strip of size one is exactly a
removable corner.

## Main results

* `List.numStdTab_eq_kostkaNum` : standard tableaux of shape `sh` are the tableaux of shape
  `sh` with letters `< |sh|` and content `(1, …, 1)`.
* `List.horizStrip_decrNth` : removing a removable corner gives a horizontal strip.
* `List.exists_remCorner_of_included_succ` : conversely, a partition contained in `lam` with
  one box less is `lam` with a removable corner removed.
* `List.numStdTab_branching` : the branching rule.
-/

namespace List

open List

/-! ### Standard tableaux as tableaux with content `(1, …, 1)` -/

/-- The reading word of a tableau is a permutation of the concatenation of its rows. -/
lemma perm_toWord_flatten (t : List (List ℕ)) : (toWord t).Perm t.flatten :=
  (List.reverse_perm t).flatten

/-- The tableaux of shape `sh` with letters `< |sh|` in which every letter occurs exactly
once are the standard tableaux of shape `sh`. -/
lemma tabSet_one (sh : List ℕ) :
    tabSet sh.sum sh (fun _ => 1) = {P | IsStdTab P ∧ shape P = sh} := by
  ext P
  simp only [tabSet, Set.mem_setOf_eq, IsStdTab]
  constructor
  · rintro ⟨htab, hsh, hlt, hcount⟩
    refine ⟨⟨htab, ?_⟩, hsh⟩
    have hlen : (toWord P).length = sh.sum := by
      rw [length_toWord, sizeTab, hsh]
    rw [IsStd, hlen, List.perm_iff_count]
    intro a
    rw [(perm_toWord_flatten P).count_eq, List.count_range]
    by_cases ha : a < sh.sum
    · rw [ite_eq_left ha]; exact hcount a ha
    · rw [ite_eq_right ha]
      exact List.count_eq_zero_of_not_mem fun hmem => ha (hlt a hmem)
  · rintro ⟨⟨htab, hstd⟩, hsh⟩
    have hlen : (toWord P).length = sh.sum := by
      rw [length_toWord, sizeTab, hsh]
    rw [IsStd, hlen, List.perm_iff_count] at hstd
    have hcount : ∀ a, P.flatten.count a = if a < sh.sum then 1 else 0 := fun a => by
      rw [← (perm_toWord_flatten P).count_eq, hstd a, List.count_range]
    refine ⟨htab, hsh, fun x hx => ?_, fun i hi => by rw [hcount i, ite_eq_left hi]⟩
    by_contra hxlt
    have hx0 := hcount x
    rw [ite_eq_right hxlt] at hx0
    exact absurd hx0 (by simp [List.count_eq_zero, hx])

/-- The number of standard tableaux of shape `sh` is the Kostka number
`K_{sh, (1, …, 1)}`. -/
theorem numStdTab_eq_kostkaNum (sh : List ℕ) :
    numStdTab sh = kostkaNum sh.sum sh (fun _ => 1) := by
  rw [numStdTab, kostkaNum, tabSet_one]
  rfl

/-! ### Horizontal strips of size one -/

/-- Removing a removable corner from a partition gives a horizontal strip. -/
lemma horizStrip_decrNth {lam : List ℕ} {r : ℕ} (hlam : IsPart lam) (hc : IsRemCorner lam r) :
    HorizStrip lam (decrNth lam r) := by
  refine ⟨included_decrNth lam r, fun i => ?_⟩
  rcases eq_or_ne i r with rfl | h
  · rw [getD_decrNth_self]
    rw [IsRemCorner] at hc
    omega
  · rw [getD_decrNth_of_ne hlam hc (Ne.symm h)]
    exact hlam.getD_antitone (Nat.le_succ i)

/-- A partition contained in `lam` and having one box less is `lam` with a removable corner
removed. -/
lemma exists_remCorner_of_included_succ {lam nu : List ℕ} (hlam : IsPart lam) (hnu : IsPart nu)
    (hinc : Included nu lam) (hsum : lam.sum = nu.sum + 1) :
    ∃ r, IsRemCorner lam r ∧ nu = decrNth lam r := by
  classical
  set L := lam.length with hL
  have hle : ∀ i, nu.getD i 0 ≤ lam.getD i 0 := hinc.getD_le
  have h1 : lam.sum = ∑ i ∈ Finset.range L, lam.getD i 0 := sum_eq_sum_range lam le_rfl
  have h2 : nu.sum = ∑ i ∈ Finset.range L, nu.getD i 0 := sum_eq_sum_range nu hinc.length_le
  set d : ℕ → ℕ := fun i => lam.getD i 0 - nu.getD i 0 with hd
  have hsplit : ∑ i ∈ Finset.range L, lam.getD i 0
      = (∑ i ∈ Finset.range L, nu.getD i 0) + ∑ i ∈ Finset.range L, d i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by have := hle i; simp only [hd]; omega
  have hdsum : ∑ i ∈ Finset.range L, d i = 1 := by
    rw [h1, h2] at hsum
    omega
  obtain ⟨r, hrmem, hr0⟩ : ∃ r ∈ Finset.range L, d r ≠ 0 := by
    by_contra hcon
    push_neg at hcon
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
    · have : lam.getD i 0 = 0 := List.getD_eq_default _ _ hiL
      simp only [hd, this]
      omega
  have hne : ∀ i, i ≠ r → nu.getD i 0 = lam.getD i 0 := by
    intro i hi
    have := hzero i hi
    have := hle i
    simp only [hd] at *
    omega
  have hrval : nu.getD r 0 + 1 = lam.getD r 0 := by
    have := hle r
    simp only [hd] at hdr
    omega
  have hcorner : IsRemCorner lam r := by
    rw [IsRemCorner, ← hne (r + 1) (by omega)]
    calc nu.getD (r + 1) 0 ≤ nu.getD r 0 := hnu.getD_antitone (Nat.le_succ r)
      _ < lam.getD r 0 := by omega
  refine ⟨r, hcorner, hnu.ext_getD (isPart_decrNth hlam hcorner) fun i => ?_⟩
  rcases eq_or_ne i r with rfl | hi
  · rw [getD_decrNth_self]
    omega
  · rw [getD_decrNth_of_ne hlam hcorner (Ne.symm hi)]
    exact hne i hi

/-- A removable corner is a row of the partition. -/
lemma IsRemCorner.lt_length {lam : List ℕ} {r : ℕ} (hc : IsRemCorner lam r) : r < lam.length := by
  by_contra h
  rw [IsRemCorner, List.getD_eq_default _ _ (not_lt.1 h)] at hc
  omega

/-! ### The branching rule -/

open Classical in
/-- **The branching rule for standard tableaux**: the number of standard tableaux of shape
`lam` is the sum of the numbers of standard tableaux of the shapes obtained by removing a
removable corner of `lam`. -/
theorem numStdTab_branching {lam : List ℕ} (hlam : IsPart lam) {n N : ℕ} (hsum : lam.sum = n + 1)
    (hN : lam.length ≤ N) :
    numStdTab lam
      = ∑ r ∈ Finset.range N, if IsRemCorner lam r then numStdTab (decrNth lam r) else 0 := by
  classical
  have hkos : numStdTab lam
      = ∑ nu : {p : List ℕ // IsPart p ∧ p.sum = n},
          if HorizStrip lam nu.1 then numStdTab nu.1 else 0 := by
    rw [numStdTab_eq_kostkaNum, hsum,
      kostkaNum_succ (N := n) (c := fun _ => 1) (m := n) hlam (by simp [hsum])]
    refine Finset.sum_congr rfl fun nu _ => ?_
    by_cases h : HorizStrip lam nu.1
    · rw [ite_eq_left h, ite_eq_left h, numStdTab_eq_kostkaNum, nu.2.2]
    · rw [ite_eq_right h, ite_eq_right h]
  rw [hkos, ← Finset.sum_filter, ← Finset.sum_filter]
  refine (Finset.sum_bij
    (fun (r : ℕ) (hr : r ∈ (Finset.range N).filter (IsRemCorner lam)) =>
      (⟨decrNth lam r, isPart_decrNth hlam (Finset.mem_filter.1 hr).2, by
        rw [sum_decrNth hlam (Finset.mem_filter.1 hr).2, hsum]
        omega⟩ :
        {p : List ℕ // IsPart p ∧ p.sum = n}))
    (fun r hr => Finset.mem_filter.2 ⟨Finset.mem_univ _,
      horizStrip_decrNth hlam (Finset.mem_filter.1 hr).2⟩)
    ?_ ?_ (fun r _ => rfl)).symm
  · intro r hr r' hr' heq
    have hc : IsRemCorner lam r := (Finset.mem_filter.1 hr).2
    have hc' : IsRemCorner lam r' := (Finset.mem_filter.1 hr').2
    have heq' : decrNth lam r = decrNth lam r' := congrArg Subtype.val heq
    by_contra hne
    have h1 : (decrNth lam r).getD r 0 = lam.getD r 0 - 1 := getD_decrNth_self lam r
    have h2 : (decrNth lam r').getD r 0 = lam.getD r 0 :=
      getD_decrNth_of_ne hlam hc' fun h => hne h.symm
    rw [heq', h2] at h1
    rw [IsRemCorner] at hc
    omega
  · intro nu hnu
    have hstrip : HorizStrip lam nu.1 := (Finset.mem_filter.1 hnu).2
    obtain ⟨r, hc, hr⟩ := exists_remCorner_of_included_succ hlam nu.2.1 hstrip.included
      (by rw [hsum, nu.2.2])
    exact ⟨r, Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_of_lt_of_le hc.lt_length hN), hc⟩,
      Subtype.ext hr.symm⟩

end List
