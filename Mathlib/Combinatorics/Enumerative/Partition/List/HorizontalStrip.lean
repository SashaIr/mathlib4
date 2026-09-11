/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.List.Included
public import Mathlib.Combinatorics.Enumerative.Partition.List.TrimZeros
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Horizontal strips and the commutation of the Pieri rule

A skew shape `outer / inner` is a *horizontal strip* when it has at most one box in each
column, i.e. when `outer_{i+1} ≤ inner_i` for all `i`.  Horizontal strips describe the
shapes that can be obtained by adding to a tableau all the boxes filled with a given
letter.

The main result of this file is a purely combinatorial counting statement, which is the
commutation of two steps of the Pieri rule: given two partitions `ρ ⊆ μ`, the number
of partitions `ν` with `ρ ⊆ ν ⊆ μ` such that both `μ / ν` and `ν / ρ` are
horizontal strips and `|ν| = s` only depends on `s` through the symmetry
`s ↦ |μ| + |ρ| - s`.  In other words, if `|μ| - |ρ| = a + b`, there are as many
ways to go from `ρ` to `μ` by a horizontal strip of size `a` followed by one of size
`b` as the other way around.

The proof is the observation that such a `ν` is exactly a sequence of parts lying in a
product of intervals `loBd i ≤ ν_i ≤ hiBd i`, and that the reflection
`ν_i ↦ loBd i + hiBd i - ν_i` of this box is an involution which sends the size `s` to
`|μ| + |ρ| - s`, because `∑_i (loBd i + hiBd i) = |μ| + |ρ|`.

## Main definitions

* `Young.HorizStrip outer inner` : the skew shape `outer / inner` is a horizontal strip.
* `Young.midSet μ ρ s` : the partitions `ν` of `s` interpolating between `ρ` and
  `μ` by horizontal strips.

## Main results

* `Young.card_midSet_symm` : the commutation of the Pieri rule described above.
-/

@[expose] public section

namespace Young

open List

/-- `HorizStrip outer inner` states that `inner` is contained in `outer` and that the skew
shape `outer / inner` is a horizontal strip: it has at most one box in each column. -/
def HorizStrip (outer inner : List ℕ) : Prop :=
  Included inner outer ∧ ∀ i, outer.getD (i + 1) 0 ≤ inner.getD i 0

lemma HorizStrip.included {outer inner : List ℕ} (h : HorizStrip outer inner) :
    Included inner outer := h.1

lemma HorizStrip.getD_succ_le {outer inner : List ℕ} (h : HorizStrip outer inner) (i : ℕ) :
    outer.getD (i + 1) 0 ≤ inner.getD i 0 := h.2 i

lemma HorizStrip.getD_le {outer inner : List ℕ} (h : HorizStrip outer inner) (i : ℕ) :
    inner.getD i 0 ≤ outer.getD i 0 := h.1.getD_le i

lemma HorizStrip.sum_le {outer inner : List ℕ} (h : HorizStrip outer inner) :
    inner.sum ≤ outer.sum := h.1.sum_le

/-- Only the indices below the length of `outer` matter in the definition of a horizontal
strip; in particular the predicate is decidable. -/
lemma horizStrip_iff_range {outer inner : List ℕ} :
    HorizStrip outer inner ↔ Included inner outer ∧
      ∀ i ∈ Finset.range outer.length, outer.getD (i + 1) 0 ≤ inner.getD i 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i _ => h2 i⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i => ?_⟩
    by_cases hi : i < outer.length
    · exact h2 i (Finset.mem_range.2 hi)
    · rw [List.getD_eq_default _ _ (show outer.length ≤ i + 1 by omega)]
      exact Nat.zero_le _

instance decidableHorizStrip (outer inner : List ℕ) : Decidable (HorizStrip outer inner) :=
  decidable_of_iff _ horizStrip_iff_range.symm

lemma horizStrip_self {μ : List ℕ} (h : IsPart μ) : HorizStrip μ μ :=
  ⟨Included.refl μ, fun i => h.getD_succ_le i⟩

/-! ### The interval bounds -/

/-- The lower bound on the `i`-th part of a shape interpolating between `ρ` and `μ`
by horizontal strips. -/
def loBd (μ ρ : List ℕ) (i : ℕ) : ℕ := max (ρ.getD i 0) (μ.getD (i + 1) 0)

/-- The upper bound on the `i`-th part of a shape interpolating between `ρ` and `μ`
by horizontal strips. -/
def hiBd (μ ρ : List ℕ) : ℕ → ℕ
  | 0 => μ.getD 0 0
  | (i + 1) => min (μ.getD (i + 1) 0) (ρ.getD i 0)

@[simp] lemma hiBd_zero (μ ρ : List ℕ) : hiBd μ ρ 0 = μ.getD 0 0 := rfl

@[simp] lemma hiBd_succ (μ ρ : List ℕ) (i : ℕ) :
    hiBd μ ρ (i + 1) = min (μ.getD (i + 1) 0) (ρ.getD i 0) := rfl

lemma hiBd_le_μ (μ ρ : List ℕ) (i : ℕ) : hiBd μ ρ i ≤ μ.getD i 0 := by
  cases i with
  | zero => exact le_rfl
  | succ j => exact min_le_left _ _

lemma loBd_le_of_lt_length {μ ρ : List ℕ} (i : ℕ) : ρ.getD i 0 ≤ loBd μ ρ i :=
  le_max_left _ _

/-- Outside the length of `μ`, both bounds vanish. -/
lemma loBd_eq_zero {μ ρ : List ℕ} (hsub : Included ρ μ) {i : ℕ}
    (hi : μ.length ≤ i) : loBd μ ρ i = 0 := by
  have h1 : μ.getD i 0 = 0 := List.getD_eq_default _ _ hi
  have h2 : μ.getD (i + 1) 0 = 0 := List.getD_eq_default _ _ (by omega)
  have h3 : ρ.getD i 0 ≤ μ.getD i 0 := hsub.getD_le i
  simp only [loBd, h2]
  omega

lemma hiBd_eq_zero {μ ρ : List ℕ} {i : ℕ} (hi : μ.length ≤ i) :
    hiBd μ ρ i = 0 := by
  have h1 : μ.getD i 0 = 0 := List.getD_eq_default _ _ hi
  have := hiBd_le_μ μ ρ i
  omega

/-- The parts of an interpolating shape lie in the box given by `loBd` and `hiBd`. -/
lemma horizStrip_iff_bounds {μ ρ ν : List ℕ} (hν : IsPart ν) (hρ : IsPart ρ) :
    (HorizStrip μ ν ∧ HorizStrip ν ρ) ↔
      ∀ i, loBd μ ρ i ≤ ν.getD i 0 ∧ ν.getD i 0 ≤ hiBd μ ρ i := by
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ i
    refine ⟨max_le (h3.getD_le i) (h2 i), ?_⟩
    cases i with
    | zero => exact h1.getD_le 0
    | succ j => exact le_min (h1.getD_le (j + 1)) (h4 j)
  · intro h
    refine ⟨⟨hν.included_iff_getD.2 fun i => le_trans (h i).2 (hiBd_le_μ μ ρ i),
      fun i => le_trans (le_max_right _ _) (h i).1⟩,
      ⟨hρ.included_iff_getD.2 fun i => le_trans (le_max_left _ _) (h i).1, fun i => ?_⟩⟩
    exact le_trans (h (i + 1)).2 (min_le_right _ _)

/-! ### The set of interpolating shapes -/

/-- The set of partitions of `s` interpolating between `ρ` and `μ` by horizontal
strips. -/
def midSet (μ ρ : List ℕ) (s : ℕ) : Set (List ℕ) :=
  {ν | IsPart ν ∧ HorizStrip μ ν ∧ HorizStrip ν ρ ∧ ν.sum = s}

lemma mem_midSet_iff {μ ρ ν : List ℕ} {s : ℕ} (hρ : IsPart ρ) :
    ν ∈ midSet μ ρ s ↔
      IsPart ν ∧ (∀ i, loBd μ ρ i ≤ ν.getD i 0 ∧ ν.getD i 0 ≤ hiBd μ ρ i)
        ∧ ν.sum = s := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, (horizStrip_iff_bounds h1 hρ).1 ⟨h2, h3⟩, h4⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨h4, h5⟩ := (horizStrip_iff_bounds h1 hρ).2 h2
    exact ⟨h1, h4, h5, h3⟩

lemma midSet_eq_empty_of_lt {μ ρ : List ℕ} {s : ℕ} (h : s < ρ.sum) :
    midSet μ ρ s = ∅ := by
  ext ν
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, -, h3, rfl⟩
  exact absurd h3.sum_le (by omega)

lemma midSet_eq_empty_of_gt {μ ρ : List ℕ} {s : ℕ} (h : μ.sum < s) :
    midSet μ ρ s = ∅ := by
  ext ν
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, h2, -, rfl⟩
  exact absurd h2.sum_le (by omega)

/-! ### The sum of the bounds -/

lemma sum_loBd_add_hiBd {μ ρ : List ℕ} (hsub : Included ρ μ) :
    ∑ i ∈ Finset.range μ.length, (loBd μ ρ i + hiBd μ ρ i) = μ.sum + ρ.sum := by
  have hrlen : ρ.length ≤ μ.length := hsub.length_le
  obtain hk | ⟨n, hk⟩ : μ.length = 0 ∨ ∃ n, μ.length = n + 1 := by
    rcases Nat.eq_zero_or_pos μ.length with h | h
    · exact Or.inl h
    · exact Or.inr ⟨μ.length - 1, by omega⟩
  · have hμ : μ = [] := List.length_eq_zero_iff.1 hk
    have hρ : ρ = [] := List.length_eq_zero_iff.1 (by omega)
    simp [hμ, hρ]
  · rw [hk, Finset.sum_add_distrib, Finset.sum_range_succ (f := loBd μ ρ),
      Finset.sum_range_succ' (f := hiBd μ ρ)]
    have hlast : loBd μ ρ n = ρ.getD n 0 := by
      have h0 : μ.getD (n + 1) 0 = 0 := List.getD_eq_default _ _ (by omega)
      simp only [loBd, h0]
      omega
    have hzero : hiBd μ ρ 0 = μ.getD 0 0 := rfl
    have hmid : (∑ i ∈ Finset.range n, loBd μ ρ i)
        + ∑ i ∈ Finset.range n, hiBd μ ρ (i + 1)
        = (∑ i ∈ Finset.range n, ρ.getD i 0) + ∑ i ∈ Finset.range n, μ.getD (i + 1) 0 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [loBd, hiBd_succ]
      omega
    have hμsum : μ.sum = (∑ i ∈ Finset.range n, μ.getD (i + 1) 0) + μ.getD 0 0 := by
      rw [← Finset.sum_range_succ' (f := fun i => μ.getD i 0) n]
      exact sum_eq_sum_range_getD μ (by omega)
    have hρsum : ρ.sum = (∑ i ∈ Finset.range n, ρ.getD i 0) + ρ.getD n 0 := by
      rw [← Finset.sum_range_succ (f := fun i => ρ.getD i 0) n]
      exact sum_eq_sum_range_getD ρ (by omega)
    rw [hlast, hzero]
    omega

/-! ### The reflection of the box -/

/-- The reflection of an interpolating shape inside the box of the bounds. -/
def pieriFlip (μ ρ ν : List ℕ) : List ℕ :=
  shapeOfFn μ.length (fun i => loBd μ ρ i + hiBd μ ρ i - ν.getD i 0)

lemma getD_pieriFlip {μ ρ ν : List ℕ} (hsub : Included ρ μ) (i : ℕ) :
    (pieriFlip μ ρ ν).getD i 0 = loBd μ ρ i + hiBd μ ρ i - ν.getD i 0 := by
  rw [pieriFlip, getD_shapeOfFn]
  split_ifs with h
  · rfl
  · rw [loBd_eq_zero hsub (by omega), hiBd_eq_zero (by omega)]
    simp

lemma getLastD_pieriFlip_ne_zero (μ ρ ν : List ℕ) :
    (pieriFlip μ ρ ν).getLastD 1 ≠ 0 := by
  rw [pieriFlip, shapeOfFn]
  exact getLastD_trimZeros_ne_zero _

lemma pieriFlip_mem {μ ρ ν : List ℕ} {s : ℕ} (hρ : IsPart ρ)
    (hsub : Included ρ μ) (hν : ν ∈ midSet μ ρ s) :
    pieriFlip μ ρ ν ∈ midSet μ ρ (μ.sum + ρ.sum - s) := by
  obtain ⟨hpart, hstr1, hstr2, hsum⟩ := hν
  have hbox : ∀ i, loBd μ ρ i ≤ ν.getD i 0 ∧ ν.getD i 0 ≤ hiBd μ ρ i :=
    (horizStrip_iff_bounds hpart hρ).1 ⟨hstr1, hstr2⟩
  set g : ℕ → ℕ := fun i => loBd μ ρ i + hiBd μ ρ i - ν.getD i 0 with hg
  have hgetD : ∀ i, (pieriFlip μ ρ ν).getD i 0 = g i := getD_pieriFlip hsub
  have hgbox : ∀ i, loBd μ ρ i ≤ g i ∧ g i ≤ hiBd μ ρ i := by
    intro i
    have := hbox i
    simp only [hg]
    omega
  have hgdec : ∀ i, g (i + 1) ≤ g i := by
    intro i
    have h1 : g (i + 1) ≤ hiBd μ ρ (i + 1) := (hgbox (i + 1)).2
    have h2 : loBd μ ρ i ≤ g i := (hgbox i).1
    have h3 : hiBd μ ρ (i + 1) ≤ ρ.getD i 0 := min_le_right _ _
    have h4 : ρ.getD i 0 ≤ loBd μ ρ i := le_max_left _ _
    omega
  have hpartflip : IsPart (pieriFlip μ ρ ν) := isPart_shapeOfFn hgdec
  refine (mem_midSet_iff hρ).2 ⟨hpartflip, fun i => by rw [hgetD i]; exact hgbox i, ?_⟩
  -- the sum
  have hνlen : ν.length ≤ μ.length := hstr1.included.length_le
  have hfliplen : (pieriFlip μ ρ ν).length ≤ μ.length := length_shapeOfFn_le _ _
  have hsum1 : (pieriFlip μ ρ ν).sum = ∑ i ∈ Finset.range μ.length, g i := by
    rw [sum_eq_sum_range_getD _ hfliplen]
    exact Finset.sum_congr rfl fun i _ => hgetD i
  have hsum2 : ν.sum = ∑ i ∈ Finset.range μ.length, ν.getD i 0 :=
    sum_eq_sum_range_getD ν hνlen
  have hsum3 : (∑ i ∈ Finset.range μ.length, g i)
      + ∑ i ∈ Finset.range μ.length, ν.getD i 0 = μ.sum + ρ.sum := by
    rw [← Finset.sum_add_distrib, ← sum_loBd_add_hiBd hsub]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hbox i).2
    simp only [hg]
    omega
  rw [hsum1]
  omega

lemma pieriFlip_pieriFlip {μ ρ ν : List ℕ} {s : ℕ} (hρ : IsPart ρ)
    (hsub : Included ρ μ) (hν : ν ∈ midSet μ ρ s) :
    pieriFlip μ ρ (pieriFlip μ ρ ν) = ν := by
  obtain ⟨hpart, hbox, -⟩ := (mem_midSet_iff hρ).1 hν
  refine ext_getD_of_getLastD_ne_zero (getLastD_pieriFlip_ne_zero _ _ _)
    hpart.getLastD_ne_zero fun i => ?_
  rw [getD_pieriFlip hsub i, getD_pieriFlip hsub i]
  have := hbox i
  omega

/-- **Commutation of the Pieri rule**: going from `κ` to `μ` through a shape of size
`s` by two horizontal strips can be done in as many ways as going through a shape of size
`|μ| + |κ| - s`; equivalently, if `|μ| - |κ| = a + b`, there are as many ways to
add a horizontal strip of size `a` and then one of size `b` as the other way around. -/
theorem card_midSet_symm (μ κ : List ℕ) (hκ : IsPart κ)
    (hsub : Included κ μ) {s : ℕ} (hs : κ.sum ≤ s) (hs' : s ≤ μ.sum) :
    Nat.card (midSet μ κ s) = Nat.card (midSet μ κ (μ.sum + κ.sum - s)) := by
  have hle : κ.sum ≤ μ.sum := hsub.sum_le
  set t := μ.sum + κ.sum - s with ht
  have hts : μ.sum + κ.sum - t = s := by omega
  refine Nat.card_congr (Equiv.ofBijective
    (fun ρ : midSet μ κ s => (⟨pieriFlip μ κ ρ.1,
      pieriFlip_mem hκ hsub ρ.2⟩ : midSet μ κ t)) ⟨?_, ?_⟩)
  · rintro ⟨ρ, hρ⟩ ⟨ν, hν⟩ h
    have h' : pieriFlip μ κ ρ = pieriFlip μ κ ν := congrArg Subtype.val h
    have := pieriFlip_pieriFlip hκ hsub hρ
    rw [h', pieriFlip_pieriFlip hκ hsub hν] at this
    exact Subtype.ext this.symm
  · rintro ⟨ν, hν⟩
    have hν' : pieriFlip μ κ ν ∈ midSet μ κ s := by
      have := pieriFlip_mem (s := t) hκ hsub hν
      rwa [hts] at this
    exact ⟨⟨pieriFlip μ κ ν, hν'⟩, Subtype.ext (pieriFlip_pieriFlip hκ hsub hν)⟩

/-- The form of `Young.card_midSet_symm` used in the Pieri rule: adding a horizontal strip
of size `a` and then one of size `b` can be done in as many ways as the other way
around. -/
theorem card_midSet_add_comm (μ ρ : List ℕ) (hρ : IsPart ρ) (hsub : Included ρ μ)
    {a b : ℕ} (hab : ρ.sum + a + b = μ.sum) :
    Nat.card (midSet μ ρ (ρ.sum + a)) = Nat.card (midSet μ ρ (ρ.sum + b)) := by
  have := card_midSet_symm μ ρ hρ hsub (s := ρ.sum + a) (by omega) (by omega)
  rwa [show μ.sum + ρ.sum - (ρ.sum + a) = ρ.sum + b by omega] at this

end Young
