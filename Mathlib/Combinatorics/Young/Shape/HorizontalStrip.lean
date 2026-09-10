/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Shape.Included
public import Mathlib.Combinatorics.Young.Shape.TrimZeros
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Horizontal strips and the commutation of the Pieri rule

A skew shape `outer / inner` is a *horizontal strip* when it has at most one box in each
column, i.e. when `outer_{i+1} ≤ inner_i` for all `i`.  Horizontal strips describe the
shapes that can be obtained by adding to a tableau all the boxes filled with a given
letter.

The main result of this file is a purely combinatorial counting statement, which is the
commutation of two steps of the Pieri rule: given two partitions `ρ ⊆ η`, the number
of partitions `ν` with `ρ ⊆ ν ⊆ η` such that both `η / ν` and `ν / ρ` are
horizontal strips and `|ν| = s` only depends on `s` through the symmetry
`s ↦ |η| + |ρ| - s`.  In other words, if `|η| - |ρ| = a + b`, there are as many
ways to go from `ρ` to `η` by a horizontal strip of size `a` followed by one of size
`b` as the other way around.

The proof is the observation that such a `ν` is exactly a sequence of parts lying in a
product of intervals `loBd i ≤ ν_i ≤ hiBd i`, and that the reflection
`ν_i ↦ loBd i + hiBd i - ν_i` of this box is an involution which sends the size `s` to
`|η| + |ρ| - s`, because `∑_i (loBd i + hiBd i) = |η| + |ρ|`.

## Main definitions

* `Young.HorizStrip outer inner` : the skew shape `outer / inner` is a horizontal strip.
* `Young.midSet η ρ s` : the partitions `ν` of `s` interpolating between `ρ` and
  `η` by horizontal strips.

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

/-- The lower bound on the `i`-th part of a shape interpolating between `ρ` and `η`
by horizontal strips. -/
def loBd (η ρ : List ℕ) (i : ℕ) : ℕ := max (ρ.getD i 0) (η.getD (i + 1) 0)

/-- The upper bound on the `i`-th part of a shape interpolating between `ρ` and `η`
by horizontal strips. -/
def hiBd (η ρ : List ℕ) : ℕ → ℕ
  | 0 => η.getD 0 0
  | (i + 1) => min (η.getD (i + 1) 0) (ρ.getD i 0)

@[simp] lemma hiBd_zero (η ρ : List ℕ) : hiBd η ρ 0 = η.getD 0 0 := rfl

@[simp] lemma hiBd_succ (η ρ : List ℕ) (i : ℕ) :
    hiBd η ρ (i + 1) = min (η.getD (i + 1) 0) (ρ.getD i 0) := rfl

lemma hiBd_le_η (η ρ : List ℕ) (i : ℕ) : hiBd η ρ i ≤ η.getD i 0 := by
  cases i with
  | zero => exact le_rfl
  | succ j => exact min_le_left _ _

lemma loBd_le_of_lt_length {η ρ : List ℕ} (i : ℕ) : ρ.getD i 0 ≤ loBd η ρ i :=
  le_max_left _ _

/-- Outside the length of `η`, both bounds vanish. -/
lemma loBd_eq_zero {η ρ : List ℕ} (hsub : Included ρ η) {i : ℕ}
    (hi : η.length ≤ i) : loBd η ρ i = 0 := by
  have h1 : η.getD i 0 = 0 := List.getD_eq_default _ _ hi
  have h2 : η.getD (i + 1) 0 = 0 := List.getD_eq_default _ _ (by omega)
  have h3 : ρ.getD i 0 ≤ η.getD i 0 := hsub.getD_le i
  simp only [loBd, h2]
  omega

lemma hiBd_eq_zero {η ρ : List ℕ} {i : ℕ} (hi : η.length ≤ i) :
    hiBd η ρ i = 0 := by
  have h1 : η.getD i 0 = 0 := List.getD_eq_default _ _ hi
  have := hiBd_le_η η ρ i
  omega

/-- The parts of an interpolating shape lie in the box given by `loBd` and `hiBd`. -/
lemma horizStrip_iff_bounds {η ρ ν : List ℕ} (hν : IsPart ν) (hρ : IsPart ρ) :
    (HorizStrip η ν ∧ HorizStrip ν ρ) ↔
      ∀ i, loBd η ρ i ≤ ν.getD i 0 ∧ ν.getD i 0 ≤ hiBd η ρ i := by
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ i
    refine ⟨max_le (h3.getD_le i) (h2 i), ?_⟩
    cases i with
    | zero => exact h1.getD_le 0
    | succ j => exact le_min (h1.getD_le (j + 1)) (h4 j)
  · intro h
    refine ⟨⟨hν.included_iff_getD.2 fun i => le_trans (h i).2 (hiBd_le_η η ρ i),
      fun i => le_trans (le_max_right _ _) (h i).1⟩,
      ⟨hρ.included_iff_getD.2 fun i => le_trans (le_max_left _ _) (h i).1, fun i => ?_⟩⟩
    exact le_trans (h (i + 1)).2 (min_le_right _ _)

/-! ### The set of interpolating shapes -/

/-- The set of partitions of `s` interpolating between `ρ` and `η` by horizontal
strips. -/
def midSet (η ρ : List ℕ) (s : ℕ) : Set (List ℕ) :=
  {ν | IsPart ν ∧ HorizStrip η ν ∧ HorizStrip ν ρ ∧ ν.sum = s}

lemma mem_midSet_iff {η ρ ν : List ℕ} {s : ℕ} (hρ : IsPart ρ) :
    ν ∈ midSet η ρ s ↔
      IsPart ν ∧ (∀ i, loBd η ρ i ≤ ν.getD i 0 ∧ ν.getD i 0 ≤ hiBd η ρ i)
        ∧ ν.sum = s := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, (horizStrip_iff_bounds h1 hρ).1 ⟨h2, h3⟩, h4⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨h4, h5⟩ := (horizStrip_iff_bounds h1 hρ).2 h2
    exact ⟨h1, h4, h5, h3⟩

lemma midSet_eq_empty_of_lt {η ρ : List ℕ} {s : ℕ} (h : s < ρ.sum) :
    midSet η ρ s = ∅ := by
  ext ν
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, -, h3, rfl⟩
  exact absurd h3.sum_le (by omega)

lemma midSet_eq_empty_of_gt {η ρ : List ℕ} {s : ℕ} (h : η.sum < s) :
    midSet η ρ s = ∅ := by
  ext ν
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, h2, -, rfl⟩
  exact absurd h2.sum_le (by omega)

/-! ### The sum of the bounds -/

lemma sum_loBd_add_hiBd {η ρ : List ℕ} (hsub : Included ρ η) :
    ∑ i ∈ Finset.range η.length, (loBd η ρ i + hiBd η ρ i) = η.sum + ρ.sum := by
  have hrlen : ρ.length ≤ η.length := hsub.length_le
  obtain hk | ⟨n, hk⟩ : η.length = 0 ∨ ∃ n, η.length = n + 1 := by
    rcases Nat.eq_zero_or_pos η.length with h | h
    · exact Or.inl h
    · exact Or.inr ⟨η.length - 1, by omega⟩
  · have hη : η = [] := List.length_eq_zero_iff.1 hk
    have hρ : ρ = [] := List.length_eq_zero_iff.1 (by omega)
    simp [hη, hρ]
  · rw [hk, Finset.sum_add_distrib, Finset.sum_range_succ (f := loBd η ρ),
      Finset.sum_range_succ' (f := hiBd η ρ)]
    have hlast : loBd η ρ n = ρ.getD n 0 := by
      have h0 : η.getD (n + 1) 0 = 0 := List.getD_eq_default _ _ (by omega)
      simp only [loBd, h0]
      omega
    have hzero : hiBd η ρ 0 = η.getD 0 0 := rfl
    have hmid : (∑ i ∈ Finset.range n, loBd η ρ i)
        + ∑ i ∈ Finset.range n, hiBd η ρ (i + 1)
        = (∑ i ∈ Finset.range n, ρ.getD i 0) + ∑ i ∈ Finset.range n, η.getD (i + 1) 0 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [loBd, hiBd_succ]
      omega
    have hηsum : η.sum = (∑ i ∈ Finset.range n, η.getD (i + 1) 0) + η.getD 0 0 := by
      rw [← Finset.sum_range_succ' (f := fun i => η.getD i 0) n]
      exact sum_eq_sum_range_getD η (by omega)
    have hρsum : ρ.sum = (∑ i ∈ Finset.range n, ρ.getD i 0) + ρ.getD n 0 := by
      rw [← Finset.sum_range_succ (f := fun i => ρ.getD i 0) n]
      exact sum_eq_sum_range_getD ρ (by omega)
    rw [hlast, hzero]
    omega

/-! ### The reflection of the box -/

/-- The reflection of an interpolating shape inside the box of the bounds. -/
def pieriFlip (η ρ ν : List ℕ) : List ℕ :=
  shapeOfFn η.length (fun i => loBd η ρ i + hiBd η ρ i - ν.getD i 0)

lemma getD_pieriFlip {η ρ ν : List ℕ} (hsub : Included ρ η) (i : ℕ) :
    (pieriFlip η ρ ν).getD i 0 = loBd η ρ i + hiBd η ρ i - ν.getD i 0 := by
  rw [pieriFlip, getD_shapeOfFn]
  split_ifs with h
  · rfl
  · rw [loBd_eq_zero hsub (by omega), hiBd_eq_zero (by omega)]
    simp

lemma getLastD_pieriFlip_ne_zero (η ρ ν : List ℕ) :
    (pieriFlip η ρ ν).getLastD 1 ≠ 0 := by
  rw [pieriFlip, shapeOfFn]
  exact getLastD_trimZeros_ne_zero _

lemma pieriFlip_mem {η ρ ν : List ℕ} {s : ℕ} (hρ : IsPart ρ)
    (hsub : Included ρ η) (hν : ν ∈ midSet η ρ s) :
    pieriFlip η ρ ν ∈ midSet η ρ (η.sum + ρ.sum - s) := by
  obtain ⟨hpart, hstr1, hstr2, hsum⟩ := hν
  have hbox : ∀ i, loBd η ρ i ≤ ν.getD i 0 ∧ ν.getD i 0 ≤ hiBd η ρ i :=
    (horizStrip_iff_bounds hpart hρ).1 ⟨hstr1, hstr2⟩
  set g : ℕ → ℕ := fun i => loBd η ρ i + hiBd η ρ i - ν.getD i 0 with hg
  have hgetD : ∀ i, (pieriFlip η ρ ν).getD i 0 = g i := getD_pieriFlip hsub
  have hgbox : ∀ i, loBd η ρ i ≤ g i ∧ g i ≤ hiBd η ρ i := by
    intro i
    have := hbox i
    simp only [hg]
    omega
  have hgdec : ∀ i, g (i + 1) ≤ g i := by
    intro i
    have h1 : g (i + 1) ≤ hiBd η ρ (i + 1) := (hgbox (i + 1)).2
    have h2 : loBd η ρ i ≤ g i := (hgbox i).1
    have h3 : hiBd η ρ (i + 1) ≤ ρ.getD i 0 := min_le_right _ _
    have h4 : ρ.getD i 0 ≤ loBd η ρ i := le_max_left _ _
    omega
  have hpartflip : IsPart (pieriFlip η ρ ν) := isPart_shapeOfFn hgdec
  refine (mem_midSet_iff hρ).2 ⟨hpartflip, fun i => by rw [hgetD i]; exact hgbox i, ?_⟩
  -- the sum
  have hνlen : ν.length ≤ η.length := hstr1.included.length_le
  have hfliplen : (pieriFlip η ρ ν).length ≤ η.length := length_shapeOfFn_le _ _
  have hsum1 : (pieriFlip η ρ ν).sum = ∑ i ∈ Finset.range η.length, g i := by
    rw [sum_eq_sum_range_getD _ hfliplen]
    exact Finset.sum_congr rfl fun i _ => hgetD i
  have hsum2 : ν.sum = ∑ i ∈ Finset.range η.length, ν.getD i 0 :=
    sum_eq_sum_range_getD ν hνlen
  have hsum3 : (∑ i ∈ Finset.range η.length, g i)
      + ∑ i ∈ Finset.range η.length, ν.getD i 0 = η.sum + ρ.sum := by
    rw [← Finset.sum_add_distrib, ← sum_loBd_add_hiBd hsub]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hbox i).2
    simp only [hg]
    omega
  rw [hsum1]
  omega

lemma pieriFlip_pieriFlip {η ρ ν : List ℕ} {s : ℕ} (hρ : IsPart ρ)
    (hsub : Included ρ η) (hν : ν ∈ midSet η ρ s) :
    pieriFlip η ρ (pieriFlip η ρ ν) = ν := by
  obtain ⟨hpart, hbox, -⟩ := (mem_midSet_iff hρ).1 hν
  refine ext_getD_of_getLastD_ne_zero (getLastD_pieriFlip_ne_zero _ _ _)
    hpart.getLastD_ne_zero fun i => ?_
  rw [getD_pieriFlip hsub i, getD_pieriFlip hsub i]
  have := hbox i
  omega

/-- **Commutation of the Pieri rule**: going from `ρ` to `η` through a shape of size
`s` by two horizontal strips can be done in as many ways as going through a shape of size
`|η| + |ρ| - s`; equivalently, if `|η| - |ρ| = a + b`, there are as many ways to
add a horizontal strip of size `a` and then one of size `b` as the other way around. -/
theorem card_midSet_symm (η ρ : List ℕ) (hρ : IsPart ρ)
    (hsub : Included ρ η) {s : ℕ} (hs : ρ.sum ≤ s) (hs' : s ≤ η.sum) :
    Nat.card (midSet η ρ s) = Nat.card (midSet η ρ (η.sum + ρ.sum - s)) := by
  have hle : ρ.sum ≤ η.sum := hsub.sum_le
  set t := η.sum + ρ.sum - s with ht
  have hts : η.sum + ρ.sum - t = s := by omega
  refine Nat.card_congr (Equiv.ofBijective
    (fun ν : midSet η ρ s => (⟨pieriFlip η ρ ν.1,
      pieriFlip_mem hρ hsub ν.2⟩ : midSet η ρ t)) ⟨?_, ?_⟩)
  · rintro ⟨ν, hν⟩ ⟨μ, hμ⟩ h
    have h' : pieriFlip η ρ ν = pieriFlip η ρ μ := congrArg Subtype.val h
    have := pieriFlip_pieriFlip hρ hsub hν
    rw [h', pieriFlip_pieriFlip hρ hsub hμ] at this
    exact Subtype.ext this.symm
  · rintro ⟨μ, hμ⟩
    have hμ' : pieriFlip η ρ μ ∈ midSet η ρ s := by
      have := pieriFlip_mem (s := t) hρ hsub hμ
      rwa [hts] at this
    exact ⟨⟨pieriFlip η ρ μ, hμ'⟩, Subtype.ext (pieriFlip_pieriFlip hρ hsub hμ)⟩

/-- The form of `Young.card_midSet_symm` used in the Pieri rule: adding a horizontal strip
of size `a` and then one of size `b` can be done in as many ways as the other way
around. -/
theorem card_midSet_add_comm (η ρ : List ℕ) (hρ : IsPart ρ) (hsub : Included ρ η)
    {a b : ℕ} (hab : ρ.sum + a + b = η.sum) :
    Nat.card (midSet η ρ (ρ.sum + a)) = Nat.card (midSet η ρ (ρ.sum + b)) := by
  have := card_midSet_symm η ρ hρ hsub (s := ρ.sum + a) (by omega) (by omega)
  rwa [show η.sum + ρ.sum - (ρ.sum + a) = ρ.sum + b by omega] at this

end Young
