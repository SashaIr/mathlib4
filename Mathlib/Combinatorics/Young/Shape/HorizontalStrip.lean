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
commutation of two steps of the Pieri rule: given two partitions `rho ⊆ lam`, the number
of partitions `nu` with `rho ⊆ nu ⊆ lam` such that both `lam / nu` and `nu / rho` are
horizontal strips and `|nu| = s` only depends on `s` through the symmetry
`s ↦ |lam| + |rho| - s`.  In other words, if `|lam| - |rho| = a + b`, there are as many
ways to go from `rho` to `lam` by a horizontal strip of size `a` followed by one of size
`b` as the other way around.

The proof is the observation that such a `nu` is exactly a sequence of parts lying in a
product of intervals `loBd i ≤ nu_i ≤ hiBd i`, and that the reflection
`nu_i ↦ loBd i + hiBd i - nu_i` of this box is an involution which sends the size `s` to
`|lam| + |rho| - s`, because `∑_i (loBd i + hiBd i) = |lam| + |rho|`.

## Main definitions

* `Young.HorizStrip outer inner` : the skew shape `outer / inner` is a horizontal strip.
* `Young.midSet lam rho s` : the partitions `nu` of `s` interpolating between `rho` and
  `lam` by horizontal strips.

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

lemma horizStrip_self {sh : List ℕ} (h : IsPart sh) : HorizStrip sh sh :=
  ⟨Included.refl sh, fun i => h.getD_succ_le i⟩

/-! ### The interval bounds -/

/-- The lower bound on the `i`-th part of a shape interpolating between `rho` and `lam`
by horizontal strips. -/
def loBd (lam rho : List ℕ) (i : ℕ) : ℕ := max (rho.getD i 0) (lam.getD (i + 1) 0)

/-- The upper bound on the `i`-th part of a shape interpolating between `rho` and `lam`
by horizontal strips. -/
def hiBd (lam rho : List ℕ) : ℕ → ℕ
  | 0 => lam.getD 0 0
  | (i + 1) => min (lam.getD (i + 1) 0) (rho.getD i 0)

@[simp] lemma hiBd_zero (lam rho : List ℕ) : hiBd lam rho 0 = lam.getD 0 0 := rfl

@[simp] lemma hiBd_succ (lam rho : List ℕ) (i : ℕ) :
    hiBd lam rho (i + 1) = min (lam.getD (i + 1) 0) (rho.getD i 0) := rfl

lemma hiBd_le_lam (lam rho : List ℕ) (i : ℕ) : hiBd lam rho i ≤ lam.getD i 0 := by
  cases i with
  | zero => exact le_rfl
  | succ j => exact min_le_left _ _

lemma loBd_le_of_lt_length {lam rho : List ℕ} (i : ℕ) : rho.getD i 0 ≤ loBd lam rho i :=
  le_max_left _ _

/-- Outside the length of `lam`, both bounds vanish. -/
lemma loBd_eq_zero {lam rho : List ℕ} (hsub : Included rho lam) {i : ℕ}
    (hi : lam.length ≤ i) : loBd lam rho i = 0 := by
  have h1 : lam.getD i 0 = 0 := List.getD_eq_default _ _ hi
  have h2 : lam.getD (i + 1) 0 = 0 := List.getD_eq_default _ _ (by omega)
  have h3 : rho.getD i 0 ≤ lam.getD i 0 := hsub.getD_le i
  simp only [loBd, h2]
  omega

lemma hiBd_eq_zero {lam rho : List ℕ} {i : ℕ} (hi : lam.length ≤ i) :
    hiBd lam rho i = 0 := by
  have h1 : lam.getD i 0 = 0 := List.getD_eq_default _ _ hi
  have := hiBd_le_lam lam rho i
  omega

/-- The parts of an interpolating shape lie in the box given by `loBd` and `hiBd`. -/
lemma horizStrip_iff_bounds {lam rho nu : List ℕ} (hnu : IsPart nu) (hrho : IsPart rho) :
    (HorizStrip lam nu ∧ HorizStrip nu rho) ↔
      ∀ i, loBd lam rho i ≤ nu.getD i 0 ∧ nu.getD i 0 ≤ hiBd lam rho i := by
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ i
    refine ⟨max_le (h3.getD_le i) (h2 i), ?_⟩
    cases i with
    | zero => exact h1.getD_le 0
    | succ j => exact le_min (h1.getD_le (j + 1)) (h4 j)
  · intro h
    refine ⟨⟨hnu.included_iff_getD.2 fun i => le_trans (h i).2 (hiBd_le_lam lam rho i),
      fun i => le_trans (le_max_right _ _) (h i).1⟩,
      ⟨hrho.included_iff_getD.2 fun i => le_trans (le_max_left _ _) (h i).1, fun i => ?_⟩⟩
    exact le_trans (h (i + 1)).2 (min_le_right _ _)

/-! ### The set of interpolating shapes -/

/-- The set of partitions of `s` interpolating between `rho` and `lam` by horizontal
strips. -/
def midSet (lam rho : List ℕ) (s : ℕ) : Set (List ℕ) :=
  {nu | IsPart nu ∧ HorizStrip lam nu ∧ HorizStrip nu rho ∧ nu.sum = s}

lemma mem_midSet_iff {lam rho nu : List ℕ} {s : ℕ} (hrho : IsPart rho) :
    nu ∈ midSet lam rho s ↔
      IsPart nu ∧ (∀ i, loBd lam rho i ≤ nu.getD i 0 ∧ nu.getD i 0 ≤ hiBd lam rho i)
        ∧ nu.sum = s := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, (horizStrip_iff_bounds h1 hrho).1 ⟨h2, h3⟩, h4⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨h4, h5⟩ := (horizStrip_iff_bounds h1 hrho).2 h2
    exact ⟨h1, h4, h5, h3⟩

lemma midSet_eq_empty_of_lt {lam rho : List ℕ} {s : ℕ} (h : s < rho.sum) :
    midSet lam rho s = ∅ := by
  ext nu
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, -, h3, rfl⟩
  exact absurd h3.sum_le (by omega)

lemma midSet_eq_empty_of_gt {lam rho : List ℕ} {s : ℕ} (h : lam.sum < s) :
    midSet lam rho s = ∅ := by
  ext nu
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, h2, -, rfl⟩
  exact absurd h2.sum_le (by omega)

/-! ### The sum of the bounds -/

lemma sum_loBd_add_hiBd {lam rho : List ℕ} (hsub : Included rho lam) :
    ∑ i ∈ Finset.range lam.length, (loBd lam rho i + hiBd lam rho i) = lam.sum + rho.sum := by
  have hrlen : rho.length ≤ lam.length := hsub.length_le
  obtain hk | ⟨n, hk⟩ : lam.length = 0 ∨ ∃ n, lam.length = n + 1 := by
    rcases Nat.eq_zero_or_pos lam.length with h | h
    · exact Or.inl h
    · exact Or.inr ⟨lam.length - 1, by omega⟩
  · have hlam : lam = [] := List.length_eq_zero_iff.1 hk
    have hrho : rho = [] := List.length_eq_zero_iff.1 (by omega)
    simp [hlam, hrho]
  · rw [hk, Finset.sum_add_distrib, Finset.sum_range_succ (f := loBd lam rho),
      Finset.sum_range_succ' (f := hiBd lam rho)]
    have hlast : loBd lam rho n = rho.getD n 0 := by
      have h0 : lam.getD (n + 1) 0 = 0 := List.getD_eq_default _ _ (by omega)
      simp only [loBd, h0]
      omega
    have hzero : hiBd lam rho 0 = lam.getD 0 0 := rfl
    have hmid : (∑ i ∈ Finset.range n, loBd lam rho i)
        + ∑ i ∈ Finset.range n, hiBd lam rho (i + 1)
        = (∑ i ∈ Finset.range n, rho.getD i 0) + ∑ i ∈ Finset.range n, lam.getD (i + 1) 0 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [loBd, hiBd_succ]
      omega
    have hlamsum : lam.sum = (∑ i ∈ Finset.range n, lam.getD (i + 1) 0) + lam.getD 0 0 := by
      rw [← Finset.sum_range_succ' (f := fun i => lam.getD i 0) n]
      exact sum_eq_sum_range_getD lam (by omega)
    have hrhosum : rho.sum = (∑ i ∈ Finset.range n, rho.getD i 0) + rho.getD n 0 := by
      rw [← Finset.sum_range_succ (f := fun i => rho.getD i 0) n]
      exact sum_eq_sum_range_getD rho (by omega)
    rw [hlast, hzero]
    omega

/-! ### The reflection of the box -/

/-- The reflection of an interpolating shape inside the box of the bounds. -/
def pieriFlip (lam rho nu : List ℕ) : List ℕ :=
  shapeOfFn lam.length (fun i => loBd lam rho i + hiBd lam rho i - nu.getD i 0)

lemma getD_pieriFlip {lam rho nu : List ℕ} (hsub : Included rho lam) (i : ℕ) :
    (pieriFlip lam rho nu).getD i 0 = loBd lam rho i + hiBd lam rho i - nu.getD i 0 := by
  rw [pieriFlip, getD_shapeOfFn]
  split_ifs with h
  · rfl
  · rw [loBd_eq_zero hsub (by omega), hiBd_eq_zero (by omega)]
    simp

lemma getLastD_pieriFlip_ne_zero (lam rho nu : List ℕ) :
    (pieriFlip lam rho nu).getLastD 1 ≠ 0 := by
  rw [pieriFlip, shapeOfFn]
  exact getLastD_trimZeros_ne_zero _

lemma pieriFlip_mem {lam rho nu : List ℕ} {s : ℕ} (hrho : IsPart rho)
    (hsub : Included rho lam) (hnu : nu ∈ midSet lam rho s) :
    pieriFlip lam rho nu ∈ midSet lam rho (lam.sum + rho.sum - s) := by
  obtain ⟨hpart, hstr1, hstr2, hsum⟩ := hnu
  have hbox : ∀ i, loBd lam rho i ≤ nu.getD i 0 ∧ nu.getD i 0 ≤ hiBd lam rho i :=
    (horizStrip_iff_bounds hpart hrho).1 ⟨hstr1, hstr2⟩
  set g : ℕ → ℕ := fun i => loBd lam rho i + hiBd lam rho i - nu.getD i 0 with hg
  have hgetD : ∀ i, (pieriFlip lam rho nu).getD i 0 = g i := getD_pieriFlip hsub
  have hgbox : ∀ i, loBd lam rho i ≤ g i ∧ g i ≤ hiBd lam rho i := by
    intro i
    have := hbox i
    simp only [hg]
    omega
  have hgdec : ∀ i, g (i + 1) ≤ g i := by
    intro i
    have h1 : g (i + 1) ≤ hiBd lam rho (i + 1) := (hgbox (i + 1)).2
    have h2 : loBd lam rho i ≤ g i := (hgbox i).1
    have h3 : hiBd lam rho (i + 1) ≤ rho.getD i 0 := min_le_right _ _
    have h4 : rho.getD i 0 ≤ loBd lam rho i := le_max_left _ _
    omega
  have hpartflip : IsPart (pieriFlip lam rho nu) := isPart_shapeOfFn hgdec
  refine (mem_midSet_iff hrho).2 ⟨hpartflip, fun i => by rw [hgetD i]; exact hgbox i, ?_⟩
  -- the sum
  have hnulen : nu.length ≤ lam.length := hstr1.included.length_le
  have hfliplen : (pieriFlip lam rho nu).length ≤ lam.length := length_shapeOfFn_le _ _
  have hsum1 : (pieriFlip lam rho nu).sum = ∑ i ∈ Finset.range lam.length, g i := by
    rw [sum_eq_sum_range_getD _ hfliplen]
    exact Finset.sum_congr rfl fun i _ => hgetD i
  have hsum2 : nu.sum = ∑ i ∈ Finset.range lam.length, nu.getD i 0 :=
    sum_eq_sum_range_getD nu hnulen
  have hsum3 : (∑ i ∈ Finset.range lam.length, g i)
      + ∑ i ∈ Finset.range lam.length, nu.getD i 0 = lam.sum + rho.sum := by
    rw [← Finset.sum_add_distrib, ← sum_loBd_add_hiBd hsub]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hbox i).2
    simp only [hg]
    omega
  rw [hsum1]
  omega

lemma pieriFlip_pieriFlip {lam rho nu : List ℕ} {s : ℕ} (hrho : IsPart rho)
    (hsub : Included rho lam) (hnu : nu ∈ midSet lam rho s) :
    pieriFlip lam rho (pieriFlip lam rho nu) = nu := by
  obtain ⟨hpart, hbox, -⟩ := (mem_midSet_iff hrho).1 hnu
  refine ext_getD_of_getLastD_ne_zero (getLastD_pieriFlip_ne_zero _ _ _)
    hpart.getLastD_ne_zero fun i => ?_
  rw [getD_pieriFlip hsub i, getD_pieriFlip hsub i]
  have := hbox i
  omega

/-- **Commutation of the Pieri rule**: going from `rho` to `lam` through a shape of size
`s` by two horizontal strips can be done in as many ways as going through a shape of size
`|lam| + |rho| - s`; equivalently, if `|lam| - |rho| = a + b`, there are as many ways to
add a horizontal strip of size `a` and then one of size `b` as the other way around. -/
theorem card_midSet_symm (lam rho : List ℕ) (hrho : IsPart rho)
    (hsub : Included rho lam) {s : ℕ} (hs : rho.sum ≤ s) (hs' : s ≤ lam.sum) :
    Nat.card (midSet lam rho s) = Nat.card (midSet lam rho (lam.sum + rho.sum - s)) := by
  have hle : rho.sum ≤ lam.sum := hsub.sum_le
  set t := lam.sum + rho.sum - s with ht
  have hts : lam.sum + rho.sum - t = s := by omega
  refine Nat.card_congr (Equiv.ofBijective
    (fun nu : midSet lam rho s => (⟨pieriFlip lam rho nu.1,
      pieriFlip_mem hrho hsub nu.2⟩ : midSet lam rho t)) ⟨?_, ?_⟩)
  · rintro ⟨nu, hnu⟩ ⟨mu, hmu⟩ h
    have h' : pieriFlip lam rho nu = pieriFlip lam rho mu := congrArg Subtype.val h
    have := pieriFlip_pieriFlip hrho hsub hnu
    rw [h', pieriFlip_pieriFlip hrho hsub hmu] at this
    exact Subtype.ext this.symm
  · rintro ⟨mu, hmu⟩
    have hmu' : pieriFlip lam rho mu ∈ midSet lam rho s := by
      have := pieriFlip_mem (s := t) hrho hsub hmu
      rwa [hts] at this
    exact ⟨⟨pieriFlip lam rho mu, hmu'⟩, Subtype.ext (pieriFlip_pieriFlip hrho hsub hmu)⟩

/-- The form of `Young.card_midSet_symm` used in the Pieri rule: adding a horizontal strip
of size `a` and then one of size `b` can be done in as many ways as the other way
around. -/
theorem card_midSet_add_comm (lam rho : List ℕ) (hrho : IsPart rho) (hsub : Included rho lam)
    {a b : ℕ} (hab : rho.sum + a + b = lam.sum) :
    Nat.card (midSet lam rho (rho.sum + a)) = Nat.card (midSet lam rho (rho.sum + b)) := by
  have := card_midSet_symm lam rho hrho hsub (s := rho.sum + a) (by omega) (by omega)
  rwa [show lam.sum + rho.sum - (rho.sum + a) = rho.sum + b by omega] at this

end Young
