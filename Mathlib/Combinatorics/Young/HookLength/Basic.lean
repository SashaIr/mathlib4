/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Combinatorics.Enumerative.Partition.List.Conjugate
public import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Hook lengths

The *hook* of a box `(i, j)` of a Young diagram consists of the box itself, the boxes to its
right in the same row (its *arm*) and the boxes below it in the same column (its *leg*); the
*hook length* `hookLength μ i j` is the number of boxes of the hook, that is

`hookLength μ i j = (μ_i - j) + (μ'_j - i) - 1`,

where `μ'` is the conjugate partition.

The main result of this file relates the product of the hook lengths of a row to the *first
column hook lengths* `colHook μ r = μ_r + (length μ - 1 - r)`: the hook lengths of the
row `r` are exactly the numbers `1, …, colHook μ r` from which the numbers
`colHook μ r - colHook μ s`, `s > r`, have been removed.

## Main definitions

* `Young.hookLength μ i j` : the hook length of the box `(i, j)` of `μ`.
* `Young.colHook μ r` : the hook length of the first box of the row `r`.
* `Young.rowHookProd μ r` : the product of the hook lengths of the row `r`.
* `Young.hookProd μ` : the product of all the hook lengths of `μ`.

## Main results

* `Young.rowHookProd_mul_prod_colHook_sub` : the product of the hook lengths of a row, times
  the product of the differences `colHook μ r - colHook μ s` for `s > r`, is
  `(colHook μ r)!`.
-/

@[expose] public section

namespace Young

open List Finset

variable {μ : List ℕ}

/-! ### Definitions -/

/-- The hook length of the box `(i, j)` of the shape `μ`: the number of boxes of `μ` that
are in the box `(i, j)`, to its right in the row `i`, or below it in the column `j`. -/
def hookLength (μ : List ℕ) (i j : ℕ) : ℕ :=
  (μ.getD i 0 - j) + ((conjPart μ).getD j 0 - i) - 1

/-- The hook length of the first box of the row `r`, that is `μ_r + (length μ - 1 - r)`. -/
def colHook (μ : List ℕ) (r : ℕ) : ℕ := μ.getD r 0 + (μ.length - 1 - r)

/-- The product of the hook lengths of the boxes of the row `r`. -/
def rowHookProd (μ : List ℕ) (r : ℕ) : ℕ :=
  ∏ c ∈ Finset.range (μ.getD r 0), hookLength μ r c

/-- The product of all the hook lengths of the shape `μ`. -/
def hookProd (μ : List ℕ) : ℕ := ∏ r ∈ Finset.range μ.length, rowHookProd μ r

/-! ### Elementary properties of the conjugate -/

/-- The first part of the conjugate partition is the number of rows. -/
lemma getD_conjPart_zero (hμ : IsPart μ) : (conjPart μ).getD 0 0 = μ.length := by
  rcases Nat.eq_zero_or_pos μ.length with hlen | hlen
  · have : μ = [] := List.eq_nil_of_length_eq_zero hlen
    subst this
    simp [conjPart]
  · have h1 : (conjPart μ).getD 0 0 ≤ μ.length := by
      rw [← getD_le_conjPart_iff hμ]
      simp
    have h2 : ¬ (conjPart μ).getD 0 0 ≤ μ.length - 1 := by
      rw [← getD_le_conjPart_iff hμ]
      have := hμ.getD_pos (i := μ.length - 1) (by omega)
      omega
    omega

/-- Every part of the conjugate partition is at most the number of rows. -/
lemma getD_conjPart_le (hμ : IsPart μ) (c : ℕ) : (conjPart μ).getD c 0 ≤ μ.length := by
  calc (conjPart μ).getD c 0 ≤ (conjPart μ).getD 0 0 :=
        (isPart_conjPart hμ).getD_antitone (Nat.zero_le c)
    _ = μ.length := getD_conjPart_zero hμ

/-- A box of the shape has a nonempty column in the conjugate. -/
lemma lt_getD_conjPart {r c : ℕ} (hμ : IsPart μ) (h : c < μ.getD r 0) :
    r < (conjPart μ).getD c 0 := (inShape_conjPart hμ r c).1 h

/-! ### The hook lengths of a row -/

/-- The complement `g c = c + (number of rows) - μ'_c` of the hook length of the box
`(r, c)` inside the first column hook length of the row `r`. -/
private def hookCompl (μ : List ℕ) (c : ℕ) : ℕ := c + μ.length - (conjPart μ).getD c 0

/-- The hook length of a box and its complement add up to the first column hook length. -/
private lemma hookLength_add_hookCompl (hμ : IsPart μ) {r c : ℕ} (hr : r < μ.length)
    (hc : c < μ.getD r 0) :
    hookLength μ r c + hookCompl μ c = colHook μ r := by
  have h1 : r < (conjPart μ).getD c 0 := lt_getD_conjPart hμ hc
  have h2 : (conjPart μ).getD c 0 ≤ μ.length := getD_conjPart_le hμ c
  simp only [hookLength, hookCompl, colHook]
  omega

/-- The hook length of a box of the shape is positive. -/
lemma one_le_hookLength (hμ : IsPart μ) {r c : ℕ} (hc : c < μ.getD r 0) :
    1 ≤ hookLength μ r c := by
  have h1 : r < (conjPart μ).getD c 0 := lt_getD_conjPart hμ hc
  simp only [hookLength]
  omega

/-- The complement of a hook length is strictly smaller than the first column hook length of
its row. -/
private lemma hookCompl_lt (hμ : IsPart μ) {r c : ℕ} (hr : r < μ.length) (hc : c < μ.getD r 0) :
    hookCompl μ c < colHook μ r := by
  have h1 : r < (conjPart μ).getD c 0 := lt_getD_conjPart hμ hc
  have h2 : (conjPart μ).getD c 0 ≤ μ.length := getD_conjPart_le hμ c
  have h3 := hookLength_add_hookCompl hμ hr hc
  have h4 : 1 ≤ hookLength μ r c := one_le_hookLength hμ hc
  omega

/-- The complement of the hook lengths is strictly increasing along a row. -/
private lemma hookCompl_strictMono (hμ : IsPart μ) {c c' : ℕ} (h : c < c') :
    hookCompl μ c < hookCompl μ c' := by
  have h1 : (conjPart μ).getD c' 0 ≤ (conjPart μ).getD c 0 :=
    (isPart_conjPart hμ).getD_antitone (le_of_lt h)
  have h2 : (conjPart μ).getD c 0 ≤ μ.length := getD_conjPart_le hμ c
  have h3 : (conjPart μ).getD c' 0 ≤ μ.length := getD_conjPart_le hμ c'
  simp only [hookCompl]
  omega

/-- The first column hook lengths are strictly decreasing. -/
lemma colHook_strictAnti (hμ : IsPart μ) {r s : ℕ} (hrs : r < s) (hs : s < μ.length) :
    colHook μ s < colHook μ r := by
  have h1 : μ.getD s 0 ≤ μ.getD r 0 := hμ.getD_antitone (le_of_lt hrs)
  simp only [colHook]
  omega

/-- The complement of a hook length of the row `r` is never a first column hook length of a
row below `r`. -/
private lemma hookCompl_ne_colHook (hμ : IsPart μ) {c s : ℕ} (hs : s < μ.length) :
    hookCompl μ c ≠ colHook μ s := by
  have h2 : (conjPart μ).getD c 0 ≤ μ.length := getD_conjPart_le hμ c
  rcases lt_or_ge c (μ.getD s 0) with hcs | hcs
  · have h1 : s < (conjPart μ).getD c 0 := lt_getD_conjPart hμ hcs
    simp only [hookCompl, colHook]
    omega
  · have h1 : (conjPart μ).getD c 0 ≤ s := (getD_le_conjPart_iff hμ s c).1 hcs
    simp only [hookCompl, colHook]
    omega

/-! ### The product of the hook lengths of a row -/

/-- The product `∏_{v < m} (m - v)` is `m !`. -/
lemma prod_range_sub (m : ℕ) : ∏ v ∈ Finset.range m, (m - v) = Nat.factorial m := by
  rw [← Finset.prod_range_reflect (fun v => m - v) m, ← Finset.prod_range_add_one_eq_factorial m]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  omega

/-- **The hook lengths of a row**: the product of the hook lengths of the row `r`, times the
product of the differences `colHook μ r - colHook μ s` over the rows `s` below `r`, is the
factorial of the first column hook length of the row `r`.  Equivalently, the hook lengths of
the row `r` are the numbers `1, …, colHook μ r` with the numbers `colHook μ r - colHook μ s`
removed. -/
theorem rowHookProd_mul_prod_colHook_sub (hμ : IsPart μ) {r : ℕ} (hr : r < μ.length) :
    rowHookProd μ r * ∏ s ∈ Finset.Ico (r + 1) μ.length, (colHook μ r - colHook μ s)
      = Nat.factorial (colHook μ r) := by
  classical
  set k := μ.length with hk
  set m := colHook μ r with hm
  set A := (Finset.range (μ.getD r 0)).image (hookCompl μ) with hA
  set B := (Finset.Ico (r + 1) k).image (colHook μ) with hB
  have hinjA : Set.InjOn (hookCompl μ) (Finset.range (μ.getD r 0)) := by
    intro a _ b _ hab
    by_contra hne
    rcases Nat.lt_or_ge a b with h | h
    · exact absurd hab (Nat.ne_of_lt (hookCompl_strictMono hμ h))
    · have h' : b < a := by omega
      exact absurd hab.symm (Nat.ne_of_lt (hookCompl_strictMono hμ h'))
  have hinjB : Set.InjOn (colHook μ) (Finset.Ico (r + 1) k) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_Ico] at ha hb
    by_contra hne
    rcases Nat.lt_or_ge a b with h | h
    · exact absurd hab.symm (Nat.ne_of_lt (colHook_strictAnti hμ h hb.2))
    · have h' : b < a := by omega
      exact absurd hab (Nat.ne_of_lt (colHook_strictAnti hμ h' ha.2))
  have hAsub : A ⊆ Finset.range m := by
    intro a ha
    rw [hA, Finset.mem_image] at ha
    obtain ⟨c, hc, rfl⟩ := ha
    rw [Finset.mem_range] at hc ⊢
    exact hookCompl_lt hμ hr hc
  have hBsub : B ⊆ Finset.range m := by
    intro b hb
    rw [hB, Finset.mem_image] at hb
    obtain ⟨s, hs, rfl⟩ := hb
    rw [Finset.mem_Ico] at hs
    rw [Finset.mem_range]
    exact colHook_strictAnti hμ hs.1 hs.2
  have hdisj : _root_.Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    rw [hA, Finset.mem_image] at haA
    rw [hB, Finset.mem_image] at haB
    obtain ⟨c, hc, rfl⟩ := haA
    obtain ⟨s, hs, hsc⟩ := haB
    rw [Finset.mem_range] at hc
    rw [Finset.mem_Ico] at hs
    exact hookCompl_ne_colHook hμ hs.2 hsc.symm
  have hcardA : A.card = μ.getD r 0 := by
    rw [hA, Finset.card_image_of_injOn hinjA, Finset.card_range]
  have hcardB : B.card = k - 1 - r := by
    rw [hB, Finset.card_image_of_injOn hinjB, Nat.card_Ico]
    omega
  have hunion : A ∪ B = Finset.range m := by
    refine Finset.eq_of_subset_of_card_le (Finset.union_subset hAsub hBsub) ?_
    rw [Finset.card_union_of_disjoint hdisj, hcardA, hcardB, Finset.card_range, hm, colHook]
  have hprodA : ∏ c ∈ Finset.range (μ.getD r 0), hookLength μ r c
      = ∏ a ∈ A, (m - a) := by
    rw [hA, Finset.prod_image hinjA]
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    have := hookLength_add_hookCompl hμ hr hc
    omega
  have hprodB : ∏ s ∈ Finset.Ico (r + 1) k, (m - colHook μ s) = ∏ b ∈ B, (m - b) := by
    rw [hB, Finset.prod_image hinjB]
  rw [rowHookProd, hprodA, hprodB, ← Finset.prod_union hdisj, hunion, prod_range_sub]

end Young
