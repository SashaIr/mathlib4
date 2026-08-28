/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Combinatorics.Young.Shape.Conjugate

/-!
# Hook lengths

The *hook* of a box `(i, j)` of a Young diagram consists of the box itself, the boxes to its
right in the same row (its *arm*) and the boxes below it in the same column (its *leg*); the
*hook length* `hookLength sh i j` is the number of boxes of the hook, that is

`hookLength sh i j = (sh_i - j) + (sh'_j - i) - 1`,

where `sh'` is the conjugate partition.

The main result of this file relates the product of the hook lengths of a row to the *first
column hook lengths* `colHook sh r = sh_r + (length sh - 1 - r)`: the hook lengths of the
row `r` are exactly the numbers `1, …, colHook sh r` from which the numbers
`colHook sh r - colHook sh s`, `s > r`, have been removed.

## Main definitions

* `List.hookLength sh i j` : the hook length of the box `(i, j)` of `sh`.
* `List.colHook sh r` : the hook length of the first box of the row `r`.
* `List.rowHookProd sh r` : the product of the hook lengths of the row `r`.
* `List.hookProd sh` : the product of all the hook lengths of `sh`.

## Main results

* `List.rowHookProd_mul_prod_colHook_sub` : the product of the hook lengths of a row, times
  the product of the differences `colHook sh r - colHook sh s` for `s > r`, is
  `(colHook sh r)!`.
-/

namespace List

open List Finset

variable {sh : List ℕ}

/-! ### Definitions -/

/-- The hook length of the box `(i, j)` of the shape `sh`: the number of boxes of `sh` that
are in the box `(i, j)`, to its right in the row `i`, or below it in the column `j`. -/
def hookLength (sh : List ℕ) (i j : ℕ) : ℕ :=
  (sh.getD i 0 - j) + ((conjPart sh).getD j 0 - i) - 1

/-- The hook length of the first box of the row `r`, that is `sh_r + (length sh - 1 - r)`. -/
def colHook (sh : List ℕ) (r : ℕ) : ℕ := sh.getD r 0 + (sh.length - 1 - r)

/-- The product of the hook lengths of the boxes of the row `r`. -/
def rowHookProd (sh : List ℕ) (r : ℕ) : ℕ :=
  ∏ c ∈ Finset.range (sh.getD r 0), hookLength sh r c

/-- The product of all the hook lengths of the shape `sh`. -/
def hookProd (sh : List ℕ) : ℕ := ∏ r ∈ Finset.range sh.length, rowHookProd sh r

/-! ### Elementary properties of the conjugate -/

/-- The first part of the conjugate partition is the number of rows. -/
lemma getD_conjPart_zero (hsh : IsPart sh) : (conjPart sh).getD 0 0 = sh.length := by
  rcases Nat.eq_zero_or_pos sh.length with hlen | hlen
  · have : sh = [] := List.eq_nil_of_length_eq_zero hlen
    subst this
    simp [conjPart]
  · have h1 : (conjPart sh).getD 0 0 ≤ sh.length := by
      rw [← getD_le_conjPart_iff hsh]
      simp
    have h2 : ¬ (conjPart sh).getD 0 0 ≤ sh.length - 1 := by
      rw [← getD_le_conjPart_iff hsh]
      have := hsh.getD_pos (i := sh.length - 1) (by omega)
      omega
    omega

/-- Every part of the conjugate partition is at most the number of rows. -/
lemma getD_conjPart_le (hsh : IsPart sh) (c : ℕ) : (conjPart sh).getD c 0 ≤ sh.length := by
  calc (conjPart sh).getD c 0 ≤ (conjPart sh).getD 0 0 :=
        (isPart_conjPart hsh).getD_antitone (Nat.zero_le c)
    _ = sh.length := getD_conjPart_zero hsh

/-- A box of the shape has a nonempty column in the conjugate. -/
lemma lt_getD_conjPart {r c : ℕ} (hsh : IsPart sh) (h : c < sh.getD r 0) :
    r < (conjPart sh).getD c 0 := (inShape_conjPart hsh r c).1 h

/-! ### The hook lengths of a row -/

/-- The complement `g c = c + (number of rows) - sh'_c` of the hook length of the box
`(r, c)` inside the first column hook length of the row `r`. -/
private def hookCompl (sh : List ℕ) (c : ℕ) : ℕ := c + sh.length - (conjPart sh).getD c 0

/-- The hook length of a box and its complement add up to the first column hook length. -/
lemma hookLength_add_hookCompl (hsh : IsPart sh) {r c : ℕ} (hr : r < sh.length)
    (hc : c < sh.getD r 0) :
    hookLength sh r c + hookCompl sh c = colHook sh r := by
  have h1 : r < (conjPart sh).getD c 0 := lt_getD_conjPart hsh hc
  have h2 : (conjPart sh).getD c 0 ≤ sh.length := getD_conjPart_le hsh c
  simp only [hookLength, hookCompl, colHook]
  omega

/-- The hook length of a box of the shape is positive. -/
lemma one_le_hookLength (hsh : IsPart sh) {r c : ℕ} (hc : c < sh.getD r 0) :
    1 ≤ hookLength sh r c := by
  have h1 : r < (conjPart sh).getD c 0 := lt_getD_conjPart hsh hc
  simp only [hookLength]
  omega

/-- The complement of a hook length is strictly smaller than the first column hook length of
its row. -/
lemma hookCompl_lt (hsh : IsPart sh) {r c : ℕ} (hr : r < sh.length) (hc : c < sh.getD r 0) :
    hookCompl sh c < colHook sh r := by
  have h1 : r < (conjPart sh).getD c 0 := lt_getD_conjPart hsh hc
  have h2 : (conjPart sh).getD c 0 ≤ sh.length := getD_conjPart_le hsh c
  have h3 := hookLength_add_hookCompl hsh hr hc
  have h4 : 1 ≤ hookLength sh r c := one_le_hookLength hsh hc
  omega

/-- The complement of the hook lengths is strictly increasing along a row. -/
lemma hookCompl_strictMono (hsh : IsPart sh) {c c' : ℕ} (h : c < c') :
    hookCompl sh c < hookCompl sh c' := by
  have h1 : (conjPart sh).getD c' 0 ≤ (conjPart sh).getD c 0 :=
    (isPart_conjPart hsh).getD_antitone (le_of_lt h)
  have h2 : (conjPart sh).getD c 0 ≤ sh.length := getD_conjPart_le hsh c
  have h3 : (conjPart sh).getD c' 0 ≤ sh.length := getD_conjPart_le hsh c'
  simp only [hookCompl]
  omega

/-- The first column hook lengths are strictly decreasing. -/
lemma colHook_strictAnti (hsh : IsPart sh) {r s : ℕ} (hrs : r < s) (hs : s < sh.length) :
    colHook sh s < colHook sh r := by
  have h1 : sh.getD s 0 ≤ sh.getD r 0 := hsh.getD_antitone (le_of_lt hrs)
  simp only [colHook]
  omega

/-- The complement of a hook length of the row `r` is never a first column hook length of a
row below `r`. -/
lemma hookCompl_ne_colHook (hsh : IsPart sh) {c s : ℕ} (hs : s < sh.length) :
    hookCompl sh c ≠ colHook sh s := by
  have h2 : (conjPart sh).getD c 0 ≤ sh.length := getD_conjPart_le hsh c
  rcases lt_or_ge c (sh.getD s 0) with hcs | hcs
  · have h1 : s < (conjPart sh).getD c 0 := lt_getD_conjPart hsh hcs
    simp only [hookCompl, colHook]
    omega
  · have h1 : (conjPart sh).getD c 0 ≤ s := (getD_le_conjPart_iff hsh s c).1 hcs
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
product of the differences `colHook sh r - colHook sh s` over the rows `s` below `r`, is the
factorial of the first column hook length of the row `r`.  Equivalently, the hook lengths of
the row `r` are the numbers `1, …, colHook sh r` with the numbers `colHook sh r - colHook sh s`
removed. -/
theorem rowHookProd_mul_prod_colHook_sub (hsh : IsPart sh) {r : ℕ} (hr : r < sh.length) :
    rowHookProd sh r * ∏ s ∈ Finset.Ico (r + 1) sh.length, (colHook sh r - colHook sh s)
      = Nat.factorial (colHook sh r) := by
  classical
  set k := sh.length with hk
  set m := colHook sh r with hm
  set A := (Finset.range (sh.getD r 0)).image (hookCompl sh) with hA
  set B := (Finset.Ico (r + 1) k).image (colHook sh) with hB
  have hinjA : Set.InjOn (hookCompl sh) (Finset.range (sh.getD r 0)) := by
    intro a _ b _ hab
    by_contra hne
    rcases Nat.lt_or_ge a b with h | h
    · exact absurd hab (Nat.ne_of_lt (hookCompl_strictMono hsh h))
    · have h' : b < a := by omega
      exact absurd hab.symm (Nat.ne_of_lt (hookCompl_strictMono hsh h'))
  have hinjB : Set.InjOn (colHook sh) (Finset.Ico (r + 1) k) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_Ico] at ha hb
    by_contra hne
    rcases Nat.lt_or_ge a b with h | h
    · exact absurd hab.symm (Nat.ne_of_lt (colHook_strictAnti hsh h hb.2))
    · have h' : b < a := by omega
      exact absurd hab (Nat.ne_of_lt (colHook_strictAnti hsh h' ha.2))
  have hAsub : A ⊆ Finset.range m := by
    intro a ha
    rw [hA, Finset.mem_image] at ha
    obtain ⟨c, hc, rfl⟩ := ha
    rw [Finset.mem_range] at hc ⊢
    exact hookCompl_lt hsh hr hc
  have hBsub : B ⊆ Finset.range m := by
    intro b hb
    rw [hB, Finset.mem_image] at hb
    obtain ⟨s, hs, rfl⟩ := hb
    rw [Finset.mem_Ico] at hs
    rw [Finset.mem_range]
    exact colHook_strictAnti hsh hs.1 hs.2
  have hdisj : _root_.Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    rw [hA, Finset.mem_image] at haA
    rw [hB, Finset.mem_image] at haB
    obtain ⟨c, hc, rfl⟩ := haA
    obtain ⟨s, hs, hsc⟩ := haB
    rw [Finset.mem_range] at hc
    rw [Finset.mem_Ico] at hs
    exact hookCompl_ne_colHook hsh hs.2 hsc.symm
  have hcardA : A.card = sh.getD r 0 := by
    rw [hA, Finset.card_image_of_injOn hinjA, Finset.card_range]
  have hcardB : B.card = k - 1 - r := by
    rw [hB, Finset.card_image_of_injOn hinjB, Nat.card_Ico]
    omega
  have hunion : A ∪ B = Finset.range m := by
    refine Finset.eq_of_subset_of_card_le (Finset.union_subset hAsub hBsub) ?_
    rw [Finset.card_union_of_disjoint hdisj, hcardA, hcardB, Finset.card_range, hm, colHook]
  have hprodA : ∏ c ∈ Finset.range (sh.getD r 0), hookLength sh r c
      = ∏ a ∈ A, (m - a) := by
    rw [hA, Finset.prod_image hinjA]
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    have := hookLength_add_hookCompl hsh hr hc
    omega
  have hprodB : ∏ s ∈ Finset.Ico (r + 1) k, (m - colHook sh s) = ∏ b ∈ B, (m - b) := by
    rw [hB, Finset.prod_image hinjB]
  rw [rowHookProd, hprodA, hprodB, ← Finset.prod_union hdisj, hunion, prod_range_sub]

end List
