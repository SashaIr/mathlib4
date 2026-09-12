/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.HookLength.Formula
public import Mathlib.Combinatorics.Young.HookLength.HookWalk

/-!
# The Greene–Nijenhuis–Wilf proof of the hook length formula

Starting from the hook walk of `Mathlib/Combinatorics/Young/HookLength/HookWalk.lean`, this
file gives the probabilistic proof of the hook length formula due to Greene, Nijenhuis and Wilf (the
Coq file `HookFormula/hook.v`).

Writing `F μ = |μ| ! / (∏ hook lengths)`, the walk started at a uniformly chosen box of
the diagram ends at the corner in the row `al` with probability `F (μ ∖ al) / F μ`;
since it ends at some corner, these probabilities add up to one, which is the recursion
satisfied by the number of standard Young tableaux (the branching rule).  The hook length
formula follows by induction on the number of boxes.

## Main results

* `Young.hookProd_decrNth_mul` : the hook lengths of the diagram obtained by removing a
  corner: they are those of `μ`, the hook lengths of the boxes above and to the left of the
  corner being decreased by one.
* `Young.sum_hookWalkProb_cells` : starting from a uniformly chosen box, the walk ends at the
  corner of the row `al` with probability `(∏ hook lengths of μ) / (|μ| * ∏ hook lengths
  of μ ∖ al)`.
* `Young.sum_hookProd_div_hookProd_decrNth` : **the Greene–Nijenhuis–Wilf identity**, the sum
  of these probabilities over the corners is one.
* `Young.numStdTab_mul_hookProd_hookWalk` : **the hook length formula**, proved by the hook
  walk.
* `Young.sum_hookWalkProb_cells_div_sum` : the walk started at a uniformly chosen box ends at
  a corner with the branching probability `f^(μ ∖ c) / f^μ`.
-/

@[expose] public section

namespace Young

open List Finset

variable {μ : List ℕ} {al : ℕ}

/-! ### Auxiliary facts on shapes -/

/-- Removing a box does not increase the number of rows. -/
lemma length_decrNth_le : ∀ (ν : List ℕ) (i : ℕ), (decrNth ν i).length ≤ ν.length
  | [], _ => by simp [decrNth]
  | 0 :: _, 0 => by simp [decrNth]
  | 1 :: _, 0 => by simp [decrNth]
  | (_ + 2) :: _, 0 => by simp [decrNth]
  | n :: v, i + 1 => by
    simp only [decrNth, List.length_cons, Nat.add_le_add_iff_right]
    exact length_decrNth_le v i

/-- The product of the hook lengths as a product over any large enough range of rows. -/
lemma hookProd_eq_prod_range {ν : List ℕ} {N : ℕ} (h : ν.length ≤ N) :
    hookProd ν = ∏ r ∈ Finset.range N, rowHookProd ν r := by
  rw [hookProd, ← Finset.prod_range_mul_prod_Ico _ h]
  refine (mul_right_eq_self₀.2 (Or.inl ?_)).symm
  refine Finset.prod_eq_one fun r hr => ?_
  rw [Finset.mem_Ico] at hr
  rw [rowHookProd, List.getD_eq_default _ _ hr.1]
  simp

/-! ### The diagram with a corner removed -/

/-- Away from the column of the removed corner, the conjugate is unchanged. -/
lemma getD_conjPart_decrNth_of_ne (hμ : IsPart μ) (hal : IsRemCorner μ al) {j : ℕ}
    (hj : j ≠ μ.getD al 0 - 1) :
    (conjPart (decrNth μ al)).getD j 0 = (conjPart μ).getD j 0 := by
  have hν : IsPart (decrNth μ al) := isPart_decrNth hμ hal
  have hle1 : (conjPart (decrNth μ al)).getD j 0 ≤ (conjPart μ).getD j 0 := by
    rw [← getD_le_conjPart_iff hν]
    exact le_trans (getD_decrNth_le μ al _)
      ((getD_le_conjPart_iff hμ ((conjPart μ).getD j 0) j).2 le_rfl)
  have hle2 : (conjPart μ).getD j 0 ≤ (conjPart (decrNth μ al)).getD j 0 := by
    rw [← getD_le_conjPart_iff hμ]
    have h2 : (decrNth μ al).getD ((conjPart (decrNth μ al)).getD j 0) 0 ≤ j :=
      (getD_le_conjPart_iff hν ((conjPart (decrNth μ al)).getD j 0) j).2 le_rfl
    by_cases hi : (conjPart (decrNth μ al)).getD j 0 = al
    · rw [hi, getD_decrNth_self] at h2
      rw [hi]
      simp only [IsRemCorner] at hal
      omega
    · rwa [getD_decrNth_of_ne hμ hal (Ne.symm hi)] at h2
  omega

/-- At the column of the removed corner, the conjugate loses its last box. -/
lemma getD_conjPart_decrNth_self (hμ : IsPart μ) (hal : IsRemCorner μ al) :
    (conjPart (decrNth μ al)).getD (μ.getD al 0 - 1) 0 = al := by
  have hν : IsPart (decrNth μ al) := isPart_decrNth hμ hal
  have hle1 : (conjPart (decrNth μ al)).getD (μ.getD al 0 - 1) 0 ≤ al := by
    rw [← getD_le_conjPart_iff hν, getD_decrNth_self]
  have hle2 : al ≤ (conjPart (decrNth μ al)).getD (μ.getD al 0 - 1) 0 := by
    by_contra hcon
    have hi : (conjPart (decrNth μ al)).getD (μ.getD al 0 - 1) 0 ≠ al := by omega
    have h2 : (decrNth μ al).getD ((conjPart (decrNth μ al)).getD (μ.getD al 0 - 1) 0) 0
        ≤ μ.getD al 0 - 1 :=
      (getD_le_conjPart_iff hν _ _).2 le_rfl
    rw [getD_decrNth_of_ne hμ hal (Ne.symm hi)] at h2
    have h3 : μ.getD al 0 ≤ μ.getD ((conjPart (decrNth μ al)).getD (μ.getD al 0 - 1) 0) 0 :=
      hμ.getD_antitone (by omega)
    simp only [IsRemCorner] at hal
    omega
  omega

/-- Away from the row and the column of the removed corner, the hook lengths are unchanged. -/
lemma hookLength_decrNth_of_ne (hμ : IsPart μ) (hal : IsRemCorner μ al) {i j : ℕ}
    (hi : i ≠ al) (hj : j ≠ μ.getD al 0 - 1) :
    hookLength (decrNth μ al) i j = hookLength μ i j := by
  simp only [hookLength, getD_decrNth_of_ne hμ hal (Ne.symm hi),
    getD_conjPart_decrNth_of_ne hμ hal hj]

/-- In the row of the removed corner, the hook lengths decrease by one. -/
lemma hookLength_decrNth_row (hμ : IsPart μ) (hal : IsRemCorner μ al) {j : ℕ}
    (hj : j < μ.getD al 0 - 1) :
    hookLength (decrNth μ al) al j + 1 = hookLength μ al j := by
  have hjlam : j < μ.getD al 0 := by omega
  have hconj : al < (conjPart μ).getD j 0 := lt_getD_conjPart hμ hjlam
  simp only [hookLength, getD_decrNth_self,
    getD_conjPart_decrNth_of_ne hμ hal (by omega : j ≠ μ.getD al 0 - 1)]
  omega

/-- In the column of the removed corner, the hook lengths decrease by one. -/
lemma hookLength_decrNth_col (hμ : IsPart μ) (hal : IsRemCorner μ al) {i : ℕ}
    (hi : i < al) :
    hookLength (decrNth μ al) i (μ.getD al 0 - 1) + 1
      = hookLength μ i (μ.getD al 0 - 1) := by
  have hcell : μ.getD al 0 - 1 < μ.getD i 0 := corner_lt_getD hμ hal (le_of_lt hi)
  simp only [hookLength, getD_decrNth_of_ne hμ hal (by omega : al ≠ i),
    getD_conjPart_decrNth_self hμ hal, getD_conjPart_corner hμ hal]
  omega

/-- **The hook lengths after removing a corner**: the product of the hook lengths of
`μ ∖ al`, times the hook lengths of `μ` in the row and in the column of the corner, is
the product of the hook lengths of `μ` times the corresponding hook lengths of `μ ∖ al`.
-/
theorem hookProd_decrNth_mul (hμ : IsPart μ) (hal : IsRemCorner μ al) :
    hookProd (decrNth μ al) *
        ((∏ i ∈ Finset.range al, hookLength μ i (μ.getD al 0 - 1)) *
          ∏ j ∈ Finset.range (μ.getD al 0 - 1), hookLength μ al j)
      = hookProd μ *
        ((∏ i ∈ Finset.range al, hookLength (decrNth μ al) i (μ.getD al 0 - 1)) *
          ∏ j ∈ Finset.range (μ.getD al 0 - 1), hookLength (decrNth μ al) al j) := by
  have hν : IsPart (decrNth μ al) := isPart_decrNth hμ hal
  have hallt : al < μ.length := hal.lt_length
  have hlen : (decrNth μ al).length ≤ μ.length := length_decrNth_le μ al
  have hbe : μ.getD al 0 = (μ.getD al 0 - 1) + 1 := getD_corner hal
  -- the rows above the corner
  have hup : ∀ r ∈ Finset.range al,
      rowHookProd (decrNth μ al) r * hookLength μ r (μ.getD al 0 - 1)
        = rowHookProd μ r * hookLength (decrNth μ al) r (μ.getD al 0 - 1) := by
    intro r hr
    rw [Finset.mem_range] at hr
    have hcell : μ.getD al 0 - 1 < μ.getD r 0 := corner_lt_getD hμ hal (le_of_lt hr)
    have hmem : μ.getD al 0 - 1 ∈ Finset.range (μ.getD r 0) := Finset.mem_range.2 hcell
    have hrow : rowHookProd (decrNth μ al) r
        = ∏ c ∈ Finset.range (μ.getD r 0), hookLength (decrNth μ al) r c := by
      rw [rowHookProd, getD_decrNth_of_ne hμ hal (by omega : al ≠ r)]
    rw [hrow, rowHookProd, ← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem,
      Finset.prod_congr rfl (fun c hc => hookLength_decrNth_of_ne hμ hal (by omega : r ≠ al)
        (Finset.ne_of_mem_erase hc))]
    ring
  -- the row of the corner
  have hrowal : rowHookProd (decrNth μ al) al
      = ∏ j ∈ Finset.range (μ.getD al 0 - 1), hookLength (decrNth μ al) al j := by
    rw [rowHookProd, getD_decrNth_self]
  have hrowlam : rowHookProd μ al
      = ∏ j ∈ Finset.range (μ.getD al 0 - 1), hookLength μ al j := by
    have hcell : μ.getD al 0 - 1 < μ.getD al 0 := by omega
    have hone : hookLength μ al (μ.getD al 0 - 1) = 1 :=
      (hookLength_eq_one_iff hμ hcell).2 ⟨hal, rfl⟩
    rw [rowHookProd]
    nth_rewrite 1 [hbe]
    rw [Finset.prod_range_succ, hone, mul_one]
  -- the rows below the corner
  have hdown : ∀ r ∈ Finset.Ico (al + 1) μ.length,
      rowHookProd (decrNth μ al) r = rowHookProd μ r := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have hle : μ.getD r 0 ≤ μ.getD al 0 - 1 := by
      have h1 : μ.getD r 0 ≤ μ.getD (al + 1) 0 := hμ.getD_antitone hr.1
      simp only [IsRemCorner] at hal
      omega
    rw [rowHookProd, rowHookProd, getD_decrNth_of_ne hμ hal (by omega : al ≠ r)]
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    exact hookLength_decrNth_of_ne hμ hal (by omega : r ≠ al) (by omega)
  -- splitting the products over the rows
  have hsplit : ∀ f : ℕ → ℕ, ∏ r ∈ Finset.range μ.length, f r
      = ((∏ r ∈ Finset.range al, f r) * f al) * ∏ r ∈ Finset.Ico (al + 1) μ.length, f r := by
    intro f
    rw [Finset.range_eq_Ico, ← Finset.prod_Ico_consecutive f (Nat.zero_le al) (le_of_lt hallt),
      Finset.prod_eq_prod_Ico_succ_bot hallt f, ← Finset.range_eq_Ico]
    ring
  rw [hookProd_eq_prod_range hlen, hookProd, hsplit (rowHookProd (decrNth μ al)),
    hsplit (rowHookProd μ), hrowal, hrowlam,
    Finset.prod_congr rfl hdown]
  have hcols : (∏ r ∈ Finset.range al, rowHookProd (decrNth μ al) r) *
        ∏ i ∈ Finset.range al, hookLength μ i (μ.getD al 0 - 1)
      = (∏ r ∈ Finset.range al, rowHookProd μ r) *
        ∏ i ∈ Finset.range al, hookLength (decrNth μ al) i (μ.getD al 0 - 1) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hup
  calc ((∏ r ∈ Finset.range al, rowHookProd (decrNth μ al) r) *
          ∏ j ∈ Finset.range (μ.getD al 0 - 1), hookLength (decrNth μ al) al j) *
        (∏ r ∈ Finset.Ico (al + 1) μ.length, rowHookProd μ r) *
        ((∏ i ∈ Finset.range al, hookLength μ i (μ.getD al 0 - 1)) *
          ∏ j ∈ Finset.range (μ.getD al 0 - 1), hookLength μ al j)
      = ((∏ r ∈ Finset.range al, rowHookProd (decrNth μ al) r) *
            ∏ i ∈ Finset.range al, hookLength μ i (μ.getD al 0 - 1)) *
          ((∏ j ∈ Finset.range (μ.getD al 0 - 1), hookLength μ al j) *
            (∏ r ∈ Finset.Ico (al + 1) μ.length, rowHookProd μ r) *
            ∏ j ∈ Finset.range (μ.getD al 0 - 1), hookLength (decrNth μ al) al j) := by
        ring
    _ = ((∏ r ∈ Finset.range al, rowHookProd μ r) *
            ∏ i ∈ Finset.range al, hookLength (decrNth μ al) i (μ.getD al 0 - 1)) *
          ((∏ j ∈ Finset.range (μ.getD al 0 - 1), hookLength μ al j) *
            (∏ r ∈ Finset.Ico (al + 1) μ.length, rowHookProd μ r) *
            ∏ j ∈ Finset.range (μ.getD al 0 - 1), hookLength (decrNth μ al) al j) := by
        rw [hcols]
    _ = ((∏ r ∈ Finset.range al, rowHookProd μ r) *
            ∏ j ∈ Finset.range (μ.getD al 0 - 1), hookLength μ al j) *
          (∏ r ∈ Finset.Ico (al + 1) μ.length, rowHookProd μ r) *
          ((∏ i ∈ Finset.range al, hookLength (decrNth μ al) i (μ.getD al 0 - 1)) *
            ∏ j ∈ Finset.range (μ.getD al 0 - 1), hookLength (decrNth μ al) al j) := by
        ring

/-! ### The probability of ending at a given corner -/

/-- Starting from a uniformly chosen box, the hook walk ends at the corner of the row `al`
with probability `(∏ hook lengths of μ) / (|μ| * ∏ hook lengths of μ ∖ al)`. -/
lemma prod_one_add_gnwRow_mul (hμ : IsPart μ) (hal : IsRemCorner μ al) :
    (∏ i ∈ Finset.range al, (1 + gnwRow μ al i)) *
        ∏ i ∈ Finset.range al, (hookLength (decrNth μ al) i (μ.getD al 0 - 1) : ℚ)
      = ∏ i ∈ Finset.range al, (hookLength μ i (μ.getD al 0 - 1) : ℚ) := by
  have hν : IsPart (decrNth μ al) := isPart_decrNth hμ hal
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hcell : μ.getD al 0 - 1 < (decrNth μ al).getD i 0 := by
    rw [getD_decrNth_of_ne hμ hal (by omega : al ≠ i)]
    exact corner_lt_getD hμ hal (le_of_lt hi)
  have hpos : 1 ≤ hookLength (decrNth μ al) i (μ.getD al 0 - 1) :=
    one_le_hookLength hν hcell
  have hdec := hookLength_decrNth_col hμ hal hi
  have hposQ : (1 : ℚ) ≤ (hookLength (decrNth μ al) i (μ.getD al 0 - 1) : ℚ) := by
    exact_mod_cast hpos
  have hcast : (hookLength (decrNth μ al) i (μ.getD al 0 - 1) : ℚ) + 1
      = (hookLength μ i (μ.getD al 0 - 1) : ℚ) := by exact_mod_cast hdec
  rw [gnwRow, ite_eq_right (by omega : ¬ i = al), ← hcast, add_sub_cancel_right]
  have hne : (hookLength (decrNth μ al) i (μ.getD al 0 - 1) : ℚ) ≠ 0 := by linarith
  field_simp

lemma prod_one_add_gnwCol_mul (hμ : IsPart μ) (hal : IsRemCorner μ al) :
    (∏ j ∈ Finset.range (μ.getD al 0 - 1), (1 + gnwCol μ al j)) *
        ∏ j ∈ Finset.range (μ.getD al 0 - 1), (hookLength (decrNth μ al) al j : ℚ)
      = ∏ j ∈ Finset.range (μ.getD al 0 - 1), (hookLength μ al j : ℚ) := by
  have hν : IsPart (decrNth μ al) := isPart_decrNth hμ hal
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hcell : j < (decrNth μ al).getD al 0 := by
    rw [getD_decrNth_self]
    exact hj
  have hpos : 1 ≤ hookLength (decrNth μ al) al j := one_le_hookLength hν hcell
  have hdec := hookLength_decrNth_row hμ hal hj
  have hposQ : (1 : ℚ) ≤ (hookLength (decrNth μ al) al j : ℚ) := by exact_mod_cast hpos
  have hcast : (hookLength (decrNth μ al) al j : ℚ) + 1 = (hookLength μ al j : ℚ) := by
    exact_mod_cast hdec
  rw [gnwCol, ite_eq_right (by omega : ¬ j = μ.getD al 0 - 1), ← hcast, add_sub_cancel_right]
  have hne : (hookLength (decrNth μ al) al j : ℚ) ≠ 0 := by linarith
  field_simp

/-- Starting from a uniformly chosen box, the hook walk ends at the corner of the row `al`
with probability `(∏ hook lengths of μ) / (|μ| * ∏ hook lengths of μ ∖ al)`. -/
theorem sum_hookWalkProb_cells (hμ : IsPart μ) (hal : IsRemCorner μ al) :
    ∑ i ∈ Finset.range μ.length, ∑ j ∈ Finset.range (μ.getD i 0),
        hookWalkProb μ (al, μ.getD al 0 - 1) (i, j)
      = (hookProd μ : ℚ) / hookProd (decrNth μ al) := by
  have hν : IsPart (decrNth μ al) := isPart_decrNth hμ hal
  have hallt : al < μ.length := hal.lt_length
  have hbe : μ.getD al 0 = (μ.getD al 0 - 1) + 1 := getD_corner hal
  -- only the boxes above and to the left of the corner contribute
  have hstep1 : ∑ i ∈ Finset.range μ.length, ∑ j ∈ Finset.range (μ.getD i 0),
        hookWalkProb μ (al, μ.getD al 0 - 1) (i, j)
      = ∑ i ∈ Finset.range (al + 1), ∑ j ∈ Finset.range (μ.getD i 0),
        hookWalkProb μ (al, μ.getD al 0 - 1) (i, j) := by
    refine (Finset.sum_subset (by
      intro i hi
      rw [Finset.mem_range] at hi ⊢
      omega) ?_).symm
    intro i hi hi'
    rw [Finset.mem_range] at hi hi'
    refine Finset.sum_eq_zero fun j _ => ?_
    exact hookWalkProb_eq_zero_of_not_le (by simp only; omega)
  have hstep2 : ∀ i ∈ Finset.range (al + 1), ∑ j ∈ Finset.range (μ.getD i 0),
        hookWalkProb μ (al, μ.getD al 0 - 1) (i, j)
      = ∑ j ∈ Finset.range (μ.getD al 0 - 1 + 1),
          gnwRow μ al i * gnwCol μ al j *
            (∏ i' ∈ Finset.Ioo i al, (1 + gnwRow μ al i')) *
            ∏ j' ∈ Finset.Ioo j (μ.getD al 0 - 1), (1 + gnwCol μ al j') := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hcell : μ.getD al 0 - 1 < μ.getD i 0 := corner_lt_getD hμ hal (by omega)
    rw [← Finset.sum_subset (s₁ := Finset.range (μ.getD al 0 - 1 + 1)) (by
      intro j hj
      rw [Finset.mem_range] at hj ⊢
      omega)]
    · exact Finset.sum_congr rfl fun j hj => hookWalkProb_corner hμ hal (by omega)
        (by rw [Finset.mem_range] at hj; omega)
    · intro j hj hj'
      rw [Finset.mem_range] at hj hj'
      exact hookWalkProb_eq_zero_of_not_le (by simp only; omega)
  rw [hstep1, Finset.sum_congr rfl hstep2]
  -- the two telescoping sums
  have hIcc : ∀ m : ℕ, Finset.range (m + 1) = Finset.Icc 0 m := by
    intro m
    ext k
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega
  have hprodrow : ∑ i ∈ Finset.range (al + 1),
        gnwRow μ al i * ∏ i' ∈ Finset.Ioo i al, (1 + gnwRow μ al i')
      = ∏ i ∈ Finset.range al, (1 + gnwRow μ al i) := by
    rw [hIcc, sum_Icc_mul_prod_Ioo (gnwRow μ al) al al 0 (by omega), gnwRow_self,
      ← Finset.range_eq_Ico]
    ring
  have hprodcol : ∑ j ∈ Finset.range (μ.getD al 0 - 1 + 1),
        gnwCol μ al j * ∏ j' ∈ Finset.Ioo j (μ.getD al 0 - 1), (1 + gnwCol μ al j')
      = ∏ j ∈ Finset.range (μ.getD al 0 - 1), (1 + gnwCol μ al j) := by
    rw [hIcc, sum_Icc_mul_prod_Ioo (gnwCol μ al) (μ.getD al 0 - 1) (μ.getD al 0 - 1) 0
      (by omega), gnwCol_self, ← Finset.range_eq_Ico]
    ring
  have hfactor : ∑ i ∈ Finset.range (al + 1), ∑ j ∈ Finset.range (μ.getD al 0 - 1 + 1),
        gnwRow μ al i * gnwCol μ al j *
          (∏ i' ∈ Finset.Ioo i al, (1 + gnwRow μ al i')) *
          ∏ j' ∈ Finset.Ioo j (μ.getD al 0 - 1), (1 + gnwCol μ al j')
      = (∑ i ∈ Finset.range (al + 1),
            gnwRow μ al i * ∏ i' ∈ Finset.Ioo i al, (1 + gnwRow μ al i')) *
        ∑ j ∈ Finset.range (μ.getD al 0 - 1 + 1),
            gnwCol μ al j * ∏ j' ∈ Finset.Ioo j (μ.getD al 0 - 1), (1 + gnwCol μ al j') := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfactor, hprodrow, hprodcol]
  -- comparison with the products of the hook lengths
  have hνpos : (0 : ℚ) < hookProd (decrNth μ al) := by
    exact_mod_cast hookProd_pos hν
  have hcolpos : (0 : ℚ) < ∏ i ∈ Finset.range al,
      (hookLength (decrNth μ al) i (μ.getD al 0 - 1) : ℚ) := by
    refine Finset.prod_pos fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hcell : μ.getD al 0 - 1 < (decrNth μ al).getD i 0 := by
      rw [getD_decrNth_of_ne hμ hal (by omega : al ≠ i)]
      exact corner_lt_getD hμ hal (le_of_lt hi)
    have := one_le_hookLength hν hcell
    have : (1 : ℚ) ≤ (hookLength (decrNth μ al) i (μ.getD al 0 - 1) : ℚ) := by
      exact_mod_cast this
    linarith
  have hrowpos : (0 : ℚ) < ∏ j ∈ Finset.range (μ.getD al 0 - 1),
      (hookLength (decrNth μ al) al j : ℚ) := by
    refine Finset.prod_pos fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hcell : j < (decrNth μ al).getD al 0 := by
      rw [getD_decrNth_self]; exact hj
    have := one_le_hookLength hν hcell
    have : (1 : ℚ) ≤ (hookLength (decrNth μ al) al j : ℚ) := by exact_mod_cast this
    linarith
  have hkey := hookProd_decrNth_mul hμ hal
  have hkeyQ : (hookProd (decrNth μ al) : ℚ) *
        ((∏ i ∈ Finset.range al, (hookLength μ i (μ.getD al 0 - 1) : ℚ)) *
          ∏ j ∈ Finset.range (μ.getD al 0 - 1), (hookLength μ al j : ℚ))
      = (hookProd μ : ℚ) *
        ((∏ i ∈ Finset.range al, (hookLength (decrNth μ al) i (μ.getD al 0 - 1) : ℚ)) *
          ∏ j ∈ Finset.range (μ.getD al 0 - 1), (hookLength (decrNth μ al) al j : ℚ)) := by
    exact_mod_cast hkey
  rw [eq_div_iff (by linarith)]
  have hrowmul := prod_one_add_gnwRow_mul hμ hal
  have hcolmul := prod_one_add_gnwCol_mul hμ hal
  have hfin : ((∏ i ∈ Finset.range al, (1 + gnwRow μ al i)) *
        ∏ j ∈ Finset.range (μ.getD al 0 - 1), (1 + gnwCol μ al j)) *
      (hookProd (decrNth μ al) : ℚ) *
      ((∏ i ∈ Finset.range al, (hookLength (decrNth μ al) i (μ.getD al 0 - 1) : ℚ)) *
        ∏ j ∈ Finset.range (μ.getD al 0 - 1), (hookLength (decrNth μ al) al j : ℚ))
      = (hookProd μ : ℚ) *
      ((∏ i ∈ Finset.range al, (hookLength (decrNth μ al) i (μ.getD al 0 - 1) : ℚ)) *
        ∏ j ∈ Finset.range (μ.getD al 0 - 1), (hookLength (decrNth μ al) al j : ℚ)) := by
    rw [← hkeyQ]
    calc ((∏ i ∈ Finset.range al, (1 + gnwRow μ al i)) *
          ∏ j ∈ Finset.range (μ.getD al 0 - 1), (1 + gnwCol μ al j)) *
        (hookProd (decrNth μ al) : ℚ) *
        ((∏ i ∈ Finset.range al, (hookLength (decrNth μ al) i (μ.getD al 0 - 1) : ℚ)) *
          ∏ j ∈ Finset.range (μ.getD al 0 - 1), (hookLength (decrNth μ al) al j : ℚ))
        = (hookProd (decrNth μ al) : ℚ) *
          (((∏ i ∈ Finset.range al, (1 + gnwRow μ al i)) *
              ∏ i ∈ Finset.range al, (hookLength (decrNth μ al) i (μ.getD al 0 - 1) : ℚ)) *
            ((∏ j ∈ Finset.range (μ.getD al 0 - 1), (1 + gnwCol μ al j)) *
              ∏ j ∈ Finset.range (μ.getD al 0 - 1),
                (hookLength (decrNth μ al) al j : ℚ))) := by ring
      _ = _ := by rw [hrowmul, hcolmul]
  have hposprod : (0 : ℚ) < (∏ i ∈ Finset.range al,
      (hookLength (decrNth μ al) i (μ.getD al 0 - 1) : ℚ)) *
      ∏ j ∈ Finset.range (μ.getD al 0 - 1), (hookLength (decrNth μ al) al j : ℚ) :=
    mul_pos hcolpos hrowpos
  exact mul_right_cancel₀ (ne_of_gt hposprod) hfin

/-! ### The Greene–Nijenhuis–Wilf identity and the hook length formula -/

/-- **The Greene–Nijenhuis–Wilf identity**: for a partition of `n`, the sum over the corners
of the ratios of the products of the hook lengths is `n`. -/
theorem sum_hookProd_div_hookProd_decrNth (hμ : IsPart μ) :
    ∑ r ∈ Finset.range μ.length,
        (if IsRemCorner μ r then (hookProd μ : ℚ) / hookProd (decrNth μ r) else 0)
      = μ.sum := by
  have hexp : ∀ r ∈ Finset.range μ.length,
      (if IsRemCorner μ r then (hookProd μ : ℚ) / hookProd (decrNth μ r) else 0)
        = ∑ i ∈ Finset.range μ.length, ∑ j ∈ Finset.range (μ.getD i 0),
            (if IsRemCorner μ r then
              hookWalkProb μ (r, μ.getD r 0 - 1) (i, j) else 0) := by
    intro r _
    by_cases hc : IsRemCorner μ r
    · simp only [ite_eq_left hc]
      exact (sum_hookWalkProb_cells hμ hc).symm
    · simp [hc]
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  have hone : ∀ i ∈ Finset.range μ.length,
      ∑ r ∈ Finset.range μ.length, ∑ j ∈ Finset.range (μ.getD i 0),
        (if IsRemCorner μ r then hookWalkProb μ (r, μ.getD r 0 - 1) (i, j) else 0)
      = (μ.getD i 0 : ℚ) := by
    intro i _
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun j hj => sum_hookWalkProb_corners hμ
      (i := i) (j := j) (Finset.mem_range.1 hj)]
    simp
  rw [Finset.sum_congr rfl hone, ← Nat.cast_sum, ← sum_eq_sum_range_getD μ le_rfl]

private lemma numStdTab_mul_hookProd_aux :
    ∀ (n : ℕ) (μ : List ℕ), IsPart μ → μ.sum = n →
      numStdTab μ * hookProd μ = Nat.factorial n := by
  intro n
  induction n with
  | zero =>
    intro μ hμ hsum
    rw [hμ.eq_nil_of_sum_eq_zero hsum, numStdTab_nil, hookProd]
    simp
  | succ n ih =>
    intro μ hμ hsum
    have hbr := numStdTab_branching hμ hsum (le_refl μ.length)
    have hcast : (numStdTab μ : ℚ)
        = ∑ r ∈ Finset.range μ.length,
            (if IsRemCorner μ r then (numStdTab (decrNth μ r) : ℚ) else 0) := by
      rw [hbr]
      push_cast
      exact Finset.sum_congr rfl fun r _ => by by_cases hc : IsRemCorner μ r <;> simp [hc]
    have hterm : ∀ r ∈ Finset.range μ.length,
        (if IsRemCorner μ r then (numStdTab (decrNth μ r) : ℚ) else 0) * hookProd μ
          = (Nat.factorial n : ℚ) *
            (if IsRemCorner μ r then (hookProd μ : ℚ) / hookProd (decrNth μ r) else 0) := by
      intro r _
      by_cases hc : IsRemCorner μ r
      · rw [ite_eq_left hc, ite_eq_left hc]
        have hν : IsPart (decrNth μ r) := isPart_decrNth hμ hc
        have hsum' : (decrNth μ r).sum = n := by rw [sum_decrNth hμ hc, hsum]; omega
        have hIH : (numStdTab (decrNth μ r) : ℚ) * hookProd (decrNth μ r)
            = (Nat.factorial n : ℚ) := by exact_mod_cast ih (decrNth μ r) hν hsum'
        have hposQ : (0 : ℚ) < hookProd (decrNth μ r) := by
          exact_mod_cast hookProd_pos hν
        rw [← hIH]
        field_simp
      · simp [hc]
    have key : (numStdTab μ : ℚ) * hookProd μ = (Nat.factorial (n + 1) : ℚ) := by
      rw [hcast, Finset.sum_mul, Finset.sum_congr rfl hterm, ← Finset.mul_sum,
        sum_hookProd_div_hookProd_decrNth hμ, hsum, Nat.factorial_succ]
      push_cast
      ring
    exact_mod_cast key

/-- **The hook length formula**, proved by the hook walk of Greene, Nijenhuis and Wilf: the
number of standard Young tableaux of shape a partition `μ` of `n`, multiplied by the
product of the hook lengths of the boxes of `μ`, is `n !`.

This is the theorem `Young.numStdTab_mul_hookProd`, obtained here by a different route: the
proof by the hook walk replaces the Frobenius formula for the number of standard tableaux by
the Greene–Nijenhuis–Wilf identity `Young.sum_hookProd_div_hookProd_decrNth`. -/
theorem numStdTab_mul_hookProd_hookWalk (hμ : IsPart μ) :
    numStdTab μ * hookProd μ = Nat.factorial μ.sum :=
  numStdTab_mul_hookProd_aux μ.sum μ hμ rfl

/-- **The hook walk ends at a corner with the branching probability**: the walk started at a
uniformly chosen box of a partition `μ` of `n` ends at the corner of the row `al` with
probability `f^(μ ∖ al) / f^μ`, the ratio of the numbers of standard Young tableaux.
This is the statement which, by the branching rule, gives the hook length formula. -/
theorem sum_hookWalkProb_cells_div_sum (hμ : IsPart μ) (hal : IsRemCorner μ al) :
    (∑ i ∈ Finset.range μ.length, ∑ j ∈ Finset.range (μ.getD i 0),
        hookWalkProb μ (al, μ.getD al 0 - 1) (i, j)) / μ.sum
      = (numStdTab (decrNth μ al) : ℚ) / numStdTab μ := by
  have hν : IsPart (decrNth μ al) := isPart_decrNth hμ hal
  have hallt : al < μ.length := hal.lt_length
  have hn : 0 < μ.sum := by
    have : 0 < μ.getD al 0 := by simp only [IsRemCorner] at hal; omega
    have hle : μ.getD al 0 ≤ μ.sum := getD_le_sum _ _
    omega
  have hsum : (decrNth μ al).sum = μ.sum - 1 := sum_decrNth hμ hal
  have hμf := numStdTab_mul_hookProd_hookWalk hμ
  have hνf := numStdTab_mul_hookProd_hookWalk hν
  rw [hsum] at hνf
  have hnum : (0 : ℚ) < numStdTab μ := by exact_mod_cast numStdTab_pos hμ
  have hnumu : (0 : ℚ) < numStdTab (decrNth μ al) := by
    exact_mod_cast numStdTab_pos hν
  have hprod : (0 : ℚ) < hookProd μ := by exact_mod_cast hookProd_pos hμ
  have hprodmu : (0 : ℚ) < hookProd (decrNth μ al) := by exact_mod_cast hookProd_pos hν
  have hfac : (Nat.factorial μ.sum : ℚ) = μ.sum * Nat.factorial (μ.sum - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, μ.sum = m + 1 := ⟨μ.sum - 1, by omega⟩
    rw [hm]
    simp [Nat.factorial_succ]
  have h1 : (numStdTab μ : ℚ) * hookProd μ = (Nat.factorial μ.sum : ℚ) := by
    exact_mod_cast hμf
  have h2 : (numStdTab (decrNth μ al) : ℚ) * hookProd (decrNth μ al)
      = (Nat.factorial (μ.sum - 1) : ℚ) := by exact_mod_cast hνf
  rw [sum_hookWalkProb_cells hμ hal, div_div, div_eq_div_iff (by positivity) (by positivity)]
  have hnQ : (0 : ℚ) < μ.sum := by exact_mod_cast hn
  field_simp at h1 h2 ⊢
  nlinarith [h1, h2, hfac, hprodmu, hprod, hnumu, hnum]

end Young
