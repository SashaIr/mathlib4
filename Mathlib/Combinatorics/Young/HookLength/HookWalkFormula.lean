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

Writing `F η = |η| ! / (∏ hook lengths)`, the walk started at a uniformly chosen box of
the diagram ends at the corner in the row `al` with probability `F (η ∖ al) / F η`;
since it ends at some corner, these probabilities add up to one, which is the recursion
satisfied by the number of standard Young tableaux (the branching rule).  The hook length
formula follows by induction on the number of boxes.

## Main results

* `Young.hookProd_decrNth_mul` : the hook lengths of the diagram obtained by removing a
  corner: they are those of `η`, the hook lengths of the boxes above and to the left of the
  corner being decreased by one.
* `Young.sum_hookWalkProb_cells` : starting from a uniformly chosen box, the walk ends at the
  corner of the row `al` with probability `(∏ hook lengths of η) / (|η| * ∏ hook lengths
  of η ∖ al)`.
* `Young.sum_hookProd_div_hookProd_decrNth` : **the Greene–Nijenhuis–Wilf identity**, the sum
  of these probabilities over the corners is one.
* `Young.numStdTab_mul_hookProd_hookWalk` : **the hook length formula**, proved by the hook
  walk.
* `Young.sum_hookWalkProb_cells_div_sum` : the walk started at a uniformly chosen box ends at
  a corner with the branching probability `f^(η ∖ c) / f^η`.
-/

@[expose] public section

namespace Young

open List Finset

variable {η : List ℕ} {al : ℕ}

/-! ### Auxiliary facts on shapes -/

/-- Removing a box does not increase the number of rows. -/
lemma length_decrNth_le : ∀ (μ : List ℕ) (i : ℕ), (decrNth μ i).length ≤ μ.length
  | [], _ => by simp [decrNth]
  | 0 :: _, 0 => by simp [decrNth]
  | 1 :: _, 0 => by simp [decrNth]
  | (_ + 2) :: _, 0 => by simp [decrNth]
  | n :: v, i + 1 => by
    simp only [decrNth, List.length_cons, Nat.add_le_add_iff_right]
    exact length_decrNth_le v i

/-- The product of the hook lengths as a product over any large enough range of rows. -/
lemma hookProd_eq_prod_range {μ : List ℕ} {N : ℕ} (h : μ.length ≤ N) :
    hookProd μ = ∏ r ∈ Finset.range N, rowHookProd μ r := by
  rw [hookProd, ← Finset.prod_range_mul_prod_Ico _ h]
  refine (mul_right_eq_self₀.2 (Or.inl ?_)).symm
  refine Finset.prod_eq_one fun r hr => ?_
  rw [Finset.mem_Ico] at hr
  rw [rowHookProd, List.getD_eq_default _ _ hr.1]
  simp

/-! ### The diagram with a corner removed -/

/-- Away from the column of the removed corner, the conjugate is unchanged. -/
lemma getD_conjPart_decrNth_of_ne (hη : IsPart η) (hal : IsRemCorner η al) {j : ℕ}
    (hj : j ≠ η.getD al 0 - 1) :
    (conjPart (decrNth η al)).getD j 0 = (conjPart η).getD j 0 := by
  have hμ : IsPart (decrNth η al) := isPart_decrNth hη hal
  have hle1 : (conjPart (decrNth η al)).getD j 0 ≤ (conjPart η).getD j 0 := by
    rw [← getD_le_conjPart_iff hμ]
    exact le_trans (getD_decrNth_le η al _)
      ((getD_le_conjPart_iff hη ((conjPart η).getD j 0) j).2 le_rfl)
  have hle2 : (conjPart η).getD j 0 ≤ (conjPart (decrNth η al)).getD j 0 := by
    rw [← getD_le_conjPart_iff hη]
    have h2 : (decrNth η al).getD ((conjPart (decrNth η al)).getD j 0) 0 ≤ j :=
      (getD_le_conjPart_iff hμ ((conjPart (decrNth η al)).getD j 0) j).2 le_rfl
    by_cases hi : (conjPart (decrNth η al)).getD j 0 = al
    · rw [hi, getD_decrNth_self] at h2
      rw [hi]
      simp only [IsRemCorner] at hal
      omega
    · rwa [getD_decrNth_of_ne hη hal (Ne.symm hi)] at h2
  omega

/-- At the column of the removed corner, the conjugate loses its last box. -/
lemma getD_conjPart_decrNth_self (hη : IsPart η) (hal : IsRemCorner η al) :
    (conjPart (decrNth η al)).getD (η.getD al 0 - 1) 0 = al := by
  have hμ : IsPart (decrNth η al) := isPart_decrNth hη hal
  have hle1 : (conjPart (decrNth η al)).getD (η.getD al 0 - 1) 0 ≤ al := by
    rw [← getD_le_conjPart_iff hμ, getD_decrNth_self]
  have hle2 : al ≤ (conjPart (decrNth η al)).getD (η.getD al 0 - 1) 0 := by
    by_contra hcon
    have hi : (conjPart (decrNth η al)).getD (η.getD al 0 - 1) 0 ≠ al := by omega
    have h2 : (decrNth η al).getD ((conjPart (decrNth η al)).getD (η.getD al 0 - 1) 0) 0
        ≤ η.getD al 0 - 1 :=
      (getD_le_conjPart_iff hμ _ _).2 le_rfl
    rw [getD_decrNth_of_ne hη hal (Ne.symm hi)] at h2
    have h3 : η.getD al 0 ≤ η.getD ((conjPart (decrNth η al)).getD (η.getD al 0 - 1) 0) 0 :=
      hη.getD_antitone (by omega)
    simp only [IsRemCorner] at hal
    omega
  omega

/-- Away from the row and the column of the removed corner, the hook lengths are unchanged. -/
lemma hookLength_decrNth_of_ne (hη : IsPart η) (hal : IsRemCorner η al) {i j : ℕ}
    (hi : i ≠ al) (hj : j ≠ η.getD al 0 - 1) :
    hookLength (decrNth η al) i j = hookLength η i j := by
  simp only [hookLength, getD_decrNth_of_ne hη hal (Ne.symm hi),
    getD_conjPart_decrNth_of_ne hη hal hj]

/-- In the row of the removed corner, the hook lengths decrease by one. -/
lemma hookLength_decrNth_row (hη : IsPart η) (hal : IsRemCorner η al) {j : ℕ}
    (hj : j < η.getD al 0 - 1) :
    hookLength (decrNth η al) al j + 1 = hookLength η al j := by
  have hjlam : j < η.getD al 0 := by omega
  have hconj : al < (conjPart η).getD j 0 := lt_getD_conjPart hη hjlam
  simp only [hookLength, getD_decrNth_self,
    getD_conjPart_decrNth_of_ne hη hal (by omega : j ≠ η.getD al 0 - 1)]
  omega

/-- In the column of the removed corner, the hook lengths decrease by one. -/
lemma hookLength_decrNth_col (hη : IsPart η) (hal : IsRemCorner η al) {i : ℕ}
    (hi : i < al) :
    hookLength (decrNth η al) i (η.getD al 0 - 1) + 1
      = hookLength η i (η.getD al 0 - 1) := by
  have hcell : η.getD al 0 - 1 < η.getD i 0 := corner_lt_getD hη hal (le_of_lt hi)
  simp only [hookLength, getD_decrNth_of_ne hη hal (by omega : al ≠ i),
    getD_conjPart_decrNth_self hη hal, getD_conjPart_corner hη hal]
  omega

/-- **The hook lengths after removing a corner**: the product of the hook lengths of
`η ∖ al`, times the hook lengths of `η` in the row and in the column of the corner, is
the product of the hook lengths of `η` times the corresponding hook lengths of `η ∖ al`.
-/
theorem hookProd_decrNth_mul (hη : IsPart η) (hal : IsRemCorner η al) :
    hookProd (decrNth η al) *
        ((∏ i ∈ Finset.range al, hookLength η i (η.getD al 0 - 1)) *
          ∏ j ∈ Finset.range (η.getD al 0 - 1), hookLength η al j)
      = hookProd η *
        ((∏ i ∈ Finset.range al, hookLength (decrNth η al) i (η.getD al 0 - 1)) *
          ∏ j ∈ Finset.range (η.getD al 0 - 1), hookLength (decrNth η al) al j) := by
  have hμ : IsPart (decrNth η al) := isPart_decrNth hη hal
  have hallt : al < η.length := hal.lt_length
  have hlen : (decrNth η al).length ≤ η.length := length_decrNth_le η al
  have hbe : η.getD al 0 = (η.getD al 0 - 1) + 1 := getD_corner hal
  -- the rows above the corner
  have hup : ∀ r ∈ Finset.range al,
      rowHookProd (decrNth η al) r * hookLength η r (η.getD al 0 - 1)
        = rowHookProd η r * hookLength (decrNth η al) r (η.getD al 0 - 1) := by
    intro r hr
    rw [Finset.mem_range] at hr
    have hcell : η.getD al 0 - 1 < η.getD r 0 := corner_lt_getD hη hal (le_of_lt hr)
    have hmem : η.getD al 0 - 1 ∈ Finset.range (η.getD r 0) := Finset.mem_range.2 hcell
    have hrow : rowHookProd (decrNth η al) r
        = ∏ c ∈ Finset.range (η.getD r 0), hookLength (decrNth η al) r c := by
      rw [rowHookProd, getD_decrNth_of_ne hη hal (by omega : al ≠ r)]
    rw [hrow, rowHookProd, ← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem,
      Finset.prod_congr rfl (fun c hc => hookLength_decrNth_of_ne hη hal (by omega : r ≠ al)
        (Finset.ne_of_mem_erase hc))]
    ring
  -- the row of the corner
  have hrowal : rowHookProd (decrNth η al) al
      = ∏ j ∈ Finset.range (η.getD al 0 - 1), hookLength (decrNth η al) al j := by
    rw [rowHookProd, getD_decrNth_self]
  have hrowlam : rowHookProd η al
      = ∏ j ∈ Finset.range (η.getD al 0 - 1), hookLength η al j := by
    have hcell : η.getD al 0 - 1 < η.getD al 0 := by omega
    have hone : hookLength η al (η.getD al 0 - 1) = 1 :=
      (hookLength_eq_one_iff hη hcell).2 ⟨hal, rfl⟩
    rw [rowHookProd]
    nth_rewrite 1 [hbe]
    rw [Finset.prod_range_succ, hone, mul_one]
  -- the rows below the corner
  have hdown : ∀ r ∈ Finset.Ico (al + 1) η.length,
      rowHookProd (decrNth η al) r = rowHookProd η r := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have hle : η.getD r 0 ≤ η.getD al 0 - 1 := by
      have h1 : η.getD r 0 ≤ η.getD (al + 1) 0 := hη.getD_antitone hr.1
      simp only [IsRemCorner] at hal
      omega
    rw [rowHookProd, rowHookProd, getD_decrNth_of_ne hη hal (by omega : al ≠ r)]
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    exact hookLength_decrNth_of_ne hη hal (by omega : r ≠ al) (by omega)
  -- splitting the products over the rows
  have hsplit : ∀ f : ℕ → ℕ, ∏ r ∈ Finset.range η.length, f r
      = ((∏ r ∈ Finset.range al, f r) * f al) * ∏ r ∈ Finset.Ico (al + 1) η.length, f r := by
    intro f
    rw [Finset.range_eq_Ico, ← Finset.prod_Ico_consecutive f (Nat.zero_le al) (le_of_lt hallt),
      Finset.prod_eq_prod_Ico_succ_bot hallt f, ← Finset.range_eq_Ico]
    ring
  rw [hookProd_eq_prod_range hlen, hookProd, hsplit (rowHookProd (decrNth η al)),
    hsplit (rowHookProd η), hrowal, hrowlam,
    Finset.prod_congr rfl hdown]
  have hcols : (∏ r ∈ Finset.range al, rowHookProd (decrNth η al) r) *
        ∏ i ∈ Finset.range al, hookLength η i (η.getD al 0 - 1)
      = (∏ r ∈ Finset.range al, rowHookProd η r) *
        ∏ i ∈ Finset.range al, hookLength (decrNth η al) i (η.getD al 0 - 1) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hup
  calc ((∏ r ∈ Finset.range al, rowHookProd (decrNth η al) r) *
          ∏ j ∈ Finset.range (η.getD al 0 - 1), hookLength (decrNth η al) al j) *
        (∏ r ∈ Finset.Ico (al + 1) η.length, rowHookProd η r) *
        ((∏ i ∈ Finset.range al, hookLength η i (η.getD al 0 - 1)) *
          ∏ j ∈ Finset.range (η.getD al 0 - 1), hookLength η al j)
      = ((∏ r ∈ Finset.range al, rowHookProd (decrNth η al) r) *
            ∏ i ∈ Finset.range al, hookLength η i (η.getD al 0 - 1)) *
          ((∏ j ∈ Finset.range (η.getD al 0 - 1), hookLength η al j) *
            (∏ r ∈ Finset.Ico (al + 1) η.length, rowHookProd η r) *
            ∏ j ∈ Finset.range (η.getD al 0 - 1), hookLength (decrNth η al) al j) := by
        ring
    _ = ((∏ r ∈ Finset.range al, rowHookProd η r) *
            ∏ i ∈ Finset.range al, hookLength (decrNth η al) i (η.getD al 0 - 1)) *
          ((∏ j ∈ Finset.range (η.getD al 0 - 1), hookLength η al j) *
            (∏ r ∈ Finset.Ico (al + 1) η.length, rowHookProd η r) *
            ∏ j ∈ Finset.range (η.getD al 0 - 1), hookLength (decrNth η al) al j) := by
        rw [hcols]
    _ = ((∏ r ∈ Finset.range al, rowHookProd η r) *
            ∏ j ∈ Finset.range (η.getD al 0 - 1), hookLength η al j) *
          (∏ r ∈ Finset.Ico (al + 1) η.length, rowHookProd η r) *
          ((∏ i ∈ Finset.range al, hookLength (decrNth η al) i (η.getD al 0 - 1)) *
            ∏ j ∈ Finset.range (η.getD al 0 - 1), hookLength (decrNth η al) al j) := by
        ring

/-! ### The probability of ending at a given corner -/

/-- Starting from a uniformly chosen box, the hook walk ends at the corner of the row `al`
with probability `(∏ hook lengths of η) / (|η| * ∏ hook lengths of η ∖ al)`. -/
lemma prod_one_add_gnwRow_mul (hη : IsPart η) (hal : IsRemCorner η al) :
    (∏ i ∈ Finset.range al, (1 + gnwRow η al i)) *
        ∏ i ∈ Finset.range al, (hookLength (decrNth η al) i (η.getD al 0 - 1) : ℚ)
      = ∏ i ∈ Finset.range al, (hookLength η i (η.getD al 0 - 1) : ℚ) := by
  have hμ : IsPart (decrNth η al) := isPart_decrNth hη hal
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hcell : η.getD al 0 - 1 < (decrNth η al).getD i 0 := by
    rw [getD_decrNth_of_ne hη hal (by omega : al ≠ i)]
    exact corner_lt_getD hη hal (le_of_lt hi)
  have hpos : 1 ≤ hookLength (decrNth η al) i (η.getD al 0 - 1) :=
    one_le_hookLength hμ hcell
  have hdec := hookLength_decrNth_col hη hal hi
  have hposQ : (1 : ℚ) ≤ (hookLength (decrNth η al) i (η.getD al 0 - 1) : ℚ) := by
    exact_mod_cast hpos
  have hcast : (hookLength (decrNth η al) i (η.getD al 0 - 1) : ℚ) + 1
      = (hookLength η i (η.getD al 0 - 1) : ℚ) := by exact_mod_cast hdec
  rw [gnwRow, ite_eq_right (by omega : ¬ i = al), ← hcast, add_sub_cancel_right]
  have hne : (hookLength (decrNth η al) i (η.getD al 0 - 1) : ℚ) ≠ 0 := by linarith
  field_simp

lemma prod_one_add_gnwCol_mul (hη : IsPart η) (hal : IsRemCorner η al) :
    (∏ j ∈ Finset.range (η.getD al 0 - 1), (1 + gnwCol η al j)) *
        ∏ j ∈ Finset.range (η.getD al 0 - 1), (hookLength (decrNth η al) al j : ℚ)
      = ∏ j ∈ Finset.range (η.getD al 0 - 1), (hookLength η al j : ℚ) := by
  have hμ : IsPart (decrNth η al) := isPart_decrNth hη hal
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hcell : j < (decrNth η al).getD al 0 := by
    rw [getD_decrNth_self]
    exact hj
  have hpos : 1 ≤ hookLength (decrNth η al) al j := one_le_hookLength hμ hcell
  have hdec := hookLength_decrNth_row hη hal hj
  have hposQ : (1 : ℚ) ≤ (hookLength (decrNth η al) al j : ℚ) := by exact_mod_cast hpos
  have hcast : (hookLength (decrNth η al) al j : ℚ) + 1 = (hookLength η al j : ℚ) := by
    exact_mod_cast hdec
  rw [gnwCol, ite_eq_right (by omega : ¬ j = η.getD al 0 - 1), ← hcast, add_sub_cancel_right]
  have hne : (hookLength (decrNth η al) al j : ℚ) ≠ 0 := by linarith
  field_simp

/-- Starting from a uniformly chosen box, the hook walk ends at the corner of the row `al`
with probability `(∏ hook lengths of η) / (|η| * ∏ hook lengths of η ∖ al)`. -/
theorem sum_hookWalkProb_cells (hη : IsPart η) (hal : IsRemCorner η al) :
    ∑ i ∈ Finset.range η.length, ∑ j ∈ Finset.range (η.getD i 0),
        hookWalkProb η (al, η.getD al 0 - 1) (i, j)
      = (hookProd η : ℚ) / hookProd (decrNth η al) := by
  have hμ : IsPart (decrNth η al) := isPart_decrNth hη hal
  have hallt : al < η.length := hal.lt_length
  have hbe : η.getD al 0 = (η.getD al 0 - 1) + 1 := getD_corner hal
  -- only the boxes above and to the left of the corner contribute
  have hstep1 : ∑ i ∈ Finset.range η.length, ∑ j ∈ Finset.range (η.getD i 0),
        hookWalkProb η (al, η.getD al 0 - 1) (i, j)
      = ∑ i ∈ Finset.range (al + 1), ∑ j ∈ Finset.range (η.getD i 0),
        hookWalkProb η (al, η.getD al 0 - 1) (i, j) := by
    refine (Finset.sum_subset (by
      intro i hi
      rw [Finset.mem_range] at hi ⊢
      omega) ?_).symm
    intro i hi hi'
    rw [Finset.mem_range] at hi hi'
    refine Finset.sum_eq_zero fun j _ => ?_
    exact hookWalkProb_eq_zero_of_not_le (by simp only; omega)
  have hstep2 : ∀ i ∈ Finset.range (al + 1), ∑ j ∈ Finset.range (η.getD i 0),
        hookWalkProb η (al, η.getD al 0 - 1) (i, j)
      = ∑ j ∈ Finset.range (η.getD al 0 - 1 + 1),
          gnwRow η al i * gnwCol η al j *
            (∏ i' ∈ Finset.Ioo i al, (1 + gnwRow η al i')) *
            ∏ j' ∈ Finset.Ioo j (η.getD al 0 - 1), (1 + gnwCol η al j') := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hcell : η.getD al 0 - 1 < η.getD i 0 := corner_lt_getD hη hal (by omega)
    rw [← Finset.sum_subset (s₁ := Finset.range (η.getD al 0 - 1 + 1)) (by
      intro j hj
      rw [Finset.mem_range] at hj ⊢
      omega)]
    · exact Finset.sum_congr rfl fun j hj => hookWalkProb_corner hη hal (by omega)
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
        gnwRow η al i * ∏ i' ∈ Finset.Ioo i al, (1 + gnwRow η al i')
      = ∏ i ∈ Finset.range al, (1 + gnwRow η al i) := by
    rw [hIcc, sum_Icc_mul_prod_Ioo (gnwRow η al) al al 0 (by omega), gnwRow_self,
      ← Finset.range_eq_Ico]
    ring
  have hprodcol : ∑ j ∈ Finset.range (η.getD al 0 - 1 + 1),
        gnwCol η al j * ∏ j' ∈ Finset.Ioo j (η.getD al 0 - 1), (1 + gnwCol η al j')
      = ∏ j ∈ Finset.range (η.getD al 0 - 1), (1 + gnwCol η al j) := by
    rw [hIcc, sum_Icc_mul_prod_Ioo (gnwCol η al) (η.getD al 0 - 1) (η.getD al 0 - 1) 0
      (by omega), gnwCol_self, ← Finset.range_eq_Ico]
    ring
  have hfactor : ∑ i ∈ Finset.range (al + 1), ∑ j ∈ Finset.range (η.getD al 0 - 1 + 1),
        gnwRow η al i * gnwCol η al j *
          (∏ i' ∈ Finset.Ioo i al, (1 + gnwRow η al i')) *
          ∏ j' ∈ Finset.Ioo j (η.getD al 0 - 1), (1 + gnwCol η al j')
      = (∑ i ∈ Finset.range (al + 1),
            gnwRow η al i * ∏ i' ∈ Finset.Ioo i al, (1 + gnwRow η al i')) *
        ∑ j ∈ Finset.range (η.getD al 0 - 1 + 1),
            gnwCol η al j * ∏ j' ∈ Finset.Ioo j (η.getD al 0 - 1), (1 + gnwCol η al j') := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfactor, hprodrow, hprodcol]
  -- comparison with the products of the hook lengths
  have hμpos : (0 : ℚ) < hookProd (decrNth η al) := by
    exact_mod_cast hookProd_pos hμ
  have hcolpos : (0 : ℚ) < ∏ i ∈ Finset.range al,
      (hookLength (decrNth η al) i (η.getD al 0 - 1) : ℚ) := by
    refine Finset.prod_pos fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hcell : η.getD al 0 - 1 < (decrNth η al).getD i 0 := by
      rw [getD_decrNth_of_ne hη hal (by omega : al ≠ i)]
      exact corner_lt_getD hη hal (le_of_lt hi)
    have := one_le_hookLength hμ hcell
    have : (1 : ℚ) ≤ (hookLength (decrNth η al) i (η.getD al 0 - 1) : ℚ) := by
      exact_mod_cast this
    linarith
  have hrowpos : (0 : ℚ) < ∏ j ∈ Finset.range (η.getD al 0 - 1),
      (hookLength (decrNth η al) al j : ℚ) := by
    refine Finset.prod_pos fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hcell : j < (decrNth η al).getD al 0 := by
      rw [getD_decrNth_self]; exact hj
    have := one_le_hookLength hμ hcell
    have : (1 : ℚ) ≤ (hookLength (decrNth η al) al j : ℚ) := by exact_mod_cast this
    linarith
  have hkey := hookProd_decrNth_mul hη hal
  have hkeyQ : (hookProd (decrNth η al) : ℚ) *
        ((∏ i ∈ Finset.range al, (hookLength η i (η.getD al 0 - 1) : ℚ)) *
          ∏ j ∈ Finset.range (η.getD al 0 - 1), (hookLength η al j : ℚ))
      = (hookProd η : ℚ) *
        ((∏ i ∈ Finset.range al, (hookLength (decrNth η al) i (η.getD al 0 - 1) : ℚ)) *
          ∏ j ∈ Finset.range (η.getD al 0 - 1), (hookLength (decrNth η al) al j : ℚ)) := by
    exact_mod_cast hkey
  rw [eq_div_iff (by linarith)]
  have hrowmul := prod_one_add_gnwRow_mul hη hal
  have hcolmul := prod_one_add_gnwCol_mul hη hal
  have hfin : ((∏ i ∈ Finset.range al, (1 + gnwRow η al i)) *
        ∏ j ∈ Finset.range (η.getD al 0 - 1), (1 + gnwCol η al j)) *
      (hookProd (decrNth η al) : ℚ) *
      ((∏ i ∈ Finset.range al, (hookLength (decrNth η al) i (η.getD al 0 - 1) : ℚ)) *
        ∏ j ∈ Finset.range (η.getD al 0 - 1), (hookLength (decrNth η al) al j : ℚ))
      = (hookProd η : ℚ) *
      ((∏ i ∈ Finset.range al, (hookLength (decrNth η al) i (η.getD al 0 - 1) : ℚ)) *
        ∏ j ∈ Finset.range (η.getD al 0 - 1), (hookLength (decrNth η al) al j : ℚ)) := by
    rw [← hkeyQ]
    calc ((∏ i ∈ Finset.range al, (1 + gnwRow η al i)) *
          ∏ j ∈ Finset.range (η.getD al 0 - 1), (1 + gnwCol η al j)) *
        (hookProd (decrNth η al) : ℚ) *
        ((∏ i ∈ Finset.range al, (hookLength (decrNth η al) i (η.getD al 0 - 1) : ℚ)) *
          ∏ j ∈ Finset.range (η.getD al 0 - 1), (hookLength (decrNth η al) al j : ℚ))
        = (hookProd (decrNth η al) : ℚ) *
          (((∏ i ∈ Finset.range al, (1 + gnwRow η al i)) *
              ∏ i ∈ Finset.range al, (hookLength (decrNth η al) i (η.getD al 0 - 1) : ℚ)) *
            ((∏ j ∈ Finset.range (η.getD al 0 - 1), (1 + gnwCol η al j)) *
              ∏ j ∈ Finset.range (η.getD al 0 - 1),
                (hookLength (decrNth η al) al j : ℚ))) := by ring
      _ = _ := by rw [hrowmul, hcolmul]
  have hposprod : (0 : ℚ) < (∏ i ∈ Finset.range al,
      (hookLength (decrNth η al) i (η.getD al 0 - 1) : ℚ)) *
      ∏ j ∈ Finset.range (η.getD al 0 - 1), (hookLength (decrNth η al) al j : ℚ) :=
    mul_pos hcolpos hrowpos
  exact mul_right_cancel₀ (ne_of_gt hposprod) hfin

/-! ### The Greene–Nijenhuis–Wilf identity and the hook length formula -/

/-- **The Greene–Nijenhuis–Wilf identity**: for a partition of `n`, the sum over the corners
of the ratios of the products of the hook lengths is `n`. -/
theorem sum_hookProd_div_hookProd_decrNth (hη : IsPart η) :
    ∑ r ∈ Finset.range η.length,
        (if IsRemCorner η r then (hookProd η : ℚ) / hookProd (decrNth η r) else 0)
      = η.sum := by
  have hexp : ∀ r ∈ Finset.range η.length,
      (if IsRemCorner η r then (hookProd η : ℚ) / hookProd (decrNth η r) else 0)
        = ∑ i ∈ Finset.range η.length, ∑ j ∈ Finset.range (η.getD i 0),
            (if IsRemCorner η r then
              hookWalkProb η (r, η.getD r 0 - 1) (i, j) else 0) := by
    intro r _
    by_cases hc : IsRemCorner η r
    · simp only [ite_eq_left hc]
      exact (sum_hookWalkProb_cells hη hc).symm
    · simp [hc]
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  have hone : ∀ i ∈ Finset.range η.length,
      ∑ r ∈ Finset.range η.length, ∑ j ∈ Finset.range (η.getD i 0),
        (if IsRemCorner η r then hookWalkProb η (r, η.getD r 0 - 1) (i, j) else 0)
      = (η.getD i 0 : ℚ) := by
    intro i _
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun j hj => sum_hookWalkProb_corners hη
      (i := i) (j := j) (Finset.mem_range.1 hj)]
    simp
  rw [Finset.sum_congr rfl hone, ← Nat.cast_sum, ← sum_eq_sum_range_getD η le_rfl]

private lemma numStdTab_mul_hookProd_aux :
    ∀ (n : ℕ) (η : List ℕ), IsPart η → η.sum = n →
      numStdTab η * hookProd η = Nat.factorial n := by
  intro n
  induction n with
  | zero =>
    intro η hη hsum
    rw [hη.eq_nil_of_sum_eq_zero hsum, numStdTab_nil, hookProd]
    simp
  | succ n ih =>
    intro η hη hsum
    have hbr := numStdTab_branching hη hsum (le_refl η.length)
    have hcast : (numStdTab η : ℚ)
        = ∑ r ∈ Finset.range η.length,
            (if IsRemCorner η r then (numStdTab (decrNth η r) : ℚ) else 0) := by
      rw [hbr]
      push_cast
      exact Finset.sum_congr rfl fun r _ => by by_cases hc : IsRemCorner η r <;> simp [hc]
    have hterm : ∀ r ∈ Finset.range η.length,
        (if IsRemCorner η r then (numStdTab (decrNth η r) : ℚ) else 0) * hookProd η
          = (Nat.factorial n : ℚ) *
            (if IsRemCorner η r then (hookProd η : ℚ) / hookProd (decrNth η r) else 0) := by
      intro r _
      by_cases hc : IsRemCorner η r
      · rw [ite_eq_left hc, ite_eq_left hc]
        have hμ : IsPart (decrNth η r) := isPart_decrNth hη hc
        have hsum' : (decrNth η r).sum = n := by rw [sum_decrNth hη hc, hsum]; omega
        have hIH : (numStdTab (decrNth η r) : ℚ) * hookProd (decrNth η r)
            = (Nat.factorial n : ℚ) := by exact_mod_cast ih (decrNth η r) hμ hsum'
        have hposQ : (0 : ℚ) < hookProd (decrNth η r) := by
          exact_mod_cast hookProd_pos hμ
        rw [← hIH]
        field_simp
      · simp [hc]
    have key : (numStdTab η : ℚ) * hookProd η = (Nat.factorial (n + 1) : ℚ) := by
      rw [hcast, Finset.sum_mul, Finset.sum_congr rfl hterm, ← Finset.mul_sum,
        sum_hookProd_div_hookProd_decrNth hη, hsum, Nat.factorial_succ]
      push_cast
      ring
    exact_mod_cast key

/-- **The hook length formula**, proved by the hook walk of Greene, Nijenhuis and Wilf: the
number of standard Young tableaux of shape a partition `η` of `n`, multiplied by the
product of the hook lengths of the boxes of `η`, is `n !`.

This is the theorem `Young.numStdTab_mul_hookProd`, obtained here by a different route: the
proof by the hook walk replaces the Frobenius formula for the number of standard tableaux by
the Greene–Nijenhuis–Wilf identity `Young.sum_hookProd_div_hookProd_decrNth`. -/
theorem numStdTab_mul_hookProd_hookWalk (hη : IsPart η) :
    numStdTab η * hookProd η = Nat.factorial η.sum :=
  numStdTab_mul_hookProd_aux η.sum η hη rfl

/-- **The hook walk ends at a corner with the branching probability**: the walk started at a
uniformly chosen box of a partition `η` of `n` ends at the corner of the row `al` with
probability `f^(η ∖ al) / f^η`, the ratio of the numbers of standard Young tableaux.
This is the statement which, by the branching rule, gives the hook length formula. -/
theorem sum_hookWalkProb_cells_div_sum (hη : IsPart η) (hal : IsRemCorner η al) :
    (∑ i ∈ Finset.range η.length, ∑ j ∈ Finset.range (η.getD i 0),
        hookWalkProb η (al, η.getD al 0 - 1) (i, j)) / η.sum
      = (numStdTab (decrNth η al) : ℚ) / numStdTab η := by
  have hμ : IsPart (decrNth η al) := isPart_decrNth hη hal
  have hallt : al < η.length := hal.lt_length
  have hn : 0 < η.sum := by
    have : 0 < η.getD al 0 := by simp only [IsRemCorner] at hal; omega
    have hle : η.getD al 0 ≤ η.sum := getD_le_sum _ _
    omega
  have hsum : (decrNth η al).sum = η.sum - 1 := sum_decrNth hη hal
  have hηf := numStdTab_mul_hookProd_hookWalk hη
  have hμf := numStdTab_mul_hookProd_hookWalk hμ
  rw [hsum] at hμf
  have hnum : (0 : ℚ) < numStdTab η := by exact_mod_cast numStdTab_pos hη
  have hnumu : (0 : ℚ) < numStdTab (decrNth η al) := by
    exact_mod_cast numStdTab_pos hμ
  have hprod : (0 : ℚ) < hookProd η := by exact_mod_cast hookProd_pos hη
  have hprodmu : (0 : ℚ) < hookProd (decrNth η al) := by exact_mod_cast hookProd_pos hμ
  have hfac : (Nat.factorial η.sum : ℚ) = η.sum * Nat.factorial (η.sum - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, η.sum = m + 1 := ⟨η.sum - 1, by omega⟩
    rw [hm]
    simp [Nat.factorial_succ]
  have h1 : (numStdTab η : ℚ) * hookProd η = (Nat.factorial η.sum : ℚ) := by
    exact_mod_cast hηf
  have h2 : (numStdTab (decrNth η al) : ℚ) * hookProd (decrNth η al)
      = (Nat.factorial (η.sum - 1) : ℚ) := by exact_mod_cast hμf
  rw [sum_hookWalkProb_cells hη hal, div_div, div_eq_div_iff (by positivity) (by positivity)]
  have hnQ : (0 : ℚ) < η.sum := by exact_mod_cast hn
  field_simp at h1 h2 ⊢
  nlinarith [h1, h2, hfac, hprodmu, hprod, hnumu, hnum]

end Young
