/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.HookLength.Formula
import Mathlib.Combinatorics.Young.HookLength.HookWalk

/-!
# The Greene–Nijenhuis–Wilf proof of the hook length formula

Starting from the hook walk of `Mathlib/Combinatorics/Young/HookLength/HookWalk.lean`, this
file gives the probabilistic proof of the hook length formula due to Greene, Nijenhuis and Wilf (the
Coq file `HookFormula/hook.v`).

Writing `F lam = |lam| ! / (∏ hook lengths)`, the walk started at a uniformly chosen box of
the diagram ends at the corner in the row `al` with probability `F (lam ∖ al) / F lam`;
since it ends at some corner, these probabilities add up to one, which is the recursion
satisfied by the number of standard Young tableaux (the branching rule).  The hook length
formula follows by induction on the number of boxes.

## Main results

* `List.hookProd_decrNth_mul` : the hook lengths of the diagram obtained by removing a
  corner: they are those of `lam`, the hook lengths of the boxes above and to the left of the
  corner being decreased by one.
* `List.sum_hookWalkProb_cells` : starting from a uniformly chosen box, the walk ends at the
  corner of the row `al` with probability `(∏ hook lengths of lam) / (|lam| * ∏ hook lengths
  of lam ∖ al)`.
* `List.sum_hookProd_div_hookProd_decrNth` : **the Greene–Nijenhuis–Wilf identity**, the sum
  of these probabilities over the corners is one.
* `List.numStdTab_mul_hookProd_hookWalk` : **the hook length formula**, proved by the hook
  walk.
* `List.sum_hookWalkProb_cells_div_sum` : the walk started at a uniformly chosen box ends at
  a corner with the branching probability `f^(lam ∖ c) / f^lam`.
-/

namespace List

open List Finset

variable {lam : List ℕ} {al : ℕ}

/-! ### Auxiliary facts on shapes -/

/-- Removing a box does not increase the number of rows. -/
lemma length_decrNth_le : ∀ (sh : List ℕ) (i : ℕ), (decrNth sh i).length ≤ sh.length
  | [], _ => by simp [decrNth]
  | 0 :: _, 0 => by simp [decrNth]
  | 1 :: _, 0 => by simp [decrNth]
  | (_ + 2) :: _, 0 => by simp [decrNth]
  | n :: v, i + 1 => by
    simp only [decrNth, List.length_cons, Nat.add_le_add_iff_right]
    exact length_decrNth_le v i

/-- The product of the hook lengths as a product over any large enough range of rows. -/
lemma hookProd_eq_prod_range {sh : List ℕ} {N : ℕ} (h : sh.length ≤ N) :
    hookProd sh = ∏ r ∈ Finset.range N, rowHookProd sh r := by
  rw [hookProd, ← Finset.prod_range_mul_prod_Ico _ h]
  refine (mul_right_eq_self₀.2 (Or.inl ?_)).symm
  refine Finset.prod_eq_one fun r hr => ?_
  rw [Finset.mem_Ico] at hr
  rw [rowHookProd, List.getD_eq_default _ _ hr.1]
  simp

/-! ### The diagram with a corner removed -/

/-- Away from the column of the removed corner, the conjugate is unchanged. -/
lemma getD_conjPart_decrNth_of_ne (hlam : IsPart lam) (hal : IsRemCorner lam al) {j : ℕ}
    (hj : j ≠ lam.getD al 0 - 1) :
    (conjPart (decrNth lam al)).getD j 0 = (conjPart lam).getD j 0 := by
  have hmu : IsPart (decrNth lam al) := isPart_decrNth hlam hal
  have hle1 : (conjPart (decrNth lam al)).getD j 0 ≤ (conjPart lam).getD j 0 := by
    rw [← getD_le_conjPart_iff hmu]
    exact le_trans (getD_decrNth_le lam al _)
      ((getD_le_conjPart_iff hlam ((conjPart lam).getD j 0) j).2 le_rfl)
  have hle2 : (conjPart lam).getD j 0 ≤ (conjPart (decrNth lam al)).getD j 0 := by
    rw [← getD_le_conjPart_iff hlam]
    have h2 : (decrNth lam al).getD ((conjPart (decrNth lam al)).getD j 0) 0 ≤ j :=
      (getD_le_conjPart_iff hmu ((conjPart (decrNth lam al)).getD j 0) j).2 le_rfl
    by_cases hi : (conjPart (decrNth lam al)).getD j 0 = al
    · rw [hi, getD_decrNth_self] at h2
      rw [hi]
      simp only [IsRemCorner] at hal
      omega
    · rwa [getD_decrNth_of_ne hlam hal (Ne.symm hi)] at h2
  omega

/-- At the column of the removed corner, the conjugate loses its last box. -/
lemma getD_conjPart_decrNth_self (hlam : IsPart lam) (hal : IsRemCorner lam al) :
    (conjPart (decrNth lam al)).getD (lam.getD al 0 - 1) 0 = al := by
  have hmu : IsPart (decrNth lam al) := isPart_decrNth hlam hal
  have hle1 : (conjPart (decrNth lam al)).getD (lam.getD al 0 - 1) 0 ≤ al := by
    rw [← getD_le_conjPart_iff hmu, getD_decrNth_self]
  have hle2 : al ≤ (conjPart (decrNth lam al)).getD (lam.getD al 0 - 1) 0 := by
    by_contra hcon
    have hi : (conjPart (decrNth lam al)).getD (lam.getD al 0 - 1) 0 ≠ al := by omega
    have h2 : (decrNth lam al).getD ((conjPart (decrNth lam al)).getD (lam.getD al 0 - 1) 0) 0
        ≤ lam.getD al 0 - 1 :=
      (getD_le_conjPart_iff hmu _ _).2 le_rfl
    rw [getD_decrNth_of_ne hlam hal (Ne.symm hi)] at h2
    have h3 : lam.getD al 0 ≤ lam.getD ((conjPart (decrNth lam al)).getD (lam.getD al 0 - 1) 0) 0 :=
      hlam.getD_antitone (by omega)
    simp only [IsRemCorner] at hal
    omega
  omega

/-- Away from the row and the column of the removed corner, the hook lengths are unchanged. -/
lemma hookLength_decrNth_of_ne (hlam : IsPart lam) (hal : IsRemCorner lam al) {i j : ℕ}
    (hi : i ≠ al) (hj : j ≠ lam.getD al 0 - 1) :
    hookLength (decrNth lam al) i j = hookLength lam i j := by
  simp only [hookLength, getD_decrNth_of_ne hlam hal (Ne.symm hi),
    getD_conjPart_decrNth_of_ne hlam hal hj]

/-- In the row of the removed corner, the hook lengths decrease by one. -/
lemma hookLength_decrNth_row (hlam : IsPart lam) (hal : IsRemCorner lam al) {j : ℕ}
    (hj : j < lam.getD al 0 - 1) :
    hookLength (decrNth lam al) al j + 1 = hookLength lam al j := by
  have hjlam : j < lam.getD al 0 := by omega
  have hconj : al < (conjPart lam).getD j 0 := lt_getD_conjPart hlam hjlam
  simp only [hookLength, getD_decrNth_self,
    getD_conjPart_decrNth_of_ne hlam hal (by omega : j ≠ lam.getD al 0 - 1)]
  omega

/-- In the column of the removed corner, the hook lengths decrease by one. -/
lemma hookLength_decrNth_col (hlam : IsPart lam) (hal : IsRemCorner lam al) {i : ℕ}
    (hi : i < al) :
    hookLength (decrNth lam al) i (lam.getD al 0 - 1) + 1
      = hookLength lam i (lam.getD al 0 - 1) := by
  have hcell : lam.getD al 0 - 1 < lam.getD i 0 := corner_lt_getD hlam hal (le_of_lt hi)
  simp only [hookLength, getD_decrNth_of_ne hlam hal (by omega : al ≠ i),
    getD_conjPart_decrNth_self hlam hal, getD_conjPart_corner hlam hal]
  omega

/-- **The hook lengths after removing a corner**: the product of the hook lengths of
`lam ∖ al`, times the hook lengths of `lam` in the row and in the column of the corner, is
the product of the hook lengths of `lam` times the corresponding hook lengths of `lam ∖ al`.
-/
theorem hookProd_decrNth_mul (hlam : IsPart lam) (hal : IsRemCorner lam al) :
    hookProd (decrNth lam al) *
        ((∏ i ∈ Finset.range al, hookLength lam i (lam.getD al 0 - 1)) *
          ∏ j ∈ Finset.range (lam.getD al 0 - 1), hookLength lam al j)
      = hookProd lam *
        ((∏ i ∈ Finset.range al, hookLength (decrNth lam al) i (lam.getD al 0 - 1)) *
          ∏ j ∈ Finset.range (lam.getD al 0 - 1), hookLength (decrNth lam al) al j) := by
  have hmu : IsPart (decrNth lam al) := isPart_decrNth hlam hal
  have hallt : al < lam.length := hal.lt_length
  have hlen : (decrNth lam al).length ≤ lam.length := length_decrNth_le lam al
  have hbe : lam.getD al 0 = (lam.getD al 0 - 1) + 1 := getD_corner hal
  -- the rows above the corner
  have hup : ∀ r ∈ Finset.range al,
      rowHookProd (decrNth lam al) r * hookLength lam r (lam.getD al 0 - 1)
        = rowHookProd lam r * hookLength (decrNth lam al) r (lam.getD al 0 - 1) := by
    intro r hr
    rw [Finset.mem_range] at hr
    have hcell : lam.getD al 0 - 1 < lam.getD r 0 := corner_lt_getD hlam hal (le_of_lt hr)
    have hmem : lam.getD al 0 - 1 ∈ Finset.range (lam.getD r 0) := Finset.mem_range.2 hcell
    have hrow : rowHookProd (decrNth lam al) r
        = ∏ c ∈ Finset.range (lam.getD r 0), hookLength (decrNth lam al) r c := by
      rw [rowHookProd, getD_decrNth_of_ne hlam hal (by omega : al ≠ r)]
    rw [hrow, rowHookProd, ← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem,
      Finset.prod_congr rfl (fun c hc => hookLength_decrNth_of_ne hlam hal (by omega : r ≠ al)
        (Finset.ne_of_mem_erase hc))]
    ring
  -- the row of the corner
  have hrowal : rowHookProd (decrNth lam al) al
      = ∏ j ∈ Finset.range (lam.getD al 0 - 1), hookLength (decrNth lam al) al j := by
    rw [rowHookProd, getD_decrNth_self]
  have hrowlam : rowHookProd lam al
      = ∏ j ∈ Finset.range (lam.getD al 0 - 1), hookLength lam al j := by
    have hcell : lam.getD al 0 - 1 < lam.getD al 0 := by omega
    have hone : hookLength lam al (lam.getD al 0 - 1) = 1 :=
      (hookLength_eq_one_iff hlam hcell).2 ⟨hal, rfl⟩
    rw [rowHookProd]
    nth_rewrite 1 [hbe]
    rw [Finset.prod_range_succ, hone, mul_one]
  -- the rows below the corner
  have hdown : ∀ r ∈ Finset.Ico (al + 1) lam.length,
      rowHookProd (decrNth lam al) r = rowHookProd lam r := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have hle : lam.getD r 0 ≤ lam.getD al 0 - 1 := by
      have h1 : lam.getD r 0 ≤ lam.getD (al + 1) 0 := hlam.getD_antitone hr.1
      simp only [IsRemCorner] at hal
      omega
    rw [rowHookProd, rowHookProd, getD_decrNth_of_ne hlam hal (by omega : al ≠ r)]
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    exact hookLength_decrNth_of_ne hlam hal (by omega : r ≠ al) (by omega)
  -- splitting the products over the rows
  have hsplit : ∀ f : ℕ → ℕ, ∏ r ∈ Finset.range lam.length, f r
      = ((∏ r ∈ Finset.range al, f r) * f al) * ∏ r ∈ Finset.Ico (al + 1) lam.length, f r := by
    intro f
    rw [Finset.range_eq_Ico, ← Finset.prod_Ico_consecutive f (Nat.zero_le al) (le_of_lt hallt),
      Finset.prod_eq_prod_Ico_succ_bot hallt f, ← Finset.range_eq_Ico]
    ring
  rw [hookProd_eq_prod_range hlen, hookProd, hsplit (rowHookProd (decrNth lam al)),
    hsplit (rowHookProd lam), hrowal, hrowlam,
    Finset.prod_congr rfl hdown]
  have hcols : (∏ r ∈ Finset.range al, rowHookProd (decrNth lam al) r) *
        ∏ i ∈ Finset.range al, hookLength lam i (lam.getD al 0 - 1)
      = (∏ r ∈ Finset.range al, rowHookProd lam r) *
        ∏ i ∈ Finset.range al, hookLength (decrNth lam al) i (lam.getD al 0 - 1) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hup
  calc ((∏ r ∈ Finset.range al, rowHookProd (decrNth lam al) r) *
          ∏ j ∈ Finset.range (lam.getD al 0 - 1), hookLength (decrNth lam al) al j) *
        (∏ r ∈ Finset.Ico (al + 1) lam.length, rowHookProd lam r) *
        ((∏ i ∈ Finset.range al, hookLength lam i (lam.getD al 0 - 1)) *
          ∏ j ∈ Finset.range (lam.getD al 0 - 1), hookLength lam al j)
      = ((∏ r ∈ Finset.range al, rowHookProd (decrNth lam al) r) *
            ∏ i ∈ Finset.range al, hookLength lam i (lam.getD al 0 - 1)) *
          ((∏ j ∈ Finset.range (lam.getD al 0 - 1), hookLength lam al j) *
            (∏ r ∈ Finset.Ico (al + 1) lam.length, rowHookProd lam r) *
            ∏ j ∈ Finset.range (lam.getD al 0 - 1), hookLength (decrNth lam al) al j) := by
        ring
    _ = ((∏ r ∈ Finset.range al, rowHookProd lam r) *
            ∏ i ∈ Finset.range al, hookLength (decrNth lam al) i (lam.getD al 0 - 1)) *
          ((∏ j ∈ Finset.range (lam.getD al 0 - 1), hookLength lam al j) *
            (∏ r ∈ Finset.Ico (al + 1) lam.length, rowHookProd lam r) *
            ∏ j ∈ Finset.range (lam.getD al 0 - 1), hookLength (decrNth lam al) al j) := by
        rw [hcols]
    _ = ((∏ r ∈ Finset.range al, rowHookProd lam r) *
            ∏ j ∈ Finset.range (lam.getD al 0 - 1), hookLength lam al j) *
          (∏ r ∈ Finset.Ico (al + 1) lam.length, rowHookProd lam r) *
          ((∏ i ∈ Finset.range al, hookLength (decrNth lam al) i (lam.getD al 0 - 1)) *
            ∏ j ∈ Finset.range (lam.getD al 0 - 1), hookLength (decrNth lam al) al j) := by
        ring

/-! ### The probability of ending at a given corner -/

/-- Starting from a uniformly chosen box, the hook walk ends at the corner of the row `al`
with probability `(∏ hook lengths of lam) / (|lam| * ∏ hook lengths of lam ∖ al)`. -/
lemma prod_one_add_gnwRow_mul (hlam : IsPart lam) (hal : IsRemCorner lam al) :
    (∏ i ∈ Finset.range al, (1 + gnwRow lam al i)) *
        ∏ i ∈ Finset.range al, (hookLength (decrNth lam al) i (lam.getD al 0 - 1) : ℚ)
      = ∏ i ∈ Finset.range al, (hookLength lam i (lam.getD al 0 - 1) : ℚ) := by
  have hmu : IsPart (decrNth lam al) := isPart_decrNth hlam hal
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hcell : lam.getD al 0 - 1 < (decrNth lam al).getD i 0 := by
    rw [getD_decrNth_of_ne hlam hal (by omega : al ≠ i)]
    exact corner_lt_getD hlam hal (le_of_lt hi)
  have hpos : 1 ≤ hookLength (decrNth lam al) i (lam.getD al 0 - 1) :=
    one_le_hookLength hmu hcell
  have hdec := hookLength_decrNth_col hlam hal hi
  have hposQ : (1 : ℚ) ≤ (hookLength (decrNth lam al) i (lam.getD al 0 - 1) : ℚ) := by
    exact_mod_cast hpos
  have hcast : (hookLength (decrNth lam al) i (lam.getD al 0 - 1) : ℚ) + 1
      = (hookLength lam i (lam.getD al 0 - 1) : ℚ) := by exact_mod_cast hdec
  rw [gnwRow, if_neg (by omega : ¬ i = al), ← hcast, add_sub_cancel_right]
  have hne : (hookLength (decrNth lam al) i (lam.getD al 0 - 1) : ℚ) ≠ 0 := by linarith
  field_simp

lemma prod_one_add_gnwCol_mul (hlam : IsPart lam) (hal : IsRemCorner lam al) :
    (∏ j ∈ Finset.range (lam.getD al 0 - 1), (1 + gnwCol lam al j)) *
        ∏ j ∈ Finset.range (lam.getD al 0 - 1), (hookLength (decrNth lam al) al j : ℚ)
      = ∏ j ∈ Finset.range (lam.getD al 0 - 1), (hookLength lam al j : ℚ) := by
  have hmu : IsPart (decrNth lam al) := isPart_decrNth hlam hal
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hcell : j < (decrNth lam al).getD al 0 := by
    rw [getD_decrNth_self]
    exact hj
  have hpos : 1 ≤ hookLength (decrNth lam al) al j := one_le_hookLength hmu hcell
  have hdec := hookLength_decrNth_row hlam hal hj
  have hposQ : (1 : ℚ) ≤ (hookLength (decrNth lam al) al j : ℚ) := by exact_mod_cast hpos
  have hcast : (hookLength (decrNth lam al) al j : ℚ) + 1 = (hookLength lam al j : ℚ) := by
    exact_mod_cast hdec
  rw [gnwCol, if_neg (by omega : ¬ j = lam.getD al 0 - 1), ← hcast, add_sub_cancel_right]
  have hne : (hookLength (decrNth lam al) al j : ℚ) ≠ 0 := by linarith
  field_simp

/-- Starting from a uniformly chosen box, the hook walk ends at the corner of the row `al`
with probability `(∏ hook lengths of lam) / (|lam| * ∏ hook lengths of lam ∖ al)`. -/
theorem sum_hookWalkProb_cells (hlam : IsPart lam) (hal : IsRemCorner lam al) :
    ∑ i ∈ Finset.range lam.length, ∑ j ∈ Finset.range (lam.getD i 0),
        hookWalkProb lam (al, lam.getD al 0 - 1) (i, j)
      = (hookProd lam : ℚ) / hookProd (decrNth lam al) := by
  have hmu : IsPart (decrNth lam al) := isPart_decrNth hlam hal
  have hallt : al < lam.length := hal.lt_length
  have hbe : lam.getD al 0 = (lam.getD al 0 - 1) + 1 := getD_corner hal
  -- only the boxes above and to the left of the corner contribute
  have hstep1 : ∑ i ∈ Finset.range lam.length, ∑ j ∈ Finset.range (lam.getD i 0),
        hookWalkProb lam (al, lam.getD al 0 - 1) (i, j)
      = ∑ i ∈ Finset.range (al + 1), ∑ j ∈ Finset.range (lam.getD i 0),
        hookWalkProb lam (al, lam.getD al 0 - 1) (i, j) := by
    refine (Finset.sum_subset (by
      intro i hi
      rw [Finset.mem_range] at hi ⊢
      omega) ?_).symm
    intro i hi hi'
    rw [Finset.mem_range] at hi hi'
    refine Finset.sum_eq_zero fun j _ => ?_
    exact hookWalkProb_eq_zero_of_not_le (by simp only; omega)
  have hstep2 : ∀ i ∈ Finset.range (al + 1), ∑ j ∈ Finset.range (lam.getD i 0),
        hookWalkProb lam (al, lam.getD al 0 - 1) (i, j)
      = ∑ j ∈ Finset.range (lam.getD al 0 - 1 + 1),
          gnwRow lam al i * gnwCol lam al j *
            (∏ i' ∈ Finset.Ioo i al, (1 + gnwRow lam al i')) *
            ∏ j' ∈ Finset.Ioo j (lam.getD al 0 - 1), (1 + gnwCol lam al j') := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hcell : lam.getD al 0 - 1 < lam.getD i 0 := corner_lt_getD hlam hal (by omega)
    rw [← Finset.sum_subset (s₁ := Finset.range (lam.getD al 0 - 1 + 1)) (by
      intro j hj
      rw [Finset.mem_range] at hj ⊢
      omega)]
    · exact Finset.sum_congr rfl fun j hj => hookWalkProb_corner hlam hal (by omega)
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
        gnwRow lam al i * ∏ i' ∈ Finset.Ioo i al, (1 + gnwRow lam al i')
      = ∏ i ∈ Finset.range al, (1 + gnwRow lam al i) := by
    rw [hIcc, sum_Icc_mul_prod_Ioo (gnwRow lam al) al al 0 (by omega), gnwRow_self,
      ← Finset.range_eq_Ico]
    ring
  have hprodcol : ∑ j ∈ Finset.range (lam.getD al 0 - 1 + 1),
        gnwCol lam al j * ∏ j' ∈ Finset.Ioo j (lam.getD al 0 - 1), (1 + gnwCol lam al j')
      = ∏ j ∈ Finset.range (lam.getD al 0 - 1), (1 + gnwCol lam al j) := by
    rw [hIcc, sum_Icc_mul_prod_Ioo (gnwCol lam al) (lam.getD al 0 - 1) (lam.getD al 0 - 1) 0
      (by omega), gnwCol_self, ← Finset.range_eq_Ico]
    ring
  have hfactor : ∑ i ∈ Finset.range (al + 1), ∑ j ∈ Finset.range (lam.getD al 0 - 1 + 1),
        gnwRow lam al i * gnwCol lam al j *
          (∏ i' ∈ Finset.Ioo i al, (1 + gnwRow lam al i')) *
          ∏ j' ∈ Finset.Ioo j (lam.getD al 0 - 1), (1 + gnwCol lam al j')
      = (∑ i ∈ Finset.range (al + 1),
            gnwRow lam al i * ∏ i' ∈ Finset.Ioo i al, (1 + gnwRow lam al i')) *
        ∑ j ∈ Finset.range (lam.getD al 0 - 1 + 1),
            gnwCol lam al j * ∏ j' ∈ Finset.Ioo j (lam.getD al 0 - 1), (1 + gnwCol lam al j') := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfactor, hprodrow, hprodcol]
  -- comparison with the products of the hook lengths
  have hmupos : (0 : ℚ) < hookProd (decrNth lam al) := by
    exact_mod_cast hookProd_pos hmu
  have hcolpos : (0 : ℚ) < ∏ i ∈ Finset.range al,
      (hookLength (decrNth lam al) i (lam.getD al 0 - 1) : ℚ) := by
    refine Finset.prod_pos fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hcell : lam.getD al 0 - 1 < (decrNth lam al).getD i 0 := by
      rw [getD_decrNth_of_ne hlam hal (by omega : al ≠ i)]
      exact corner_lt_getD hlam hal (le_of_lt hi)
    have := one_le_hookLength hmu hcell
    have : (1 : ℚ) ≤ (hookLength (decrNth lam al) i (lam.getD al 0 - 1) : ℚ) := by
      exact_mod_cast this
    linarith
  have hrowpos : (0 : ℚ) < ∏ j ∈ Finset.range (lam.getD al 0 - 1),
      (hookLength (decrNth lam al) al j : ℚ) := by
    refine Finset.prod_pos fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hcell : j < (decrNth lam al).getD al 0 := by
      rw [getD_decrNth_self]; exact hj
    have := one_le_hookLength hmu hcell
    have : (1 : ℚ) ≤ (hookLength (decrNth lam al) al j : ℚ) := by exact_mod_cast this
    linarith
  have hkey := hookProd_decrNth_mul hlam hal
  have hkeyQ : (hookProd (decrNth lam al) : ℚ) *
        ((∏ i ∈ Finset.range al, (hookLength lam i (lam.getD al 0 - 1) : ℚ)) *
          ∏ j ∈ Finset.range (lam.getD al 0 - 1), (hookLength lam al j : ℚ))
      = (hookProd lam : ℚ) *
        ((∏ i ∈ Finset.range al, (hookLength (decrNth lam al) i (lam.getD al 0 - 1) : ℚ)) *
          ∏ j ∈ Finset.range (lam.getD al 0 - 1), (hookLength (decrNth lam al) al j : ℚ)) := by
    exact_mod_cast hkey
  rw [eq_div_iff (by linarith)]
  have hrowmul := prod_one_add_gnwRow_mul hlam hal
  have hcolmul := prod_one_add_gnwCol_mul hlam hal
  have hfin : ((∏ i ∈ Finset.range al, (1 + gnwRow lam al i)) *
        ∏ j ∈ Finset.range (lam.getD al 0 - 1), (1 + gnwCol lam al j)) *
      (hookProd (decrNth lam al) : ℚ) *
      ((∏ i ∈ Finset.range al, (hookLength (decrNth lam al) i (lam.getD al 0 - 1) : ℚ)) *
        ∏ j ∈ Finset.range (lam.getD al 0 - 1), (hookLength (decrNth lam al) al j : ℚ))
      = (hookProd lam : ℚ) *
      ((∏ i ∈ Finset.range al, (hookLength (decrNth lam al) i (lam.getD al 0 - 1) : ℚ)) *
        ∏ j ∈ Finset.range (lam.getD al 0 - 1), (hookLength (decrNth lam al) al j : ℚ)) := by
    rw [← hkeyQ]
    calc ((∏ i ∈ Finset.range al, (1 + gnwRow lam al i)) *
          ∏ j ∈ Finset.range (lam.getD al 0 - 1), (1 + gnwCol lam al j)) *
        (hookProd (decrNth lam al) : ℚ) *
        ((∏ i ∈ Finset.range al, (hookLength (decrNth lam al) i (lam.getD al 0 - 1) : ℚ)) *
          ∏ j ∈ Finset.range (lam.getD al 0 - 1), (hookLength (decrNth lam al) al j : ℚ))
        = (hookProd (decrNth lam al) : ℚ) *
          (((∏ i ∈ Finset.range al, (1 + gnwRow lam al i)) *
              ∏ i ∈ Finset.range al, (hookLength (decrNth lam al) i (lam.getD al 0 - 1) : ℚ)) *
            ((∏ j ∈ Finset.range (lam.getD al 0 - 1), (1 + gnwCol lam al j)) *
              ∏ j ∈ Finset.range (lam.getD al 0 - 1),
                (hookLength (decrNth lam al) al j : ℚ))) := by ring
      _ = _ := by rw [hrowmul, hcolmul]
  have hposprod : (0 : ℚ) < (∏ i ∈ Finset.range al,
      (hookLength (decrNth lam al) i (lam.getD al 0 - 1) : ℚ)) *
      ∏ j ∈ Finset.range (lam.getD al 0 - 1), (hookLength (decrNth lam al) al j : ℚ) :=
    mul_pos hcolpos hrowpos
  exact mul_right_cancel₀ (ne_of_gt hposprod) hfin

/-! ### The Greene–Nijenhuis–Wilf identity and the hook length formula -/

/-- **The Greene–Nijenhuis–Wilf identity**: for a partition of `n`, the sum over the corners
of the ratios of the products of the hook lengths is `n`. -/
theorem sum_hookProd_div_hookProd_decrNth (hlam : IsPart lam) :
    ∑ r ∈ Finset.range lam.length,
        (if IsRemCorner lam r then (hookProd lam : ℚ) / hookProd (decrNth lam r) else 0)
      = lam.sum := by
  have hexp : ∀ r ∈ Finset.range lam.length,
      (if IsRemCorner lam r then (hookProd lam : ℚ) / hookProd (decrNth lam r) else 0)
        = ∑ i ∈ Finset.range lam.length, ∑ j ∈ Finset.range (lam.getD i 0),
            (if IsRemCorner lam r then
              hookWalkProb lam (r, lam.getD r 0 - 1) (i, j) else 0) := by
    intro r _
    by_cases hc : IsRemCorner lam r
    · simp only [if_pos hc]
      exact (sum_hookWalkProb_cells hlam hc).symm
    · simp [hc]
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  have hone : ∀ i ∈ Finset.range lam.length,
      ∑ r ∈ Finset.range lam.length, ∑ j ∈ Finset.range (lam.getD i 0),
        (if IsRemCorner lam r then hookWalkProb lam (r, lam.getD r 0 - 1) (i, j) else 0)
      = (lam.getD i 0 : ℚ) := by
    intro i _
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun j hj => sum_hookWalkProb_corners hlam
      (i := i) (j := j) (Finset.mem_range.1 hj)]
    simp
  rw [Finset.sum_congr rfl hone, ← Nat.cast_sum, ← sum_eq_sum_range_getD lam le_rfl]

private lemma numStdTab_mul_hookProd_aux :
    ∀ (n : ℕ) (lam : List ℕ), IsPart lam → lam.sum = n →
      numStdTab lam * hookProd lam = Nat.factorial n := by
  intro n
  induction n with
  | zero =>
    intro lam hlam hsum
    rw [hlam.eq_nil_of_sum_eq_zero hsum, numStdTab_nil, hookProd]
    simp
  | succ n ih =>
    intro lam hlam hsum
    have hbr := numStdTab_branching hlam hsum (le_refl lam.length)
    have hcast : (numStdTab lam : ℚ)
        = ∑ r ∈ Finset.range lam.length,
            (if IsRemCorner lam r then (numStdTab (decrNth lam r) : ℚ) else 0) := by
      rw [hbr]
      push_cast
      exact Finset.sum_congr rfl fun r _ => by by_cases hc : IsRemCorner lam r <;> simp [hc]
    have hterm : ∀ r ∈ Finset.range lam.length,
        (if IsRemCorner lam r then (numStdTab (decrNth lam r) : ℚ) else 0) * hookProd lam
          = (Nat.factorial n : ℚ) *
            (if IsRemCorner lam r then (hookProd lam : ℚ) / hookProd (decrNth lam r) else 0) := by
      intro r _
      by_cases hc : IsRemCorner lam r
      · rw [if_pos hc, if_pos hc]
        have hmu : IsPart (decrNth lam r) := isPart_decrNth hlam hc
        have hsum' : (decrNth lam r).sum = n := by rw [sum_decrNth hlam hc, hsum]; omega
        have hIH : (numStdTab (decrNth lam r) : ℚ) * hookProd (decrNth lam r)
            = (Nat.factorial n : ℚ) := by exact_mod_cast ih (decrNth lam r) hmu hsum'
        have hposQ : (0 : ℚ) < hookProd (decrNth lam r) := by
          exact_mod_cast hookProd_pos hmu
        rw [← hIH]
        field_simp
      · simp [hc]
    have key : (numStdTab lam : ℚ) * hookProd lam = (Nat.factorial (n + 1) : ℚ) := by
      rw [hcast, Finset.sum_mul, Finset.sum_congr rfl hterm, ← Finset.mul_sum,
        sum_hookProd_div_hookProd_decrNth hlam, hsum, Nat.factorial_succ]
      push_cast
      ring
    exact_mod_cast key

/-- **The hook length formula**, proved by the hook walk of Greene, Nijenhuis and Wilf: the
number of standard Young tableaux of shape a partition `lam` of `n`, multiplied by the
product of the hook lengths of the boxes of `lam`, is `n !`.

This is the theorem `List.numStdTab_mul_hookProd`, obtained here by a different route: the
proof by the hook walk replaces the Frobenius formula for the number of standard tableaux by
the Greene–Nijenhuis–Wilf identity `List.sum_hookProd_div_hookProd_decrNth`. -/
theorem numStdTab_mul_hookProd_hookWalk (hlam : IsPart lam) :
    numStdTab lam * hookProd lam = Nat.factorial lam.sum :=
  numStdTab_mul_hookProd_aux lam.sum lam hlam rfl

/-- The number of standard Young tableaux of a shape which is a partition is positive. -/
lemma numStdTab_pos_of_isPart (hlam : IsPart lam) : 0 < numStdTab lam := by
  rcases Nat.eq_zero_or_pos (numStdTab lam) with h | h
  · exfalso
    have := numStdTab_mul_hookProd_hookWalk hlam
    rw [h, zero_mul] at this
    exact absurd this.symm (Nat.factorial_pos lam.sum).ne'
  · exact h

/-- **The hook walk ends at a corner with the branching probability**: the walk started at a
uniformly chosen box of a partition `lam` of `n` ends at the corner of the row `al` with
probability `f^(lam ∖ al) / f^lam`, the ratio of the numbers of standard Young tableaux.
This is the statement which, by the branching rule, gives the hook length formula. -/
theorem sum_hookWalkProb_cells_div_sum (hlam : IsPart lam) (hal : IsRemCorner lam al) :
    (∑ i ∈ Finset.range lam.length, ∑ j ∈ Finset.range (lam.getD i 0),
        hookWalkProb lam (al, lam.getD al 0 - 1) (i, j)) / lam.sum
      = (numStdTab (decrNth lam al) : ℚ) / numStdTab lam := by
  have hmu : IsPart (decrNth lam al) := isPart_decrNth hlam hal
  have hallt : al < lam.length := hal.lt_length
  have hn : 0 < lam.sum := by
    have : 0 < lam.getD al 0 := by simp only [IsRemCorner] at hal; omega
    have hle : lam.getD al 0 ≤ lam.sum := getD_le_sum _ _
    omega
  have hsum : (decrNth lam al).sum = lam.sum - 1 := sum_decrNth hlam hal
  have hlamf := numStdTab_mul_hookProd_hookWalk hlam
  have hmuf := numStdTab_mul_hookProd_hookWalk hmu
  rw [hsum] at hmuf
  have hnum : (0 : ℚ) < numStdTab lam := by exact_mod_cast numStdTab_pos_of_isPart hlam
  have hnumu : (0 : ℚ) < numStdTab (decrNth lam al) := by
    exact_mod_cast numStdTab_pos_of_isPart hmu
  have hprod : (0 : ℚ) < hookProd lam := by exact_mod_cast hookProd_pos hlam
  have hprodmu : (0 : ℚ) < hookProd (decrNth lam al) := by exact_mod_cast hookProd_pos hmu
  have hfac : (Nat.factorial lam.sum : ℚ) = lam.sum * Nat.factorial (lam.sum - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, lam.sum = m + 1 := ⟨lam.sum - 1, by omega⟩
    rw [hm]
    simp [Nat.factorial_succ]
  have h1 : (numStdTab lam : ℚ) * hookProd lam = (Nat.factorial lam.sum : ℚ) := by
    exact_mod_cast hlamf
  have h2 : (numStdTab (decrNth lam al) : ℚ) * hookProd (decrNth lam al)
      = (Nat.factorial (lam.sum - 1) : ℚ) := by exact_mod_cast hmuf
  rw [sum_hookWalkProb_cells hlam hal, div_div, div_eq_div_iff (by positivity) (by positivity)]
  have hnQ : (0 : ℚ) < lam.sum := by exact_mod_cast hn
  field_simp at h1 h2 ⊢
  nlinarith [h1, h2, hfac, hprodmu, hprod, hnumu, hnum]

end List
