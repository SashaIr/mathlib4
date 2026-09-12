/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.LinearAlgebra.Vandermonde

/-!
# A shift identity for the Vandermonde product

This file proves the arithmetic identity underlying the branching rule for the number of
standard Young tableaux, and hence the hook length formula.

For a family `x : Fin k → ℤ` write `V(x) = ∏_{i < j} (x j - x i)` for the Vandermonde
product and `x⁽ⁱ⁾` for the family `x` with its `i`-th entry decreased by one.  Then

`∑ i, x i * V(x⁽ⁱ⁾) = (∑ i, x i - C(k, 2)) * V(x)`.

The proof writes `V(x)` as the determinant of the matrix of falling factorials
`fallMat x i j = x_i (x_i - 1) ⋯ (x_i - j + 1)`; the point of that basis is the identity
`x · (x - 1)_j = (x)_{j+1}`, which turns `x i * V(x⁽ⁱ⁾)` into the determinant of `fallMat x`
with its `i`-th row shifted by one column.  Since `(x)_{j+1} = (x)_j · (x - j)`, that row is
`x i • (fallMat x) i - (j ↦ j · (fallMat x) i j)`, and the two resulting sums over `i` are
computed by multilinearity and by a Leibniz expansion respectively.

## Main definitions

* `Young.vdmProd` : the Vandermonde product `∏_{i < j} (x j - x i)`.
* `Young.fallMat` : the matrix of falling factorials of a family of integers.

## Main results

* `Young.det_fallMat` : the determinant of the falling factorial matrix is `vdmProd`.
* `Young.sum_mul_vdmProd_update` : the shift identity displayed above.
-/

@[expose] public section

namespace Young

open List

open Finset Matrix Polynomial

variable {k : ℕ}

/-! ### The Vandermonde product and the falling factorial matrix -/

/-- The Vandermonde product `∏_{i < j} (x j - x i)` of a family of integers. -/
def vdmProd (x : Fin k → ℤ) : ℤ := ∏ i, ∏ j ∈ Finset.Ioi i, (x j - x i)

/-- The matrix whose `(i, j)` entry is the falling factorial
`x_i (x_i - 1) ⋯ (x_i - j + 1)`. -/
noncomputable def fallMat (x : Fin k → ℤ) : Matrix (Fin k) (Fin k) ℤ :=
  Matrix.of fun i j => Polynomial.eval (x i) (descPochhammer ℤ (j : ℕ))

/-- The entries of the falling factorial matrix. -/
lemma fallMat_apply (x : Fin k → ℤ) (i j : Fin k) :
    fallMat x i j = Polynomial.eval (x i) (descPochhammer ℤ (j : ℕ)) := rfl

/-- The determinant of the falling factorial matrix is the Vandermonde product. -/
theorem det_fallMat (x : Fin k → ℤ) : (fallMat x).det = vdmProd x :=
  (Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde x
      (fun j => descPochhammer ℤ (j : ℕ)) (fun i => descPochhammer_natDegree ℤ i)
      (fun i => monic_descPochhammer ℤ i)).symm.trans (Matrix.det_vandermonde x)

/-- Changing one entry of the family changes one row of the falling factorial matrix. -/
lemma fallMat_update (x : Fin k → ℤ) (i : Fin k) (a : ℤ) :
    fallMat (Function.update x i a)
      = (fallMat x).updateRow i fun j => Polynomial.eval a (descPochhammer ℤ (j : ℕ)) := by
  ext p j
  rcases eq_or_ne p i with rfl | h
  · simp [fallMat]
  · simp [fallMat, Matrix.updateRow_ne h, Function.update_of_ne h]

/-! ### The falling factorials -/

/-- The recursion `x · (x - 1)_j = (x)_{j+1}` for falling factorials. -/
lemma mul_eval_descPochhammer_sub_one (a : ℤ) (j : ℕ) :
    a * Polynomial.eval (a - 1) (descPochhammer ℤ j)
      = Polynomial.eval a (descPochhammer ℤ (j + 1)) := by
  rw [descPochhammer_succ_left]
  simp [Polynomial.eval_comp]

/-- The recursion `(x)_{j+1} = (x)_j · (x - j)` for falling factorials. -/
lemma eval_descPochhammer_succ (a : ℤ) (j : ℕ) :
    Polynomial.eval a (descPochhammer ℤ (j + 1))
      = Polynomial.eval a (descPochhammer ℤ j) * (a - j) := by
  rw [descPochhammer_succ_right]
  simp

/-! ### Two determinant sums -/

/-- Scaling the entries of one row of a matrix column by column, and summing the resulting
determinants over the rows, multiplies the determinant by the sum of the scalars. -/
lemma sum_det_updateRow_mul_row (A : Matrix (Fin k) (Fin k) ℤ) (d : Fin k → ℤ) :
    ∑ i, (A.updateRow i fun j => d j * A i j).det = (∑ j, d j) * A.det := by
  classical
  have key : ∀ i : Fin k, (A.updateRow i fun j => d j * A i j).det
      = ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • (d (σ.symm i) * ∏ p, A (σ p) p) := by
    intro i
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    have hq : σ (σ.symm i) = i := σ.apply_symm_apply i
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (σ.symm i)),
      ← Finset.mul_prod_erase _ (fun p => A (σ p) p) (Finset.mem_univ (σ.symm i)),
      ← mul_assoc]
    congr 1
    · rw [hq, Matrix.updateRow_self]
    · refine Finset.prod_congr rfl fun p hp => ?_
      have hp' : p ≠ σ.symm i := (Finset.mem_erase.1 hp).1
      have hne : σ p ≠ i := fun h => hp' (by rw [← h, σ.symm_apply_apply])
      rw [Matrix.updateRow_ne hne]
  simp_rw [key]
  rw [Finset.sum_comm, Matrix.det_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.smul_sum, ← Finset.sum_mul, Equiv.sum_comp σ.symm d, mul_smul_comm]

/-- Replacing one row of a matrix by itself scaled by a constant, and summing the resulting
determinants over the rows, multiplies the determinant by the sum of the scalars. -/
lemma sum_det_updateRow_smul_self (A : Matrix (Fin k) (Fin k) ℤ) (c : Fin k → ℤ) :
    ∑ i, (A.updateRow i fun j => c i * A i j).det = (∑ i, c i) * A.det := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsmul : (fun j => c i * A i j) = c i • A i := by ext j; simp
  rw [hsmul, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]

/-- The sum of the first `k` natural numbers. -/
lemma sum_range_id_eq_choose_two (k : ℕ) : ∑ j ∈ Finset.range k, j = k.choose 2 := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ' n 1
    rw [Finset.sum_range_succ, ih, h, Nat.choose_one_right]
    omega

/-! ### The shift identity -/

/-- **The shift identity for the Vandermonde product**: decreasing the `i`-th entry of `x`
by one, weighting by `x i` and summing over `i` multiplies the Vandermonde product by
`∑ i, x i - C(k, 2)`.  This is the arithmetic content of the branching rule for the number
of standard Young tableaux. -/
theorem sum_mul_vdmProd_update (x : Fin k → ℤ) :
    ∑ i, x i * vdmProd (Function.update x i (x i - 1))
      = ((∑ i, x i) - (k.choose 2 : ℤ)) * vdmProd x := by
  classical
  set A := fallMat x with hA
  have hrow : ∀ i : Fin k, x i * vdmProd (Function.update x i (x i - 1))
      = (A.updateRow i fun j => x i * A i j).det
        + (A.updateRow i fun j => -(j : ℤ) * A i j).det := by
    intro i
    rw [← det_fallMat, fallMat_update, ← Matrix.det_updateRow_smul]
    have hfun : (x i • fun j : Fin k =>
        Polynomial.eval (x i - 1) (descPochhammer ℤ (j : ℕ)))
        = (fun j : Fin k => x i * A i j) + (fun j : Fin k => -(j : ℤ) * A i j) := by
      ext j
      have h1 : x i * Polynomial.eval (x i - 1) (descPochhammer ℤ (j : ℕ))
          = Polynomial.eval (x i) (descPochhammer ℤ ((j : ℕ) + 1)) :=
        mul_eval_descPochhammer_sub_one _ _
      rw [Pi.smul_apply, smul_eq_mul, h1, eval_descPochhammer_succ]
      simp only [hA, fallMat_apply, Pi.add_apply]
      ring
    rw [hfun, Matrix.det_updateRow_add]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, sum_det_updateRow_smul_self,
    sum_det_updateRow_mul_row A (fun j => -(j : ℤ)), det_fallMat]
  have hsum : ∑ j : Fin k, (-(j : ℤ)) = -(k.choose 2 : ℤ) := by
    have h : ∑ j : Fin k, ((j : ℕ) : ℤ) = (k.choose 2 : ℤ) := by
      calc ∑ j : Fin k, ((j : ℕ) : ℤ) = ((∑ j ∈ Finset.range k, j : ℕ) : ℤ) := by
            rw [Nat.cast_sum, Fin.sum_univ_eq_sum_range (fun j => ((j : ℕ) : ℤ))]
        _ = (k.choose 2 : ℤ) := by rw [sum_range_id_eq_choose_two]
    simp only [← h, Finset.sum_neg_distrib]
  rw [hsum, sub_mul, neg_mul]
  ring

end Young
