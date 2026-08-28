/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.MvPolynomial.Symmetric.Alternant.Bialternant

/-!
# The alternant as a determinant, and the Vandermonde product

The alternant `alt m R a` is the determinant of the matrix `(X i ^ a j)`.  For the
staircase exponent vector `delta = (m-1, ..., 1, 0)` this determinant is the Vandermonde
product `∏_{i < j} (X i - X j)`, which turns Jacobi's bialternant formula into the
classical statement `s_lam = a_{lam + delta} / a_delta`.

## Main results

* `MvPolynomial.alt_eq_det` : the alternant is a determinant.
* `MvPolynomial.alt_staircase` : the alternant of the staircase is the Vandermonde product.
* `MvPolynomial.alt_partVec_eq_schurPoly_mul_vandermonde` : the bialternant formula, with the
  Vandermonde product made explicit.
-/

open List

namespace MvPolynomial

open MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-- The alternant of an exponent vector is the determinant of the matrix `(X i ^ a j)`. -/
theorem alt_eq_det (a : Fin m → ℕ) :
    alt m R a = (Matrix.of fun i j : Fin m => (X i : MvPolynomial (Fin m) R) ^ a j).det := by
  rw [Matrix.det_apply', alt]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [zsmul_eq_mul]
  rfl

/-- The exponent vector attached to the empty partition is the staircase. -/
lemma partVec_nil (i : Fin m) : partVec m [] i = m - 1 - (i : ℕ) := by
  simp [partVec]

/-- **The Vandermonde determinant**: the alternant of the staircase exponent vector is the
product `∏_{i < j} (X i - X j)`. -/
theorem alt_staircase (m : ℕ) (R : Type*) [CommRing R] :
    alt m R (partVec m [])
      = ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (X i - X j : MvPolynomial (Fin m) R) := by
  classical
  rw [alt_eq_det]
  have hsub : (Matrix.of fun i j : Fin m => (X i : MvPolynomial (Fin m) R) ^ partVec m [] j)
      = (Matrix.vandermonde (fun i : Fin m => (X i.rev : MvPolynomial (Fin m) R))).submatrix
          ⇑Fin.revPerm ⇑Fin.revPerm := by
    ext i j
    have hj : ((j.rev : Fin m) : ℕ) = m - 1 - (j : ℕ) := by
      rw [Fin.val_rev]
      omega
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply, Fin.rev_rev,
      partVec_nil, hj, Fin.revPerm_apply]
  rw [hsub, Matrix.det_submatrix_equiv_self Fin.revPerm, Matrix.det_vandermonde]
  rw [Finset.prod_sigma' Finset.univ (fun i : Fin m => Finset.Ioi i)
      (fun i j => (X j.rev - X i.rev : MvPolynomial (Fin m) R)),
    Finset.prod_sigma' Finset.univ (fun i : Fin m => Finset.Ioi i)
      (fun i j => (X i - X j : MvPolynomial (Fin m) R))]
  refine Finset.prod_nbij' (fun p => ⟨p.2.rev, p.1.rev⟩) (fun p => ⟨p.2.rev, p.1.rev⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] at hij ⊢
    exact Fin.rev_lt_rev.2 hij
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] at hij ⊢
    exact Fin.rev_lt_rev.2 hij
  · rintro ⟨i, j⟩ -
    simp
  · rintro ⟨i, j⟩ -
    simp
  · rintro ⟨i, j⟩ -
    simp

/-- **Jacobi's bialternant formula**: `s_lam` is the quotient of the alternant of
`lam + delta` by the Vandermonde product. -/
theorem alt_partVec_eq_schurPoly_mul_vandermonde {lam : List ℕ} (hlam : IsPart lam)
    (hlen : lam.length ≤ m) :
    alt m R (partVec m lam)
      = schurPoly (Fin m) R lam
          * ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (X i - X j : MvPolynomial (Fin m) R) := by
  rw [alt_partVec_eq_schurPoly_mul hlam hlen, alt_staircase]

end MvPolynomial
