/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Alternant.Vandermonde

/-!
# Antisymmetric polynomials

A Lean 4 port of the predicate part of `theories/MPoly/antisym.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

A polynomial is *antisymmetric* when permuting its variables multiplies it by the sign of
the permutation.  The alternants `alt m R a` are antisymmetric, and in particular so is
the Vandermonde product; multiplying an antisymmetric polynomial by a symmetric one gives
an antisymmetric polynomial, and over an integral domain this characterises the symmetric
polynomials.

## Main definitions

* `MvPolynomial.IsAntisym p` : the polynomial `p` is antisymmetric (Coq `antisym`).

## Main results

* `MvPolynomial.isAntisym_alt` : the alternants are antisymmetric (Coq `alt_anti`).
* `MvPolynomial.isAntisym_vandermonde` : the Vandermonde product is antisymmetric
  (Coq `Vanprod_anti`).
* `MvPolynomial.IsAntisym.mul_of_isSymmetric` : a symmetric polynomial times an antisymmetric one
  is antisymmetric (Coq `sym_anti`).
* `MvPolynomial.isSymmetric_iff_isAntisym_mul` : over an integral domain, multiplication by a
  nonzero antisymmetric polynomial identifies the symmetric polynomials with the
  antisymmetric ones (Coq `sym_antiE`), and `MvPolynomial.isSymmetric_iff_isAntisym_vandermonde_mul`
  is the case of the Vandermonde product.
-/

@[expose] public section

namespace MvPolynomial

open MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-- A polynomial is antisymmetric when permuting its variables multiplies it by the sign
of the permutation (Coq `antisym`). -/
def IsAntisym (p : MvPolynomial (Fin m) R) : Prop :=
  ∀ σ : Equiv.Perm (Fin m), rename σ p = (Equiv.Perm.sign σ : ℤ) • p

lemma isAntisym_zero : IsAntisym (0 : MvPolynomial (Fin m) R) := by
  intro σ
  simp

lemma IsAntisym.add {p q : MvPolynomial (Fin m) R} (hp : IsAntisym p) (hq : IsAntisym q) :
    IsAntisym (p + q) := by
  intro σ
  rw [map_add, hp σ, hq σ, smul_add]

lemma IsAntisym.neg {p : MvPolynomial (Fin m) R} (hp : IsAntisym p) : IsAntisym (-p) := by
  intro σ
  rw [map_neg, hp σ, smul_neg]

lemma IsAntisym.smul {p : MvPolynomial (Fin m) R} (hp : IsAntisym p) (c : R) :
    IsAntisym (c • p) := by
  intro σ
  rw [map_smul, hp σ, smul_comm]

/-- Coq `alt_anti`: the alternants are antisymmetric. -/
theorem isAntisym_alt (a : Fin m → ℕ) : IsAntisym (alt m R a) := by
  intro σ
  rw [alt, map_sum, Finset.smul_sum]
  refine Fintype.sum_bijective (fun w ↦ σ * w) (Group.mulLeft_bijective _) _ _ fun w ↦ ?_
  rw [map_zsmul, smul_smul, map_prod]
  congr 1
  · have hs : ((Equiv.Perm.sign σ : ℤ)) ^ 2 = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    push_cast [Equiv.Perm.sign_mul]
    rw [show ((Equiv.Perm.sign σ : ℤ)) * (((Equiv.Perm.sign σ : ℤ)) *
      ((Equiv.Perm.sign w : ℤ))) = ((Equiv.Perm.sign σ : ℤ)) ^ 2 *
      ((Equiv.Perm.sign w : ℤ)) by ring, hs, one_mul]
  · exact Finset.prod_congr rfl fun i _ ↦ by rw [map_pow, rename_X]; rfl

/-- Coq `Vanprod_anti`: the Vandermonde product is antisymmetric. -/
theorem isAntisym_vandermonde (m : ℕ) (R : Type*) [CommRing R] :
    IsAntisym (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (X i - X j : MvPolynomial (Fin m) R)) := by
  rw [← alt_staircase m R]
  exact isAntisym_alt _

/-- Coq `sym_anti`: a symmetric polynomial times an antisymmetric one is antisymmetric. -/
theorem IsAntisym.mul_of_isSymmetric {p q : MvPolynomial (Fin m) R} (hp : IsAntisym p)
    (hq : q.IsSymmetric) : IsAntisym (p * q) := by
  intro σ
  rw [map_mul, hp σ, hq σ, smul_mul_assoc]

/-- Coq `sym_antiE`: over an integral domain, a polynomial `q` is symmetric if and only if
its product with a fixed nonzero antisymmetric polynomial is antisymmetric. -/
theorem isSymmetric_iff_isAntisym_mul {A : Type*} [CommRing A] [IsDomain A]
    {p : MvPolynomial (Fin m) A} (hp : IsAntisym p) (hp0 : p ≠ 0)
    (q : MvPolynomial (Fin m) A) : q.IsSymmetric ↔ IsAntisym (p * q) := by
  refine ⟨fun hq ↦ hp.mul_of_isSymmetric hq, fun h σ ↦ ?_⟩
  have h1 : rename σ (p * q) = (Equiv.Perm.sign σ : ℤ) • (p * q) := h σ
  rw [map_mul, hp σ, smul_mul_assoc] at h1
  have hmul : p * rename σ q = p * q := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs] at h1 <;>
      simpa using h1
  exact mul_left_cancel₀ hp0 hmul

/-- The Vandermonde product is nonzero over a nontrivial commutative ring without zero
divisors (Coq `Vanprod_neq0`). -/
theorem vandermonde_ne_zero (m : ℕ) (A : Type*) [CommRing A] [IsDomain A] :
    (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (X i - X j : MvPolynomial (Fin m) A)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ ↦ Finset.prod_ne_zero_iff.2 fun j hj ↦ ?_
  have hij : i ≠ j := (Finset.mem_Ioi.1 hj).ne
  intro hzero
  have hcoeff : (X i - X j : MvPolynomial (Fin m) A).coeff (Finsupp.single i 1) = 1 := by
    have h2 : (X j : MvPolynomial (Fin m) A).coeff (Finsupp.single i 1) = 0 := by
      rw [coeff_X]
      exact ite_eq_right fun h ↦ hij (Finsupp.single_left_injective one_ne_zero h).symm
    rw [coeff_sub, coeff_X, ite_eq_left rfl, h2, sub_zero]
  rw [hzero] at hcoeff
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoeff
  exact zero_ne_one hcoeff

/-- Over an integral domain, a polynomial is symmetric if and only if its product with the
Vandermonde product is antisymmetric. -/
theorem isSymmetric_iff_isAntisym_vandermonde_mul {A : Type*} [CommRing A] [IsDomain A]
    (q : MvPolynomial (Fin m) A) :
    q.IsSymmetric ↔
      IsAntisym ((∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (X i - X j : MvPolynomial (Fin m) A)) * q) :=
  isSymmetric_iff_isAntisym_mul (isAntisym_vandermonde m A) (vandermonde_ne_zero m A) q

end MvPolynomial
