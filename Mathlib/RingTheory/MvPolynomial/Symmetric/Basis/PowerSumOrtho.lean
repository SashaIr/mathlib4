/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Cauchy.Matrix
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Cauchy.PowerSum

/-!
# Orthogonality of the power sums

Following `theories/MPoly/homogsym.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove that the products of power
sums are orthogonal for the Hall scalar product, with `⟨p_μ, p_μ⟩ = z_μ`.

## Main results

* `MvPolynomial.hallInner_pSub` : `⟨p_μ, p_ν⟩ = z_μ` if `μ = ν` and `0` otherwise.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {m n : ℕ} {R : Type*}

/-! ### Preliminaries -/

/-- The base change of a power sum. -/
lemma map_psum {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : ℕ) :
    MvPolynomial.map f (psum (Fin m) R r) = psum (Fin m) S r := by
  simp [psum, map_sum]

/-- The base change of a product of power sums. -/
lemma map_pProd {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (μ : List ℕ) :
    MvPolynomial.map f (pProd m R μ) = pProd m S μ := by
  induction μ with
  | nil => simp [pProd]
  | cons a l ih => rw [pProd_cons, pProd_cons, map_mul, ih, map_psum]

/-! ### The duality criterion -/

/-- If two families satisfy the Cauchy identity, then they are dual bases for the Hall
scalar product. -/
theorem hallInner_eq_of_cauchy [CommRing R] (u v : PartLengthLe n m → symHomogeneousSubmodule m n R)
    (h : cauchyKernelSum m n R u v = cauchyKernelSum m n R (schurSub m n R) (schurSub m n R))
    (μ ν : PartLengthLe n m) :
    hallInner m n R (u μ) (v ν) = if μ = ν then 1 else 0 := by
  have hmat := transpose_mul_eq_of_cauchyKernelSum_eq h
  rw [schurReprMat_schurSub, Matrix.transpose_one, Matrix.one_mul] at hmat
  have h2 : (schurReprMat m n R v).transpose * schurReprMat m n R u = 1 := by
    have hc := congrArg Matrix.transpose hmat
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at hc
  rw [hallInner_eq_matrix, mul_eq_one_comm.2 h2]
  by_cases hlm : μ = ν
  · rw [ite_eq_left hlm, hlm, Matrix.one_apply_eq]
  · rw [ite_eq_right hlm, Matrix.one_apply_ne hlm]

/-! ### A family with a dual family is a basis -/

/-- The matrix identity behind duality: the coordinate matrices of two dual families in the
Schur basis are inverse to each other. -/
lemma mul_transpose_eq_one_of_hallInner_dual [CommRing R]
    (u v : PartLengthLe n m → symHomogeneousSubmodule m n R)
    (h : ∀ μ ν, hallInner m n R (u μ) (v ν) = if μ = ν then 1 else 0) :
    schurReprMat m n R u * (schurReprMat m n R v).transpose = 1 := by
  classical
  ext μ ν
  rw [← hallInner_eq_matrix, h μ ν]
  by_cases hc : μ = ν
  · rw [ite_eq_left hc, hc, Matrix.one_apply_eq]
  · rw [ite_eq_right hc, Matrix.one_apply_ne hc]

/-- The expansion of an element in a family admitting a dual family. -/
lemma eq_sum_hallInner_smul_of_dual [CommRing R]
    (u v : PartLengthLe n m → symHomogeneousSubmodule m n R)
    (h : ∀ μ ν, hallInner m n R (u μ) (v ν) = if μ = ν then 1 else 0)
    (f : symHomogeneousSubmodule m n R) :
    f = ∑ μ : PartLengthLe n m, hallInner m n R f (v μ) • u μ := by
  classical
  set A := schurReprMat m n R u with hAdef
  set B := schurReprMat m n R v with hBdef
  have hBA : B.transpose * A = 1 :=
    mul_eq_one_comm.2 (mul_transpose_eq_one_of_hallInner_dual u v h)
  refine (schurBasis m n R).repr.injective (Finsupp.ext fun ρ => ?_)
  rw [map_sum]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, map_smul, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ μ : PartLengthLe n m,
      hallInner m n R f (v μ) * (schurBasis m n R).repr (u μ) ρ
        = ∑ κ : PartLengthLe n m,
            (schurBasis m n R).repr f κ * (B.transpose κ μ * A μ ρ) := by
    intro μ
    rw [hallInner_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun κ _ => by
      simp only [hAdef, hBdef, Matrix.transpose_apply, schurReprMat_apply]
      ring
  rw [Finset.sum_congr rfl fun μ _ => hterm μ, Finset.sum_comm]
  have hfin : ∀ κ : PartLengthLe n m,
      ∑ μ : PartLengthLe n m,
          (schurBasis m n R).repr f κ * (B.transpose κ μ * A μ ρ)
        = (schurBasis m n R).repr f κ
          * (1 : Matrix (PartLengthLe n m) (PartLengthLe n m) R) κ ρ := by
    intro κ
    rw [← Finset.mul_sum, ← hBA, Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun κ _ => hfin κ]
  rw [Finset.sum_eq_single ρ]
  · rw [Matrix.one_apply_eq, mul_one]
  · intro κ _ hne
    rw [Matrix.one_apply_ne hne, mul_zero]
  · intro hc
    exact absurd (Finset.mem_univ ρ) hc

/-- A family admitting a dual family for the Hall scalar product is linearly independent. -/
lemma linearIndependent_of_hallInner_dual [CommRing R]
    (u v : PartLengthLe n m → symHomogeneousSubmodule m n R)
    (h : ∀ μ ν, hallInner m n R (u μ) (v ν) = if μ = ν then 1 else 0) :
    LinearIndependent R u := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg ν
  have := congrArg (fun x => hallInner m n R x (v ν)) hg
  simp only [map_sum, map_smul, LinearMap.coe_sum, LinearMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, map_zero, LinearMap.zero_apply] at this
  rw [Finset.sum_congr rfl fun μ _ => by rw [h μ ν]] at this
  simpa using this

/-- **A family admitting a dual family for the Hall scalar product is a basis**. -/
noncomputable def basisOfHallInnerDual [CommRing R]
    (u v : PartLengthLe n m → symHomogeneousSubmodule m n R)
    (h : ∀ μ ν, hallInner m n R (u μ) (v ν) = if μ = ν then 1 else 0) :
    Module.Basis (PartLengthLe n m) R (symHomogeneousSubmodule m n R) :=
  Module.Basis.mk (linearIndependent_of_hallInner_dual u v h)
    (fun f _ => by
      rw [eq_sum_hallInner_smul_of_dual u v h f]
      exact Submodule.sum_mem _ fun μ _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, rfl⟩))

@[simp] lemma basisOfHallInnerDual_apply [CommRing R]
    (u v : PartLengthLe n m → symHomogeneousSubmodule m n R)
    (h : ∀ μ ν, hallInner m n R (u μ) (v ν) = if μ = ν then 1 else 0)
    (μ : PartLengthLe n m) : basisOfHallInnerDual u v h μ = u μ := by
  rw [basisOfHallInnerDual, Module.Basis.mk_apply]

/-! ### Orthogonality of the power sums -/

/-- **The power sums are orthogonal** for the Hall scalar product, with
`⟨p_μ, p_μ⟩ = z_μ`. -/
theorem hallInner_pSub [CommRing R] [Algebra ℚ R] (hnm : n ≤ m) (μ ν : PartLengthLe n m) :
    hallInner m n R (pSub m n R μ) (pSub m n R ν)
      = if μ = ν then (zcard μ.1 : R) else 0 := by
  classical
  set zinv : PartLengthLe n m → R := fun l => algebraMap ℚ R ((zcard l.1 : ℚ))⁻¹ with hzinv
  have hzmul : ∀ l : PartLengthLe n m, (zcard l.1 : R) * zinv l = 1 := by
    intro l
    have hz : (zcard l.1 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (zcard_pos l.2.1).ne'
    rw [hzinv]
    simp only
    rw [← map_natCast (algebraMap ℚ R) (zcard l.1), ← map_mul, mul_inv_cancel₀ hz, map_one]
  have hcauchy : ∑ l : PartLengthLe n m,
      C ((pSub m n R l : MvPolynomial (Fin m) R))
        * MvPolynomial.map (C : R →+* MvPolynomial (Fin m) R)
            (((zinv l • pSub m n R l : symHomogeneousSubmodule m n R) :
              MvPolynomial (Fin m) R))
      = ∑ l : PartLengthLe n m,
          C (schurPoly (Fin m) R l.1)
            * MvPolynomial.map (C : R →+* MvPolynomial (Fin m) R) (schurPoly (Fin m) R l.1) := by
    have hpc := power_sum_cauchy m m n R
    rw [sum_partFinset_eq_sum_partLengthLe (m := m) hnm,
      sum_partFinset_eq_sum_partLengthLe (m := m) hnm] at hpc
    have hrhs : (∑ l : PartLengthLe n m, C (schurPoly (Fin m) R l.1)
          * MvPolynomial.map (C : R →+* MvPolynomial (Fin m) R) (schurPoly (Fin m) R l.1))
        = ∑ l : PartLengthLe n m, C (schurPoly (Fin m) R l.1)
            * schurPoly (Fin m) (MvPolynomial (Fin m) R) l.1 :=
      Finset.sum_congr rfl fun l _ => by rw [map_schurPoly]
    rw [hrhs, hpc]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← map_pProd (C : R →+* MvPolynomial (Fin m) R) l.1, coe_pSub, SetLike.val_smul,
      coe_pSub, map_C_smul, mul_smul_comm, hzinv]
    exact algebraMap_smul _ _ _
  have hkey := hallInner_eq_of_cauchy (pSub m n R) (fun l => zinv l • pSub m n R l) hcauchy μ ν
  rw [map_smul, smul_eq_mul] at hkey
  by_cases hlm : μ = ν
  · subst hlm
    rw [ite_eq_left rfl] at hkey ⊢
    have := congrArg (fun x => (zcard μ.1 : R) * x) hkey
    simpa [← mul_assoc, hzmul μ] using this
  · rw [ite_eq_right hlm] at hkey ⊢
    have := congrArg (fun x => (zcard ν.1 : R) * x) hkey
    simpa [← mul_assoc, hzmul ν] using this

/-- The family dual to the power sums: `p_μ / z_μ`. -/
noncomputable def pSubInvZ (m n : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R]
    (μ : PartLengthLe n m) : symHomogeneousSubmodule m n R :=
  algebraMap ℚ R ((zcard μ.1 : ℚ))⁻¹ • pSub m n R μ

/-- **The power sums and the `p_μ / z_μ` are dual bases** for the Hall scalar
product. -/
theorem hallInner_pSub_pSubInvZ [CommRing R] [Algebra ℚ R] (hnm : n ≤ m)
    (μ ν : PartLengthLe n m) :
    hallInner m n R (pSub m n R μ) (pSubInvZ m n R ν) = if μ = ν then 1 else 0 := by
  have hz : (zcard ν.1 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (zcard_pos ν.2.1).ne'
  have hzmul : (zcard ν.1 : R) * algebraMap ℚ R ((zcard ν.1 : ℚ))⁻¹ = 1 := by
    rw [← map_natCast (algebraMap ℚ R) (zcard ν.1), ← map_mul, mul_inv_cancel₀ hz, map_one]
  rw [pSubInvZ, map_smul, smul_eq_mul, hallInner_pSub hnm]
  by_cases hlm : μ = ν
  · subst hlm
    rw [ite_eq_left rfl, ite_eq_left rfl, mul_comm]
    exact hzmul
  · rw [ite_eq_right hlm, ite_eq_right hlm, mul_zero]

/-- The expansion of a symmetric homogeneous polynomial in the power sums. -/
theorem eq_sum_hallInner_pSubInvZ_smul [CommRing R] [Algebra ℚ R] (hnm : n ≤ m)
    (f : symHomogeneousSubmodule m n R) :
    f = ∑ μ : PartLengthLe n m, hallInner m n R f (pSubInvZ m n R μ) • pSub m n R μ :=
  eq_sum_hallInner_smul_of_dual (pSub m n R) (pSubInvZ m n R) (hallInner_pSub_pSubInvZ hnm) f

end MvPolynomial
