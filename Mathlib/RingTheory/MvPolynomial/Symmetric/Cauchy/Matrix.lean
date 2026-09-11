/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.HallInnerProduct
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.DualPieriSchur

/-!
# Cauchy kernels and their matrices

Following `theories/MPoly/homogsym.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we study the Cauchy kernels

`K(u, v) = ∑_lam u_μ(x) v_μ(y)`

attached to two families `u` and `v` of symmetric homogeneous polynomials of degree `n` in
`m` variables, indexed by the partitions of `n` with at most `m` parts.  Expanding `u` and
`v` in the Schur basis, `K(u, v)` only depends on the product `Aᵀ B` of the coordinate
matrices, and conversely determines it: this is the algebraic content of the duality
between the Cauchy identity and the Hall scalar product.

## Main results

* `MvPolynomial.cauchyKernelSum_eq_sum_smul` : the expansion of a Cauchy kernel in the products
  `s_ν(x) s_ρ(y)`.
* `MvPolynomial.transpose_mul_eq_of_cauchyKernelSum_eq` : two families with the same Cauchy kernel
  have the same matrix product `Aᵀ B`.
* `MvPolynomial.cauchyKernelSum_congr_right` : an equality of Cauchy kernels can be transformed by
  applying a linear map to the second family.
* `MvPolynomial.hallInner_eq_matrix` : the Hall scalar product in terms of the coordinate matrices.
-/

@[expose] public section

namespace MvPolynomial

open List MvPolynomial

variable {m n : ℕ} {R : Type*}

/-! ### Preliminaries -/

/-- The expansion of an element of the homogeneous component in the Schur basis. -/
lemma coe_eq_sum_repr_schurBasis [CommRing R] (f : symHomogeneousSubmodule m n R) :
    (f : MvPolynomial (Fin m) R)
      = ∑ ν : PartIdx n m, (schurBasis m n R).repr f ν • schurPoly (Fin m) R ν.1 := by
  conv_lhs => rw [← (schurBasis m n R).sum_repr f]
  push_cast [Submodule.coe_sum]
  exact Finset.sum_congr rfl fun ν _ => by rw [schurBasis_apply, coe_schurSub]

/-- Base change commutes with the scalar action of the base ring. -/
lemma map_C_smul [CommRing R] (a : R) (s : MvPolynomial (Fin m) R) :
    MvPolynomial.map (C : R →+* MvPolynomial (Fin m) R) (a • s)
      = a • MvPolynomial.map (C : R →+* MvPolynomial (Fin m) R) s := by
  simp [Algebra.smul_def, MvPolynomial.algebraMap_eq]

/-- The products `s_ν(x) s_ρ(y)`. -/
noncomputable def schurPairProd (m n : ℕ) (R : Type*) [CommRing R]
    (q : PartIdx n m × PartIdx n m) : MvPolynomial (Fin m) (MvPolynomial (Fin m) R) :=
  C (schurPoly (Fin m) R q.1.1)
    * MvPolynomial.map (C : R →+* MvPolynomial (Fin m) R) (schurPoly (Fin m) R q.2.1)

/-- The products `s_ν(x) s_ρ(y)` are linearly independent. -/
lemma linearIndependent_schurPairProd (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R (schurPairProd m n R) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  have hterm : ∀ ν ρ : PartIdx n m,
      g (ν, ρ) • schurPairProd m n R (ν, ρ)
      = (g (ν, ρ) • schurPoly (Fin m) R ν.1)
          • schurPoly (Fin m) (MvPolynomial (Fin m) R) ρ.1 := by
    intro ν ρ
    rw [schurPairProd, ← map_schurPoly (C : R →+* MvPolynomial (Fin m) R) ρ.1]
    simp [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    ring
  have hsum : ∑ ρ : PartIdx n m,
      (∑ ν : PartIdx n m, g (ν, ρ) • schurPoly (Fin m) R ν.1)
        • schurPoly (Fin m) (MvPolynomial (Fin m) R) ρ.1 = 0 := by
    rw [← hg, Fintype.sum_prod_type_right]
    exact Finset.sum_congr rfl fun ρ _ => by
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun ν _ => (hterm ν ρ).symm
  have hzero := Fintype.linearIndependent_iff.1
    (linearIndependent_schurPoly m n (MvPolynomial (Fin m) R)) _ hsum p.2
  exact Fintype.linearIndependent_iff.1 (linearIndependent_schurPoly m n R) _ hzero p.1

/-! ### The coordinate matrix of a family -/

/-- The matrix of the coordinates of a family in the Schur basis. -/
noncomputable def schurReprMat (m n : ℕ) (R : Type*) [CommRing R]
    (u : PartIdx n m → symHomogeneousSubmodule m n R) :
    Matrix (PartIdx n m) (PartIdx n m) R :=
  Matrix.of fun μ ν => (schurBasis m n R).repr (u μ) ν

@[simp] lemma schurReprMat_apply [CommRing R]
    (u : PartIdx n m → symHomogeneousSubmodule m n R) (μ ν : PartIdx n m) :
    schurReprMat m n R u μ ν = (schurBasis m n R).repr (u μ) ν := rfl

@[simp] lemma schurReprMat_schurSub (m n : ℕ) (R : Type*) [CommRing R] :
    schurReprMat m n R (schurSub m n R) = 1 := by
  classical
  ext μ ν
  simp only [schurReprMat_apply, ← schurBasis_apply, Module.Basis.repr_self,
    Finsupp.single_apply, Matrix.one_apply]

/-- The coordinate matrix of the image of a family under a linear map. -/
lemma schurReprMat_comp [CommRing R]
    (phi : symHomogeneousSubmodule m n R →ₗ[R] symHomogeneousSubmodule m n R)
    (v : PartIdx n m → symHomogeneousSubmodule m n R) :
    schurReprMat m n R (fun μ => phi (v μ))
      = schurReprMat m n R v * schurReprMat m n R (fun ρ => phi (schurSub m n R ρ)) := by
  classical
  ext μ ν
  rw [Matrix.mul_apply, schurReprMat_apply]
  have hv : v μ
      = ∑ ρ : PartIdx n m, (schurBasis m n R).repr (v μ) ρ • schurSub m n R ρ := by
    conv_lhs => rw [← (schurBasis m n R).sum_repr (v μ)]
    exact Finset.sum_congr rfl fun ρ _ => by rw [schurBasis_apply]
  rw [hv, map_sum, map_sum]
  simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul, schurReprMat_apply]

/-! ### Cauchy kernels -/

/-- The Cauchy kernel `∑_lam u_μ(x) v_μ(y)` attached to two families. -/
noncomputable def cauchyKernelSum (m n : ℕ) (R : Type*) [CommRing R]
    (u v : PartIdx n m → symHomogeneousSubmodule m n R) :
    MvPolynomial (Fin m) (MvPolynomial (Fin m) R) :=
  ∑ μ : PartIdx n m,
    C ((u μ : MvPolynomial (Fin m) R))
      * MvPolynomial.map (C : R →+* MvPolynomial (Fin m) R) ((v μ : MvPolynomial (Fin m) R))

/-- The expansion of a Cauchy kernel in the products `s_ν(x) s_ρ(y)`. -/
theorem cauchyKernelSum_eq_sum_smul [CommRing R]
    (u v : PartIdx n m → symHomogeneousSubmodule m n R) :
    cauchyKernelSum m n R u v
      = ∑ q : PartIdx n m × PartIdx n m,
          (((schurReprMat m n R u).transpose * schurReprMat m n R v) q.1 q.2)
            • schurPairProd m n R q := by
  classical
  set A := schurReprMat m n R u with hAdef
  set B := schurReprMat m n R v with hBdef
  have hu : ∀ μ : PartIdx n m,
      (C ((u μ : MvPolynomial (Fin m) R)) : MvPolynomial (Fin m) (MvPolynomial (Fin m) R))
        = ∑ ν : PartIdx n m, A μ ν • C (schurPoly (Fin m) R ν.1) := by
    intro μ
    rw [coe_eq_sum_repr_schurBasis, map_sum]
    exact Finset.sum_congr rfl fun ν _ => by
      simp [hAdef, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  have hv : ∀ μ : PartIdx n m,
      MvPolynomial.map (C : R →+* MvPolynomial (Fin m) R) ((v μ : MvPolynomial (Fin m) R))
        = ∑ ρ : PartIdx n m,
            B μ ρ • MvPolynomial.map (C : R →+* MvPolynomial (Fin m) R)
              (schurPoly (Fin m) R ρ.1) := by
    intro μ
    rw [coe_eq_sum_repr_schurBasis, map_sum]
    exact Finset.sum_congr rfl fun ρ _ => by
      simp [hBdef, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  have hswap : ∀ ν ρ : PartIdx n m, (A.transpose * B) ν ρ
      = ∑ μ : PartIdx n m, A μ ν * B μ ρ := by
    intro ν ρ
    rw [Matrix.mul_apply]
    rfl
  rw [Fintype.sum_prod_type, cauchyKernelSum]
  calc ∑ μ : PartIdx n m,
        C ((u μ : MvPolynomial (Fin m) R))
          * MvPolynomial.map (C : R →+* MvPolynomial (Fin m) R)
              ((v μ : MvPolynomial (Fin m) R))
      = ∑ μ : PartIdx n m, ∑ ν : PartIdx n m, ∑ ρ : PartIdx n m,
          (A μ ν * B μ ρ) • schurPairProd m n R (ν, ρ) := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [hu μ, hv μ, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => by
          rw [schurPairProd, smul_mul_smul_comm]
    _ = ∑ ν : PartIdx n m, ∑ μ : PartIdx n m, ∑ ρ : PartIdx n m,
          (A μ ν * B μ ρ) • schurPairProd m n R (ν, ρ) := Finset.sum_comm
    _ = ∑ ν : PartIdx n m, ∑ ρ : PartIdx n m, ∑ μ : PartIdx n m,
          (A μ ν * B μ ρ) • schurPairProd m n R (ν, ρ) :=
        Finset.sum_congr rfl fun ν _ => Finset.sum_comm
    _ = ∑ ν : PartIdx n m, ∑ ρ : PartIdx n m,
          ((A.transpose * B) ν ρ) • schurPairProd m n R (ν, ρ) :=
        Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => by
          rw [hswap, Finset.sum_smul]

/-- Two families with the same Cauchy kernel have the same matrix product `Aᵀ B`. -/
theorem transpose_mul_eq_of_cauchyKernelSum_eq [CommRing R]
    {u v u' v' : PartIdx n m → symHomogeneousSubmodule m n R}
    (h : cauchyKernelSum m n R u v = cauchyKernelSum m n R u' v') :
    (schurReprMat m n R u).transpose * schurReprMat m n R v
      = (schurReprMat m n R u').transpose * schurReprMat m n R v' := by
  classical
  rw [cauchyKernelSum_eq_sum_smul, cauchyKernelSum_eq_sum_smul] at h
  have hzero : ∑ q : PartIdx n m × PartIdx n m,
      ((((schurReprMat m n R u).transpose * schurReprMat m n R v) q.1 q.2)
        - (((schurReprMat m n R u').transpose * schurReprMat m n R v') q.1 q.2))
          • schurPairProd m n R q = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have hall := Fintype.linearIndependent_iff.1 (linearIndependent_schurPairProd m n R) _ hzero
  ext ν ρ
  exact sub_eq_zero.1 (hall (ν, ρ))

/-- An equality of Cauchy kernels can be transformed by applying a linear map to the second
family. -/
theorem cauchyKernelSum_congr_right [CommRing R]
    {u v u' v' : PartIdx n m → symHomogeneousSubmodule m n R}
    (h : cauchyKernelSum m n R u v = cauchyKernelSum m n R u' v')
    (phi : symHomogeneousSubmodule m n R →ₗ[R] symHomogeneousSubmodule m n R) :
    cauchyKernelSum m n R u (fun μ => phi (v μ))
      = cauchyKernelSum m n R u' (fun μ => phi (v' μ)) := by
  rw [cauchyKernelSum_eq_sum_smul, cauchyKernelSum_eq_sum_smul, schurReprMat_comp phi v,
    schurReprMat_comp phi v', ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    transpose_mul_eq_of_cauchyKernelSum_eq h]

/-- The Hall scalar product in terms of the coordinate matrices. -/
lemma hallInner_eq_matrix [CommRing R]
    (u v : PartIdx n m → symHomogeneousSubmodule m n R) (μ ν : PartIdx n m) :
    hallInner m n R (u μ) (v ν)
      = (schurReprMat m n R u * (schurReprMat m n R v).transpose) μ ν := by
  rw [hallInner_apply, Matrix.mul_apply]
  rfl

end MvPolynomial
