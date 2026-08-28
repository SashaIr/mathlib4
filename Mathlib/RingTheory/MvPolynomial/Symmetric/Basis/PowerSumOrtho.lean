/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Cauchy.Matrix
import Mathlib.RingTheory.MvPolynomial.Symmetric.Cauchy.PowerSum

/-!
# Orthogonality of the power sums

Following `theories/MPoly/homogsym.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove that the products of power
sums are orthogonal for the Hall scalar product, with `⟨p_lam, p_lam⟩ = z_lam`.

## Main results

* `MvPolynomial.hallInner_pSub` : `⟨p_lam, p_mu⟩ = z_lam` if `lam = mu` and `0` otherwise.
-/

namespace MvPolynomial

open List MvPolynomial

variable {m n : ℕ} {R : Type*}

/-! ### Preliminaries -/

/-- The base change of a power sum. -/
lemma map_psum {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : ℕ) :
    MvPolynomial.map f (psum (Fin m) R r) = psum (Fin m) S r := by
  simp [psum, map_sum]

/-- The base change of a product of power sums. -/
lemma map_pProd {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (lam : List ℕ) :
    MvPolynomial.map f (pProd m R lam) = pProd m S lam := by
  induction lam with
  | nil => simp [pProd]
  | cons a l ih => rw [pProd_cons, pProd_cons, map_mul, ih, map_psum]

/-! ### The duality criterion -/

/-- If two families satisfy the Cauchy identity, then they are dual bases for the Hall
scalar product. -/
theorem hallInner_eq_of_cauchy [CommRing R] (u v : PartIdx n m → symHomogeneousSubmodule m n R)
    (h : cauchyKernelSum m n R u v = cauchyKernelSum m n R (schurSub m n R) (schurSub m n R))
    (lam mu : PartIdx n m) :
    hallInner m n R (u lam) (v mu) = if lam = mu then 1 else 0 := by
  have hmat := transpose_mul_eq_of_cauchyKernelSum_eq h
  rw [schurReprMat_schurSub, Matrix.transpose_one, Matrix.one_mul] at hmat
  have h2 : (schurReprMat m n R v).transpose * schurReprMat m n R u = 1 := by
    have hc := congrArg Matrix.transpose hmat
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at hc
  rw [hallInner_eq_matrix, mul_eq_one_comm.2 h2]
  by_cases hlm : lam = mu
  · rw [if_pos hlm, hlm, Matrix.one_apply_eq]
  · rw [if_neg hlm, Matrix.one_apply_ne hlm]

/-! ### A family with a dual family is a basis -/

/-- The matrix identity behind duality: the coordinate matrices of two dual families in the
Schur basis are inverse to each other. -/
lemma mul_transpose_eq_one_of_hallInner_dual [CommRing R]
    (u v : PartIdx n m → symHomogeneousSubmodule m n R)
    (h : ∀ lam mu, hallInner m n R (u lam) (v mu) = if lam = mu then 1 else 0) :
    schurReprMat m n R u * (schurReprMat m n R v).transpose = 1 := by
  classical
  ext lam mu
  rw [← hallInner_eq_matrix, h lam mu]
  by_cases hc : lam = mu
  · rw [if_pos hc, hc, Matrix.one_apply_eq]
  · rw [if_neg hc, Matrix.one_apply_ne hc]

/-- The expansion of an element in a family admitting a dual family. -/
lemma eq_sum_hallInner_smul_of_dual [CommRing R]
    (u v : PartIdx n m → symHomogeneousSubmodule m n R)
    (h : ∀ lam mu, hallInner m n R (u lam) (v mu) = if lam = mu then 1 else 0)
    (f : symHomogeneousSubmodule m n R) :
    f = ∑ lam : PartIdx n m, hallInner m n R f (v lam) • u lam := by
  classical
  set A := schurReprMat m n R u with hAdef
  set B := schurReprMat m n R v with hBdef
  have hBA : B.transpose * A = 1 :=
    mul_eq_one_comm.2 (mul_transpose_eq_one_of_hallInner_dual u v h)
  refine (schurBasis m n R).repr.injective (Finsupp.ext fun nu => ?_)
  rw [map_sum]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, map_smul, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ lam : PartIdx n m,
      hallInner m n R f (v lam) * (schurBasis m n R).repr (u lam) nu
        = ∑ rho : PartIdx n m,
            (schurBasis m n R).repr f rho * (B.transpose rho lam * A lam nu) := by
    intro lam
    rw [hallInner_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun rho _ => by
      simp only [hAdef, hBdef, Matrix.transpose_apply, schurReprMat_apply]
      ring
  rw [Finset.sum_congr rfl fun lam _ => hterm lam, Finset.sum_comm]
  have hfin : ∀ rho : PartIdx n m,
      ∑ lam : PartIdx n m,
          (schurBasis m n R).repr f rho * (B.transpose rho lam * A lam nu)
        = (schurBasis m n R).repr f rho * (1 : Matrix (PartIdx n m) (PartIdx n m) R) rho nu := by
    intro rho
    rw [← Finset.mul_sum, ← hBA, Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun rho _ => hfin rho]
  rw [Finset.sum_eq_single nu]
  · rw [Matrix.one_apply_eq, mul_one]
  · intro rho _ hne
    rw [Matrix.one_apply_ne hne, mul_zero]
  · intro hc
    exact absurd (Finset.mem_univ nu) hc

/-- A family admitting a dual family for the Hall scalar product is linearly independent. -/
lemma linearIndependent_of_hallInner_dual [CommRing R]
    (u v : PartIdx n m → symHomogeneousSubmodule m n R)
    (h : ∀ lam mu, hallInner m n R (u lam) (v mu) = if lam = mu then 1 else 0) :
    LinearIndependent R u := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg mu
  have := congrArg (fun x => hallInner m n R x (v mu)) hg
  simp only [map_sum, map_smul, LinearMap.coe_sum, LinearMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, map_zero, LinearMap.zero_apply] at this
  rw [Finset.sum_congr rfl fun lam _ => by rw [h lam mu]] at this
  simpa using this

/-- **A family admitting a dual family for the Hall scalar product is a basis**. -/
noncomputable def basisOfHallInnerDual [CommRing R]
    (u v : PartIdx n m → symHomogeneousSubmodule m n R)
    (h : ∀ lam mu, hallInner m n R (u lam) (v mu) = if lam = mu then 1 else 0) :
    Module.Basis (PartIdx n m) R (symHomogeneousSubmodule m n R) :=
  Module.Basis.mk (linearIndependent_of_hallInner_dual u v h)
    (fun f _ => by
      rw [eq_sum_hallInner_smul_of_dual u v h f]
      exact Submodule.sum_mem _ fun lam _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨lam, rfl⟩))

@[simp] lemma basisOfHallInnerDual_apply [CommRing R]
    (u v : PartIdx n m → symHomogeneousSubmodule m n R)
    (h : ∀ lam mu, hallInner m n R (u lam) (v mu) = if lam = mu then 1 else 0)
    (lam : PartIdx n m) : basisOfHallInnerDual u v h lam = u lam := by
  rw [basisOfHallInnerDual, Module.Basis.mk_apply]

/-! ### Orthogonality of the power sums -/

/-- **The power sums are orthogonal** for the Hall scalar product, with
`⟨p_lam, p_lam⟩ = z_lam`. -/
theorem hallInner_pSub [CommRing R] [Algebra ℚ R] (hnm : n ≤ m) (lam mu : PartIdx n m) :
    hallInner m n R (pSub m n R lam) (pSub m n R mu)
      = if lam = mu then (zcard lam.1 : R) else 0 := by
  classical
  set zinv : PartIdx n m → R := fun l => algebraMap ℚ R ((zcard l.1 : ℚ))⁻¹ with hzinv
  have hzmul : ∀ l : PartIdx n m, (zcard l.1 : R) * zinv l = 1 := by
    intro l
    have hz : (zcard l.1 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (zcard_pos l.2.1).ne'
    rw [hzinv]
    simp only
    rw [← map_natCast (algebraMap ℚ R) (zcard l.1), ← map_mul, mul_inv_cancel₀ hz, map_one]
  have hcauchy : ∑ l : PartIdx n m,
      C ((pSub m n R l : MvPolynomial (Fin m) R))
        * MvPolynomial.map (C : R →+* MvPolynomial (Fin m) R)
            (((zinv l • pSub m n R l : symHomogeneousSubmodule m n R) :
              MvPolynomial (Fin m) R))
      = ∑ l : PartIdx n m,
          C (schurPoly (Fin m) R l.1)
            * MvPolynomial.map (C : R →+* MvPolynomial (Fin m) R) (schurPoly (Fin m) R l.1) := by
    have hpc := power_sum_cauchy m m n R
    rw [sum_partFinset_eq_sum_partIdx (m := m) hnm,
      sum_partFinset_eq_sum_partIdx (m := m) hnm] at hpc
    have hrhs : (∑ l : PartIdx n m, C (schurPoly (Fin m) R l.1)
          * MvPolynomial.map (C : R →+* MvPolynomial (Fin m) R) (schurPoly (Fin m) R l.1))
        = ∑ l : PartIdx n m, C (schurPoly (Fin m) R l.1)
            * schurPoly (Fin m) (MvPolynomial (Fin m) R) l.1 :=
      Finset.sum_congr rfl fun l _ => by rw [map_schurPoly]
    rw [hrhs, hpc]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← map_pProd (C : R →+* MvPolynomial (Fin m) R) l.1, coe_pSub, SetLike.val_smul,
      coe_pSub, map_C_smul, mul_smul_comm, hzinv]
    exact algebraMap_smul _ _ _
  have hkey := hallInner_eq_of_cauchy (pSub m n R) (fun l => zinv l • pSub m n R l) hcauchy lam mu
  rw [map_smul, smul_eq_mul] at hkey
  by_cases hlm : lam = mu
  · subst hlm
    rw [if_pos rfl] at hkey ⊢
    have := congrArg (fun x => (zcard lam.1 : R) * x) hkey
    simpa [← mul_assoc, hzmul lam] using this
  · rw [if_neg hlm] at hkey ⊢
    have := congrArg (fun x => (zcard mu.1 : R) * x) hkey
    simpa [← mul_assoc, hzmul mu] using this

/-- The family dual to the power sums: `p_lam / z_lam`. -/
noncomputable def pSubInvZ (m n : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R]
    (lam : PartIdx n m) : symHomogeneousSubmodule m n R :=
  algebraMap ℚ R ((zcard lam.1 : ℚ))⁻¹ • pSub m n R lam

/-- **The power sums and the `p_lam / z_lam` are dual bases** for the Hall scalar
product. -/
theorem hallInner_pSub_pSubInvZ [CommRing R] [Algebra ℚ R] (hnm : n ≤ m)
    (lam mu : PartIdx n m) :
    hallInner m n R (pSub m n R lam) (pSubInvZ m n R mu) = if lam = mu then 1 else 0 := by
  have hz : (zcard mu.1 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (zcard_pos mu.2.1).ne'
  have hzmul : (zcard mu.1 : R) * algebraMap ℚ R ((zcard mu.1 : ℚ))⁻¹ = 1 := by
    rw [← map_natCast (algebraMap ℚ R) (zcard mu.1), ← map_mul, mul_inv_cancel₀ hz, map_one]
  rw [pSubInvZ, map_smul, smul_eq_mul, hallInner_pSub hnm]
  by_cases hlm : lam = mu
  · subst hlm
    rw [if_pos rfl, if_pos rfl, mul_comm]
    exact hzmul
  · rw [if_neg hlm, if_neg hlm, mul_zero]

/-- The expansion of a symmetric homogeneous polynomial in the power sums. -/
theorem eq_sum_hallInner_pSubInvZ_smul [CommRing R] [Algebra ℚ R] (hnm : n ≤ m)
    (f : symHomogeneousSubmodule m n R) :
    f = ∑ lam : PartIdx n m, hallInner m n R f (pSubInvZ m n R lam) • pSub m n R lam :=
  eq_sum_hallInner_smul_of_dual (pSub m n R) (pSubInvZ m n R) (hallInner_pSub_pSubInvZ hnm) f

end MvPolynomial
