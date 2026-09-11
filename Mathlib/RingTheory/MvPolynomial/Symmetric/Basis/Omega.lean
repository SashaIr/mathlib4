/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.Elementary
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.HallInnerProduct

/-!
# The involution `omega`

Following `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we define the involution `omega` of
the module of symmetric homogeneous polynomials of degree `n` in `m` variables, for
`n ≤ m`: it is the linear map exchanging the Schur polynomials of two conjugate shapes.
We prove that it is an involution, that it is an isometry for the Hall scalar product,
and that it exchanges the complete homogeneous and the elementary symmetric polynomials,
`omega h_μ = e_μ`.

The hypothesis `n ≤ m` guarantees that conjugation is a permutation of the partitions of
`n` with at most `m` parts, that is, of the index set of the Schur basis.

## Main results

* `MvPolynomial.conjPartIdx` : conjugation as a permutation of the index set of the bases.
* `MvPolynomial.omegaSym` : the involution `omega`.
* `MvPolynomial.omegaSym_schurSub` : `omega s_μ = s_{μ'}`.
* `MvPolynomial.omegaSym_omegaSym` : `omega` is an involution.
* `MvPolynomial.hallInner_omegaSym` : `omega` is an isometry for the Hall scalar product.
* `MvPolynomial.omegaSym_hSub` : `omega h_μ = e_μ`.
* `MvPolynomial.omegaSym_eSubOfPart` : `omega e_μ = h_μ`.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {m n : ℕ} {R : Type*}

/-! ### Conjugation on the index set -/

/-- The conjugate of a partition of `n` with at most `m` parts, again as a partition of
`n` with at most `m` parts (using `n ≤ m`). -/
def conjIdx (hnm : n ≤ m) (μ : PartIdx n m) : PartIdx n m :=
  ⟨conjPart μ.1, isPart_conjPart μ.2.1, by rw [sum_conjPart, μ.2.2.1], by
    rw [length_conjPart μ.2.1]
    exact le_trans (le_trans (headD_le_sum μ.1) (le_of_eq μ.2.2.1)) hnm⟩

@[simp] lemma conjIdx_val (hnm : n ≤ m) (μ : PartIdx n m) :
    (conjIdx hnm μ).1 = conjPart μ.1 := rfl

lemma conjIdx_conjIdx (hnm : n ≤ m) (μ : PartIdx n m) :
    conjIdx hnm (conjIdx hnm μ) = μ :=
  Subtype.ext (conjPart_conjPart μ.2.1)

/-- Conjugation is a permutation of the partitions of `n` with at most `m` parts, as soon
as `n ≤ m`. -/
def conjPartIdx (hnm : n ≤ m) : PartIdx n m ≃ PartIdx n m where
  toFun := conjIdx hnm
  invFun := conjIdx hnm
  left_inv := conjIdx_conjIdx hnm
  right_inv := conjIdx_conjIdx hnm

@[simp] lemma conjPartIdx_apply (hnm : n ≤ m) (μ : PartIdx n m) :
    conjPartIdx hnm μ = conjIdx hnm μ := rfl

/-! ### The involution -/

/-- **The involution `omega`**: the linear automorphism of the symmetric homogeneous
polynomials of degree `n` in `m` variables (`n ≤ m`) exchanging the Schur polynomials of
two conjugate shapes. -/
noncomputable def omegaSym (m n : ℕ) (R : Type*) [CommRing R] (hnm : n ≤ m) :
    symHomogeneousSubmodule m n R ≃ₗ[R] symHomogeneousSubmodule m n R :=
  (schurBasis m n R).equiv (schurBasis m n R) (conjPartIdx hnm)

/-- `omega` exchanges the Schur polynomials of two conjugate shapes. -/
@[simp] theorem omegaSym_schurSub [CommRing R] (hnm : n ≤ m) (μ : PartIdx n m) :
    omegaSym m n R hnm (schurSub m n R μ) = schurSub m n R (conjIdx hnm μ) := by
  rw [← schurBasis_apply, omegaSym, Module.Basis.equiv_apply, conjPartIdx_apply,
    schurBasis_apply]

/-- **`omega` is an involution**. -/
theorem omegaSym_omegaSym [CommRing R] (hnm : n ≤ m) (f : symHomogeneousSubmodule m n R) :
    omegaSym m n R hnm (omegaSym m n R hnm f) = f := by
  refine LinearMap.congr_fun (f := (omegaSym m n R hnm).toLinearMap.comp
    (omegaSym m n R hnm).toLinearMap) (g := LinearMap.id) ?_ f
  refine (schurBasis m n R).ext fun μ => ?_
  simp [conjIdx_conjIdx]

/-- The coordinates of `omega f` in the Schur basis are those of `f`, at the conjugate
shape. -/
lemma repr_schurBasis_omegaSym [CommRing R] (hnm : n ≤ m)
    (f : symHomogeneousSubmodule m n R) (μ : PartIdx n m) :
    (schurBasis m n R).repr (omegaSym m n R hnm f) μ
      = (schurBasis m n R).repr f (conjIdx hnm μ) := by
  have hom : omegaSym m n R hnm f
      = ∑ ρ : PartIdx n m,
          (schurBasis m n R).repr f (conjIdx hnm ρ) • schurBasis m n R ρ := by
    conv_lhs => rw [← (schurBasis m n R).sum_repr f]
    rw [map_sum]
    refine Fintype.sum_equiv (conjPartIdx hnm) _ _ fun ν => ?_
    rw [conjPartIdx_apply, conjIdx_conjIdx, map_smul, schurBasis_apply, omegaSym_schurSub,
      ← schurBasis_apply]
  rw [hom, Module.Basis.repr_sum_self]

/-- **`omega` is an isometry** for the Hall scalar product. -/
theorem hallInner_omegaSym [CommRing R] (hnm : n ≤ m)
    (f g : symHomogeneousSubmodule m n R) :
    hallInner m n R (omegaSym m n R hnm f) (omegaSym m n R hnm g) = hallInner m n R f g := by
  rw [hallInner_apply, hallInner_apply]
  refine Fintype.sum_equiv (conjPartIdx hnm) _ _ fun μ => ?_
  rw [repr_schurBasis_omegaSym, repr_schurBasis_omegaSym, conjPartIdx_apply]

/-! ### `omega` exchanges the bases `h` and `e` -/

lemma eProd_mem_symHomogeneousSubmodule [CommRing R] (hnm : n ≤ m) (μ : PartIdx n m) :
    eProd m R μ.1 ∈ symHomogeneousSubmodule m n R := by
  have h := eProd_conj_mem_symHomogeneousSubmodule (R := R) (conjIdx hnm μ)
  rwa [conjIdx_val, conjPart_conjPart μ.2.1] at h

/-- The product `e_μ = e_{μ_1} ⋯ e_{μ_k}` of elementary symmetric polynomials, as an
element of the module of symmetric homogeneous polynomials of degree `n` (here `n ≤ m`, so
that all the factors are nonzero). -/
noncomputable def eSubOfPart (m n : ℕ) (R : Type*) [CommRing R] (hnm : n ≤ m)
    (μ : PartIdx n m) : symHomogeneousSubmodule m n R :=
  ⟨eProd m R μ.1, eProd_mem_symHomogeneousSubmodule hnm μ⟩

@[simp] lemma coe_eSubOfPart (m n : ℕ) (R : Type*) [CommRing R] (hnm : n ≤ m)
    (μ : PartIdx n m) :
    (eSubOfPart m n R hnm μ : MvPolynomial (Fin m) R) = eProd m R μ.1 := rfl

/-- The expansion of `e_μ` in the Schur polynomials, indexed by `PartIdx n m`. -/
lemma eProd_eq_sum_partIdx [CommRing R] (μ : PartIdx n m) :
    eProd m R μ.1
      = ∑ ν : PartIdx n m, (kostka (conjPart ν.1) μ.1 : R) • schurPoly (Fin m) R ν.1 := by
  classical
  rw [eProd_eq_sum_partsFinset m μ.2.1, μ.2.2.1, partsFinset,
    Finset.sum_image fun x _ y _ h => Subtype.ext h]

/-- **`omega` exchanges the complete homogeneous and the elementary symmetric
polynomials**: `omega h_μ = e_μ`. -/
theorem omegaSym_hSub [CommRing R] (hnm : n ≤ m) (μ : PartIdx n m) :
    omegaSym m n R hnm (hSub m n R μ) = eSubOfPart m n R hnm μ := by
  classical
  apply Subtype.ext
  change (omegaSym m n R hnm (hSub m n R μ) : MvPolynomial (Fin m) R) = eProd m R μ.1
  have hh : hSub m n R μ
      = ∑ ν : PartIdx n m, (kostka ν.1 μ.1 : R) • schurSub m n R ν := by
    apply Subtype.ext
    have hcoe : ((∑ ν : PartIdx n m, (kostka ν.1 μ.1 : R) • schurSub m n R ν
          : symHomogeneousSubmodule m n R) : MvPolynomial (Fin m) R)
        = ∑ ν : PartIdx n m, (kostka ν.1 μ.1 : R) • schurPoly (Fin m) R ν.1 := by
      simp
    rw [hcoe, coe_hSub, hProd_eq_sum_partIdx]
  rw [hh, map_sum]
  have hcoe : ((∑ ν : PartIdx n m,
        omegaSym m n R hnm ((kostka ν.1 μ.1 : R) • schurSub m n R ν)
          : symHomogeneousSubmodule m n R) : MvPolynomial (Fin m) R)
      = ∑ ν : PartIdx n m, (kostka ν.1 μ.1 : R) • schurPoly (Fin m) R (conjPart ν.1) := by
    simp
  rw [hcoe, eProd_eq_sum_partIdx μ]
  refine (Fintype.sum_equiv (conjPartIdx hnm) _ _ fun ν => ?_).symm
  rw [conjPartIdx_apply, conjIdx_val, conjPart_conjPart ν.2.1]

/-! ### The forgotten symmetric polynomials -/

/-- The forgotten symmetric polynomial `f_μ`, the image of the monomial symmetric
polynomial `m_μ` under the involution `omega`. -/
noncomputable def forgottenSub (m n : ℕ) (R : Type*) [CommRing R] (hnm : n ≤ m)
    (μ : PartIdx n m) : symHomogeneousSubmodule m n R :=
  omegaSym m n R hnm (mSub m n R μ)

/-- **The elementary symmetric polynomials and the forgotten symmetric polynomials are
dual bases** for the Hall scalar product. -/
theorem hallInner_eSubOfPart_forgottenSub [CommRing R] (hnm : n ≤ m) (μ ν : PartIdx n m) :
    hallInner m n R (eSubOfPart m n R hnm μ) (forgottenSub m n R hnm ν)
      = if μ = ν then 1 else 0 := by
  rw [forgottenSub, ← omegaSym_hSub hnm μ, hallInner_omegaSym, hallInner_hSub_mSub]

/-- `omega` exchanges the elementary and the complete homogeneous symmetric
polynomials: `omega e_μ = h_μ`. -/
theorem omegaSym_eSubOfPart [CommRing R] (hnm : n ≤ m) (μ : PartIdx n m) :
    omegaSym m n R hnm (eSubOfPart m n R hnm μ) = hSub m n R μ := by
  rw [← omegaSym_hSub hnm μ, omegaSym_omegaSym]

end MvPolynomial
