/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.Elementary
import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.HallInnerProduct

/-!
# The involution `omega`

Following `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we define the involution `omega` of
the module of symmetric homogeneous polynomials of degree `n` in `m` variables, for
`n ≤ m`: it is the linear map exchanging the Schur polynomials of two conjugate shapes.
We prove that it is an involution, that it is an isometry for the Hall scalar product,
and that it exchanges the complete homogeneous and the elementary symmetric polynomials,
`omega h_lam = e_lam`.

The hypothesis `n ≤ m` guarantees that conjugation is a permutation of the partitions of
`n` with at most `m` parts, that is, of the index set of the Schur basis.

## Main results

* `MvPolynomial.conjPartIdx` : conjugation as a permutation of the index set of the bases.
* `MvPolynomial.omegaSym` : the involution `omega`.
* `MvPolynomial.omegaSym_schurSub` : `omega s_lam = s_{lam'}`.
* `MvPolynomial.omegaSym_omegaSym` : `omega` is an involution.
* `MvPolynomial.hallInner_omegaSym` : `omega` is an isometry for the Hall scalar product.
* `MvPolynomial.omegaSym_hSub` : `omega h_lam = e_lam`.
* `MvPolynomial.omegaSym_eSubOfPart` : `omega e_lam = h_lam`.
-/

namespace MvPolynomial

open List MvPolynomial

variable {m n : ℕ} {R : Type*}

/-! ### Conjugation on the index set -/

/-- The conjugate of a partition of `n` with at most `m` parts, again as a partition of
`n` with at most `m` parts (using `n ≤ m`). -/
def conjIdx (hnm : n ≤ m) (lam : PartIdx n m) : PartIdx n m :=
  ⟨conjPart lam.1, isPart_conjPart lam.2.1, by rw [sum_conjPart, lam.2.2.1], by
    rw [length_conjPart lam.2.1]
    exact le_trans (le_trans (headD_le_sum lam.1) (le_of_eq lam.2.2.1)) hnm⟩

@[simp] lemma conjIdx_val (hnm : n ≤ m) (lam : PartIdx n m) :
    (conjIdx hnm lam).1 = conjPart lam.1 := rfl

lemma conjIdx_conjIdx (hnm : n ≤ m) (lam : PartIdx n m) :
    conjIdx hnm (conjIdx hnm lam) = lam :=
  Subtype.ext (conjPart_conjPart lam.2.1)

/-- Conjugation is a permutation of the partitions of `n` with at most `m` parts, as soon
as `n ≤ m`. -/
def conjPartIdx (hnm : n ≤ m) : PartIdx n m ≃ PartIdx n m where
  toFun := conjIdx hnm
  invFun := conjIdx hnm
  left_inv := conjIdx_conjIdx hnm
  right_inv := conjIdx_conjIdx hnm

@[simp] lemma conjPartIdx_apply (hnm : n ≤ m) (lam : PartIdx n m) :
    conjPartIdx hnm lam = conjIdx hnm lam := rfl

/-! ### The involution -/

/-- **The involution `omega`**: the linear automorphism of the symmetric homogeneous
polynomials of degree `n` in `m` variables (`n ≤ m`) exchanging the Schur polynomials of
two conjugate shapes. -/
noncomputable def omegaSym (m n : ℕ) (R : Type*) [CommRing R] (hnm : n ≤ m) :
    symHomogeneousSubmodule m n R ≃ₗ[R] symHomogeneousSubmodule m n R :=
  (schurBasis m n R).equiv (schurBasis m n R) (conjPartIdx hnm)

/-- `omega` exchanges the Schur polynomials of two conjugate shapes. -/
@[simp] theorem omegaSym_schurSub [CommRing R] (hnm : n ≤ m) (lam : PartIdx n m) :
    omegaSym m n R hnm (schurSub m n R lam) = schurSub m n R (conjIdx hnm lam) := by
  rw [← schurBasis_apply, omegaSym, Module.Basis.equiv_apply, conjPartIdx_apply,
    schurBasis_apply]

/-- **`omega` is an involution**. -/
theorem omegaSym_omegaSym [CommRing R] (hnm : n ≤ m) (f : symHomogeneousSubmodule m n R) :
    omegaSym m n R hnm (omegaSym m n R hnm f) = f := by
  refine LinearMap.congr_fun (f := (omegaSym m n R hnm).toLinearMap.comp
    (omegaSym m n R hnm).toLinearMap) (g := LinearMap.id) ?_ f
  refine (schurBasis m n R).ext fun lam => ?_
  simp [conjIdx_conjIdx]

/-- The coordinates of `omega f` in the Schur basis are those of `f`, at the conjugate
shape. -/
lemma repr_schurBasis_omegaSym [CommRing R] (hnm : n ≤ m)
    (f : symHomogeneousSubmodule m n R) (lam : PartIdx n m) :
    (schurBasis m n R).repr (omegaSym m n R hnm f) lam
      = (schurBasis m n R).repr f (conjIdx hnm lam) := by
  have hom : omegaSym m n R hnm f
      = ∑ nu : PartIdx n m,
          (schurBasis m n R).repr f (conjIdx hnm nu) • schurBasis m n R nu := by
    conv_lhs => rw [← (schurBasis m n R).sum_repr f]
    rw [map_sum]
    refine Fintype.sum_equiv (conjPartIdx hnm) _ _ fun mu => ?_
    rw [conjPartIdx_apply, conjIdx_conjIdx, map_smul, schurBasis_apply, omegaSym_schurSub,
      ← schurBasis_apply]
  rw [hom, Module.Basis.repr_sum_self]

/-- **`omega` is an isometry** for the Hall scalar product. -/
theorem hallInner_omegaSym [CommRing R] (hnm : n ≤ m)
    (f g : symHomogeneousSubmodule m n R) :
    hallInner m n R (omegaSym m n R hnm f) (omegaSym m n R hnm g) = hallInner m n R f g := by
  rw [hallInner_apply, hallInner_apply]
  refine Fintype.sum_equiv (conjPartIdx hnm) _ _ fun lam => ?_
  rw [repr_schurBasis_omegaSym, repr_schurBasis_omegaSym, conjPartIdx_apply]

/-! ### `omega` exchanges the bases `h` and `e` -/

lemma eProd_mem_symHomogeneousSubmodule [CommRing R] (hnm : n ≤ m) (lam : PartIdx n m) :
    eProd m R lam.1 ∈ symHomogeneousSubmodule m n R := by
  have h := eProd_conj_mem_symHomogeneousSubmodule (R := R) (conjIdx hnm lam)
  rwa [conjIdx_val, conjPart_conjPart lam.2.1] at h

/-- The product `e_lam = e_{lam_1} ⋯ e_{lam_k}` of elementary symmetric polynomials, as an
element of the module of symmetric homogeneous polynomials of degree `n` (here `n ≤ m`, so
that all the factors are nonzero). -/
noncomputable def eSubOfPart (m n : ℕ) (R : Type*) [CommRing R] (hnm : n ≤ m)
    (lam : PartIdx n m) : symHomogeneousSubmodule m n R :=
  ⟨eProd m R lam.1, eProd_mem_symHomogeneousSubmodule hnm lam⟩

@[simp] lemma coe_eSubOfPart (m n : ℕ) (R : Type*) [CommRing R] (hnm : n ≤ m)
    (lam : PartIdx n m) :
    (eSubOfPart m n R hnm lam : MvPolynomial (Fin m) R) = eProd m R lam.1 := rfl

/-- The expansion of `e_lam` in the Schur polynomials, indexed by `PartIdx n m`. -/
lemma eProd_eq_sum_partIdx [CommRing R] (lam : PartIdx n m) :
    eProd m R lam.1
      = ∑ nu : PartIdx n m, (kostka (conjPart nu.1) lam.1 : R) • schurPoly (Fin m) R nu.1 := by
  classical
  rw [eProd_eq_sum_partsFinset m lam.2.1, lam.2.2.1, partsFinset,
    Finset.sum_image fun x _ y _ h => Subtype.ext h]

/-- **`omega` exchanges the complete homogeneous and the elementary symmetric
polynomials**: `omega h_lam = e_lam`. -/
theorem omegaSym_hSub [CommRing R] (hnm : n ≤ m) (lam : PartIdx n m) :
    omegaSym m n R hnm (hSub m n R lam) = eSubOfPart m n R hnm lam := by
  classical
  apply Subtype.ext
  change (omegaSym m n R hnm (hSub m n R lam) : MvPolynomial (Fin m) R) = eProd m R lam.1
  have hh : hSub m n R lam
      = ∑ nu : PartIdx n m, (kostka nu.1 lam.1 : R) • schurSub m n R nu := by
    apply Subtype.ext
    have hcoe : ((∑ nu : PartIdx n m, (kostka nu.1 lam.1 : R) • schurSub m n R nu
          : symHomogeneousSubmodule m n R) : MvPolynomial (Fin m) R)
        = ∑ nu : PartIdx n m, (kostka nu.1 lam.1 : R) • schurPoly (Fin m) R nu.1 := by
      simp
    rw [hcoe, coe_hSub, hProd_eq_sum_partIdx]
  rw [hh, map_sum]
  have hcoe : ((∑ nu : PartIdx n m,
        omegaSym m n R hnm ((kostka nu.1 lam.1 : R) • schurSub m n R nu)
          : symHomogeneousSubmodule m n R) : MvPolynomial (Fin m) R)
      = ∑ nu : PartIdx n m, (kostka nu.1 lam.1 : R) • schurPoly (Fin m) R (conjPart nu.1) := by
    simp
  rw [hcoe, eProd_eq_sum_partIdx lam]
  refine (Fintype.sum_equiv (conjPartIdx hnm) _ _ fun nu => ?_).symm
  rw [conjPartIdx_apply, conjIdx_val, conjPart_conjPart nu.2.1]

/-! ### The forgotten symmetric polynomials -/

/-- The forgotten symmetric polynomial `f_lam`, the image of the monomial symmetric
polynomial `m_lam` under the involution `omega`. -/
noncomputable def forgottenSub (m n : ℕ) (R : Type*) [CommRing R] (hnm : n ≤ m)
    (lam : PartIdx n m) : symHomogeneousSubmodule m n R :=
  omegaSym m n R hnm (mSub m n R lam)

/-- **The elementary symmetric polynomials and the forgotten symmetric polynomials are
dual bases** for the Hall scalar product. -/
theorem hallInner_eSubOfPart_forgottenSub [CommRing R] (hnm : n ≤ m) (lam mu : PartIdx n m) :
    hallInner m n R (eSubOfPart m n R hnm lam) (forgottenSub m n R hnm mu)
      = if lam = mu then 1 else 0 := by
  rw [forgottenSub, ← omegaSym_hSub hnm lam, hallInner_omegaSym, hallInner_hSub_mSub]

/-- `omega` exchanges the elementary and the complete homogeneous symmetric
polynomials: `omega e_lam = h_lam`. -/
theorem omegaSym_eSubOfPart [CommRing R] (hnm : n ≤ m) (lam : PartIdx n m) :
    omegaSym m n R hnm (eSubOfPart m n R hnm lam) = hSub m n R lam := by
  rw [← omegaSym_hSub hnm lam, omegaSym_omegaSym]

end MvPolynomial
