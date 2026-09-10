/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.CompleteHomogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.PowerSumBasis

/-!
# The Hall scalar product

Following `theories/MPoly/homogsym.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we define the Hall scalar product on
the module of symmetric homogeneous polynomials of degree `n` in `m` variables, as the
bilinear form for which the Schur polynomials are orthonormal, and we prove that the
complete homogeneous symmetric polynomials and the monomial symmetric polynomials are
dual bases for it.

## Main results

* `MvPolynomial.mBasis` : the monomial symmetric polynomials of the partitions of `n` with at
  most `m` parts form a basis of the symmetric homogeneous polynomials of degree `n`.
* `MvPolynomial.hallInner` : the Hall scalar product.
* `MvPolynomial.hallInner_schurSub` : the Schur polynomials are orthonormal.
* `MvPolynomial.hallInner_comm` : the Hall scalar product is symmetric.
* `MvPolynomial.hallInner_hSub_eq_coeff` : `⟨h_μ, f⟩` is the coefficient of the monomial
  `x^μ` in `f`.
* `MvPolynomial.hallInner_hSub_mSub` : the bases `h` and `m` are dual to each other.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {m n : ℕ} {R : Type*}

/-! ### The monomial symmetric polynomials as a basis of a homogeneous component -/

/-- The monomial symmetric polynomial of a partition of `n` is homogeneous of degree
`n`. -/
lemma isHomogeneous_monomialSym [CommSemiring R] {η : List ℕ} (hη : IsPart η)
    (hlen : η.length ≤ m) (hsum : η.sum = n) :
    (monomialSym m R η).IsHomogeneous n := by
  classical
  rw [monomialSym]
  refine IsHomogeneous.sum _ _ _ fun d hd => isHomogeneous_monomial 1 ?_
  rw [Finsupp.degree]
  have h1 : ∑ i ∈ d.support, d i = ∑ i : Fin m, d i :=
    Finset.sum_subset (Finset.subset_univ _) fun i _ hi => Finsupp.notMem_support_iff.1 hi
  change (∑ i ∈ d.support, d i) = n
  rw [h1, sum_eq_of_mem_degOrbit_shapeContent hη hlen hd, hsum]

lemma monomialSym_mem_symHomogeneousSubmodule [CommRing R] (η : PartIdx n m) :
    monomialSym m R η.1 ∈ symHomogeneousSubmodule m n R :=
  ⟨isHomogeneous_monomialSym η.2.1 η.2.2.2 η.2.2.1, monomialSym_isSymmetric η.1⟩

/-- The monomial symmetric polynomial of a partition of `n` with at most `m` parts, as an
element of the module of symmetric homogeneous polynomials of degree `n`. -/
noncomputable def mSub (m n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n m) :
    symHomogeneousSubmodule m n R :=
  ⟨monomialSym m R η.1, monomialSym_mem_symHomogeneousSubmodule η⟩

@[simp] lemma coe_mSub (m n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n m) :
    (mSub m n R η : MvPolynomial (Fin m) R) = monomialSym m R η.1 := rfl

lemma linearIndependent_mSub (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R (mSub m n R) :=
  LinearIndependent.of_comp (symHomogeneousSubmodule m n R).subtype
    (linearIndependent_monomialSym_partIdx m n R)

/-- Every symmetric homogeneous polynomial of degree `n` is the combination of the
monomial symmetric polynomials of the partitions of `n` with at most `m` parts given by
its coefficients. -/
lemma eq_sum_coeff_mSub [CommRing R] (f : symHomogeneousSubmodule m n R) :
    f = ∑ μ : PartIdx n m,
      coeff (shapeContent m μ.1) (f : MvPolynomial (Fin m) R) • mSub m n R μ := by
  classical
  apply Subtype.ext
  have hcoe : ((∑ μ : PartIdx n m, coeff (shapeContent m μ.1) (f : MvPolynomial (Fin m) R)
        • mSub m n R μ : symHomogeneousSubmodule m n R) : MvPolynomial (Fin m) R)
      = ∑ μ : PartIdx n m, coeff (shapeContent m μ.1) (f : MvPolynomial (Fin m) R)
        • monomialSym m R μ.1 := by
    simp
  rw [hcoe]
  conv_lhs => rw [eq_sum_monomialSym_partsFinset f.2.2 f.2.1]
  rw [partsFinset, Finset.sum_image fun x _ y _ h => Subtype.ext h]

lemma span_mSub (m n : ℕ) (R : Type*) [CommRing R] :
    ⊤ ≤ Submodule.span R (Set.range (mSub m n R)) := by
  intro f _
  rw [eq_sum_coeff_mSub f]
  exact Submodule.sum_mem _ fun μ _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, rfl⟩)

/-- **The monomial symmetric polynomials form a basis** of the module of symmetric
homogeneous polynomials of degree `n` in `m` variables. -/
noncomputable def mBasis (m n : ℕ) (R : Type*) [CommRing R] :
    Module.Basis (PartIdx n m) R (symHomogeneousSubmodule m n R) :=
  Module.Basis.mk (linearIndependent_mSub m n R) (span_mSub m n R)

@[simp] lemma mBasis_apply (m n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n m) :
    mBasis m n R η = mSub m n R η := by
  rw [mBasis, Module.Basis.mk_apply]

lemma coe_mBasis (m n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n m) :
    (mBasis m n R η : MvPolynomial (Fin m) R) = monomialSym m R η.1 := by
  rw [mBasis_apply, coe_mSub]

@[simp] lemma schurBasis_apply (m n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n m) :
    schurBasis m n R η = schurSub m n R η := by
  rw [schurBasis, Module.Basis.mk_apply]

/-- The coordinates of a symmetric homogeneous polynomial in the basis of the monomial
symmetric polynomials are its coefficients. -/
lemma repr_mBasis_apply [CommRing R] (f : symHomogeneousSubmodule m n R)
    (η : PartIdx n m) :
    (mBasis m n R).repr f η = coeff (shapeContent m η.1) (f : MvPolynomial (Fin m) R) := by
  conv_lhs => rw [eq_sum_coeff_mSub f]
  simp only [← mBasis_apply]
  rw [Module.Basis.repr_sum_self]

/-! ### The Kostka expansions in coordinates -/

/-- The number of tableaux of a given content does not change when the alphabet is
enlarged, as long as the extra letters do not occur. -/
lemma kostkaNum_alphabet {N N' : ℕ} {μ : List ℕ} {c : ℕ → ℕ} (hc : ∀ i, N ≤ i → c i = 0)
    (hle : N ≤ N') : kostkaNum N' μ c = kostkaNum N μ c := by
  have hset : tabSet N' μ c = tabSet N μ c := by
    ext P
    simp only [tabSet, Set.mem_ofPred_eq]
    refine and_congr_right fun hP => and_congr_right fun hμ => ?_
    constructor
    · rintro ⟨hlt, hcount⟩
      refine ⟨fun x hx => ?_, fun i hi => hcount i (lt_of_lt_of_le hi hle)⟩
      by_contra hxN
      have hcx : P.flatten.count x = c x := hcount x (hlt x hx)
      rw [hc x (by omega)] at hcx
      exact absurd (List.count_pos_iff.2 hx) (by omega)
    · rintro ⟨hlt, hcount⟩
      refine ⟨fun x hx => lt_of_lt_of_le (hlt x hx) hle, fun i hi => ?_⟩
      rcases lt_or_ge i N with h | h
      · exact hcount i h
      · rw [hc i h, List.count_eq_zero]
        intro hmem
        exact absurd (hlt i hmem) (by omega)
  rw [kostkaNum, kostkaNum, hset]

/-- The bridge between the two definitions of the Kostka numbers, over an alphabet of any
size at least the number of parts of the content. -/
lemma kostkaNum_eq_kostka' {μ : List ℕ} (hμ : IsPart μ) (hlen : μ.length ≤ m)
    (ν : List ℕ) : kostkaNum m ν (fun i => μ.getD i 0) = kostka ν μ := by
  have h1 : kostkaNum m ν (fun i => μ.getD i 0)
      = kostkaNum μ.length ν (fun i => μ.getD i 0) :=
    kostkaNum_alphabet (fun i hi => List.getD_eq_default _ _ hi) hlen
  rw [h1]
  exact kostkaNum_eq_kostka hμ ν

/-- The expansion of a Schur polynomial in the monomial symmetric polynomials, indexed by
`PartIdx n m`. -/
lemma schurPoly_eq_sum_partIdx [CommRing R] (η : PartIdx n m) :
    schurPoly (Fin m) R η.1
      = ∑ μ : PartIdx n m, (kostka η.1 μ.1 : R) • monomialSym m R μ.1 := by
  classical
  rw [schurPoly_eq_sum_kostkaNum_monomialSym η.1, η.2.2.1, partsFinset,
    Finset.sum_image fun x _ y _ h => Subtype.ext h]
  exact Finset.sum_congr rfl fun μ _ => by
    rw [kostkaNum_eq_kostka' μ.2.1 μ.2.2.2 η.1]

lemma repr_mBasis_schurSub [CommRing R] (η μ : PartIdx n m) :
    (mBasis m n R).repr (schurSub m n R η) μ = (kostka η.1 μ.1 : R) := by
  rw [repr_mBasis_apply]
  have hcoe : ((schurSub m n R η : symHomogeneousSubmodule m n R) : MvPolynomial (Fin m) R)
      = ∑ ν : PartIdx n m, (kostka η.1 ν.1 : R) • monomialSym m R ν.1 := by
    rw [coe_schurSub, schurPoly_eq_sum_partIdx]
  rw [hcoe, coeff_sum]
  rw [Finset.sum_eq_single μ]
  · rw [coeff_smul, coeff_monomialSym_shapeContent, smul_eq_mul, mul_one]
  · intro ν _ hne
    rw [coeff_smul, coeff_monomialSym, ite_eq_right, smul_zero]
    intro hmem
    have h2 := degShape_eq_iff.2 (mem_degOrbit_iff.1 hmem)
    rw [degShape_shapeContent μ.2.1 μ.2.2.2, degShape_shapeContent ν.2.1 ν.2.2.2] at h2
    exact hne (Subtype.ext h2.symm)
  · intro h
    exact absurd (Finset.mem_univ μ) h

lemma repr_schurBasis_hSub [CommRing R] (η μ : PartIdx n m) :
    (schurBasis m n R).repr (hSub m n R μ) η = (kostka η.1 μ.1 : R) := by
  have hsum : hSub m n R μ
      = ∑ ν : PartIdx n m, (kostka ν.1 μ.1 : R) • schurBasis m n R ν := by
    apply Subtype.ext
    have hcoe : ((∑ ν : PartIdx n m, (kostka ν.1 μ.1 : R) • schurBasis m n R ν
          : symHomogeneousSubmodule m n R) : MvPolynomial (Fin m) R)
        = ∑ ν : PartIdx n m, (kostka ν.1 μ.1 : R) • schurPoly (Fin m) R ν.1 := by
      simp
    rw [hcoe, coe_hSub, hProd_eq_sum_partIdx]
  rw [hsum, Module.Basis.repr_sum_self]

/-! ### The Hall scalar product -/

/-- **The Hall scalar product**: the symmetric bilinear form on the symmetric homogeneous
polynomials of degree `n` in `m` variables for which the Schur polynomials form an
orthonormal basis. -/
noncomputable def hallInner (m n : ℕ) (R : Type*) [CommRing R] :
    symHomogeneousSubmodule m n R →ₗ[R] symHomogeneousSubmodule m n R →ₗ[R] R :=
  LinearMap.mk₂ R
    (fun f g => ∑ η : PartIdx n m,
      (schurBasis m n R).repr f η * (schurBasis m n R).repr g η)
    (by intro f₁ f₂ g; simp [add_mul, Finset.sum_add_distrib])
    (by intro c f g; simp [Finset.mul_sum, mul_assoc])
    (by intro f g₁ g₂; simp [mul_add, Finset.sum_add_distrib])
    (by
      intro c f g
      simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)

lemma hallInner_apply [CommRing R] (f g : symHomogeneousSubmodule m n R) :
    hallInner m n R f g
      = ∑ η : PartIdx n m,
          (schurBasis m n R).repr f η * (schurBasis m n R).repr g η := rfl

/-- **The Schur polynomials are orthonormal** for the Hall scalar product. -/
theorem hallInner_schurSub [CommRing R] (η μ : PartIdx n m) :
    hallInner m n R (schurSub m n R η) (schurSub m n R μ) = if η = μ then 1 else 0 := by
  classical
  rw [hallInner_apply]
  simp only [← schurBasis_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

/-- The Hall scalar product is symmetric. -/
theorem hallInner_comm [CommRing R] (f g : symHomogeneousSubmodule m n R) :
    hallInner m n R f g = hallInner m n R g f := by
  simp only [hallInner_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- **The Hall scalar product against `h_μ` extracts a coefficient**: pairing with the
product of complete homogeneous symmetric polynomials `h_μ` gives the coefficient of the
monomial `x^μ`. -/
theorem hallInner_hSub_eq_coeff [CommRing R] (μ : PartIdx n m)
    (f : symHomogeneousSubmodule m n R) :
    hallInner m n R (hSub m n R μ) f
      = coeff (shapeContent m μ.1) (f : MvPolynomial (Fin m) R) := by
  have key : hallInner m n R (hSub m n R μ)
      = (Finsupp.lapply μ).comp ((mBasis m n R).repr : _ →ₗ[R] _) := by
    refine (schurBasis m n R).ext fun η => ?_
    simp only [schurBasis_apply, LinearMap.comp_apply, Finsupp.lapply_apply,
      LinearEquiv.coe_coe]
    rw [repr_mBasis_schurSub, hallInner_apply]
    rw [Finset.sum_eq_single η]
    · rw [repr_schurBasis_hSub, ← schurBasis_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same, mul_one]
    · intro ν _ hne
      rw [← schurBasis_apply, Module.Basis.repr_self, Finsupp.single_apply,
        ite_eq_right (fun h => hne h.symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ η) h
  rw [key]
  simp only [LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe]
  rw [repr_mBasis_apply]

/-- The Hall scalar product of `h_μ` with a Schur polynomial is a Kostka number. -/
theorem hallInner_hSub_schurSub [CommRing R] (η μ : PartIdx n m) :
    hallInner m n R (hSub m n R μ) (schurSub m n R η) = (kostka η.1 μ.1 : R) := by
  rw [hallInner_hSub_eq_coeff, ← repr_mBasis_apply, repr_mBasis_schurSub]

/-- **The bases `h` and `m` are dual** for the Hall scalar product. -/
theorem hallInner_hSub_mSub [CommRing R] (η μ : PartIdx n m) :
    hallInner m n R (hSub m n R η) (mSub m n R μ) = if η = μ then 1 else 0 := by
  classical
  rw [hallInner_hSub_eq_coeff, coe_mSub, coeff_monomialSym]
  by_cases h : η = μ
  · subst h
    rw [ite_eq_left (self_mem_degOrbit _), ite_eq_left rfl]
  · rw [ite_eq_right h, ite_eq_right]
    intro hmem
    refine h (Subtype.ext ?_)
    have := degShape_eq_iff.2 (mem_degOrbit_iff.1 hmem)
    rwa [degShape_shapeContent η.2.1 η.2.2.2, degShape_shapeContent μ.2.1 μ.2.2.2] at this

end MvPolynomial
