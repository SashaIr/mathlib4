/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.PowerSum

/-!
# The basis of products of power sums

Following `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove that, over a commutative
ring containing the rationals, the products of power sums

`p_η = p_{η_1} * ... * p_{η_k}`

of the partitions `η` of `n` with at most `m` parts form a basis of the module of
symmetric homogeneous polynomials of degree `n` in `m` variables.

The proof is the triangularity of the expansion of `p_η` in the monomial symmetric polynomials
proved in `Mathlib/RingTheory/MvPolynomial/Symmetric/Basis/PowerSum.lean`: only the shapes
dominating `η` occur, and the leading coefficient is a nonzero natural number, hence invertible in
a `ℚ`-algebra.  (Some invertibility assumption is necessary: already `p_{1,1} = m_{1,1} * 2 + m_2`
in two variables, so the `p_η` do not form a basis over `ℤ`.)

## Main results

* `MvPolynomial.linearIndependent_pProd` : the `p_η` are linearly independent.
* `MvPolynomial.span_pProd` : the `p_η` span the symmetric homogeneous polynomials.
* `MvPolynomial.pBasis` : the resulting basis.
-/

@[expose] public section

open Young

open List

namespace MvPolynomial

open MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### Preliminaries -/

/-- In a `ℚ`-algebra, a nonzero natural number is invertible. -/
lemma isUnit_natCast_of_ne_zero [Algebra ℚ R] {c : ℕ} (hc : c ≠ 0) : IsUnit (c : R) := by
  have h1 : IsUnit ((c : ℚ)) := (Nat.cast_ne_zero.2 hc).isUnit
  have h2 := h1.map (algebraMap ℚ R)
  rwa [map_natCast] at h2

lemma linearIndependent_monomialSym_partIdx (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R fun η : PartIdx n m => monomialSym m R η.1 := by
  classical
  rw [linearIndependent_iff']
  intro s g hg η hη
  have hcoeff := congrArg (coeff (shapeContent m η.1)) hg
  rw [coeff_zero, coeff_sum] at hcoeff
  have hsingle : ∀ ν ∈ s, ν ≠ η →
      coeff (shapeContent m η.1) (g ν • monomialSym m R ν.1) = 0 := by
    intro ν _ hne
    rw [coeff_smul, smul_eq_mul, coeff_monomialSym, ite_eq_right, mul_zero]
    intro hmem
    refine hne (Subtype.ext ?_)
    have h2 := degShape_eq_iff.2 (mem_degOrbit_iff.1 hmem)
    rw [degShape_shapeContent η.2.1 η.2.2.2, degShape_shapeContent ν.2.1 ν.2.2.2] at h2
    exact h2.symm
  rw [Finset.sum_eq_single η hsingle (fun h => absurd hη h), coeff_smul, smul_eq_mul,
    coeff_monomialSym_shapeContent, mul_one] at hcoeff
  exact hcoeff

/-- The expansion of `p_η` in the monomial symmetric polynomials, indexed by
`PartIdx n m`. -/
lemma pProd_eq_sum_partIdx {n : ℕ} (η : PartIdx n m) :
    pProd m R η.1
      = ∑ μ : PartIdx n m, (pCoeff m η.1 μ.1 : R) • monomialSym m R μ.1 := by
  classical
  rw [pProd_eq_sum_monomialSym η.1, η.2.2.1, partsFinset,
    Finset.sum_image fun x _ y _ h => Subtype.ext h]

lemma pProd_mem_symHomogeneousSubmodule {n : ℕ} (η : PartIdx n m) :
    pProd m R η.1 ∈ symHomogeneousSubmodule m n R := by
  refine ⟨?_, pProd_isSymmetric η.1⟩
  have h := isHomogeneous_pProd (m := m) (R := R) η.1
  rwa [η.2.2.1] at h

/-! ### Linear independence -/

/-- **The products of power sums are linearly independent** over a ring containing the
rationals: the `p_η` for `η` a partition of `n` with at most `m` parts. -/
theorem linearIndependent_pProd (m n : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] :
    LinearIndependent R fun η : PartIdx n m => pProd m R η.1 := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg η
  have hexp : ∑ μ : PartIdx n m, g μ • pProd m R μ.1
      = ∑ ν : PartIdx n m,
          (∑ μ : PartIdx n m, g μ * (pCoeff m μ.1 ν.1 : R)) • monomialSym m R ν.1 := by
    simp only [pProd_eq_sum_partIdx, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have hcoef : ∀ ν : PartIdx n m, ∑ μ : PartIdx n m, g μ * (pCoeff m μ.1 ν.1 : R) = 0 :=
    Fintype.linearIndependent_iff.1 (linearIndependent_monomialSym_partIdx m n R) _
      (by rw [← hexp, hg])
  by_contra hne
  obtain ⟨ν, hνt, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun μ : PartIdx n m => g μ ≠ 0) (fun μ => domWeight n μ.1)
    ⟨η, Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩⟩
  obtain ⟨-, hν0⟩ := Finset.mem_filter.1 hνt
  have hsingle : ∀ μ ∈ (Finset.univ : Finset (PartIdx n m)), μ ≠ ν →
      g μ * (pCoeff m μ.1 ν.1 : R) = 0 := by
    intro μ _ hμne
    by_cases hgmu : g μ = 0
    · rw [hgmu, zero_mul]
    · have hμt : μ ∈ Finset.univ.filter fun μ : PartIdx n m => g μ ≠ 0 :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hgmu⟩
      have hzero : pCoeff m μ.1 ν.1 = 0 := by
        by_contra hk
        have hdom : Partdom μ.1 ν.1 := partdom_of_pCoeff_ne_zero μ.2.1 ν.2.1 ν.2.2.2
          (by rw [μ.2.2.1, ν.2.2.1]) hk
        exact hμne (Subtype.ext (eq_of_partdom_of_domWeight_eq μ.2.1 ν.2.1 μ.2.2.1
          ν.2.2.1 hdom (hmin μ hμt)))
      rw [hzero, Nat.cast_zero, mul_zero]
  have hzero := hcoef ν
  rw [Finset.sum_eq_single ν hsingle (fun h => absurd (Finset.mem_univ ν) h)] at hzero
  obtain ⟨u, hu⟩ := isUnit_natCast_of_ne_zero (R := R) (pCoeff_self_ne_zero ν.2.2.2)
  refine hν0 ?_
  have hprod : g ν * (pCoeff m ν.1 ν.1 : R) * ((u⁻¹ : Rˣ) : R) = 0 := by
    rw [hzero, zero_mul]
  rwa [← hu, mul_assoc, u.mul_inv, mul_one] at hprod

/-! ### Spanning -/

/-- Every monomial symmetric polynomial of a partition of `n` with at most `m` parts is a
linear combination of the products of power sums. -/
theorem monomialSym_mem_span_pProd [Algebra ℚ R] (n : ℕ) {η : List ℕ} (hη : IsPart η)
    (hsum : η.sum = n) (hlen : η.length ≤ m) :
    monomialSym m R η
      ∈ Submodule.span R (Set.range fun μ : PartIdx n m => pProd m R μ.1) := by
  classical
  set W := Submodule.span R (Set.range fun μ : PartIdx n m => pProd m R μ.1) with hW
  suffices H : ∀ k : ℕ, ∀ ν : List ℕ, IsPart ν → ν.sum = n → ν.length ≤ m →
      (n + 1) * n - domWeight n ν ≤ k → monomialSym m R ν ∈ W by
    exact H _ η hη hsum hlen le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro ν hν hνsum hνlen hk
    have hexp := pProd_eq_sum_monomialSym (R := R) (m := m) ν
    rw [hνsum] at hexp
    have hmem : ν ∈ partsFinset n m := mem_partsFinset.2 ⟨hν, hνsum, hνlen⟩
    have hsplit := Finset.add_sum_erase (partsFinset n m)
      (fun μ => (pCoeff m ν μ : R) • monomialSym m R μ) hmem
    have hrest : ∀ μ ∈ (partsFinset n m).erase ν,
        (pCoeff m ν μ : R) • monomialSym m R μ ∈ W := by
      intro μ hμ
      have hμne : μ ≠ ν := Finset.ne_of_mem_erase hμ
      obtain ⟨hμpart, hμsum, hμlen⟩ := mem_partsFinset.1 (Finset.mem_of_mem_erase hμ)
      by_cases hk0 : pCoeff m ν μ = 0
      · rw [hk0, Nat.cast_zero, zero_smul]
        exact Submodule.zero_mem _
      · have hdom : Partdom ν μ :=
          partdom_of_pCoeff_ne_zero hν hμpart hμlen (by rw [hνsum, hμsum]) hk0
        have hlt : domWeight n ν < domWeight n μ := by
          rcases lt_or_eq_of_le (domWeight_le_domWeight (n := n) hdom) with h | h
          · exact h
          · exact absurd (eq_of_partdom_of_domWeight_eq hν hμpart hνsum hμsum hdom
              (le_of_eq h.symm)) (Ne.symm hμne)
        have hbd : domWeight n μ ≤ (n + 1) * n := by
          rw [domWeight]
          calc ∑ j ∈ Finset.range (n + 1), (μ.take j).sum
              ≤ ∑ _j ∈ Finset.range (n + 1), n :=
                Finset.sum_le_sum fun j _ => hμsum ▸ sum_take_le_sum μ j
            _ = (n + 1) * n := by simp [mul_comm]
        exact Submodule.smul_mem _ _
          (ih ((n + 1) * n - domWeight n μ) (by omega) μ hμpart hμsum hμlen le_rfl)
    have hkey : (pCoeff m ν ν : R) • monomialSym m R ν
        = pProd m R ν - ∑ μ ∈ (partsFinset n m).erase ν,
            (pCoeff m ν μ : R) • monomialSym m R μ :=
      eq_sub_of_add_eq (hsplit.trans hexp.symm)
    obtain ⟨u, hu⟩ := isUnit_natCast_of_ne_zero (R := R) (pCoeff_self_ne_zero (m := m) hνlen)
    have hu' : ((u⁻¹ : Rˣ) : R) * (pCoeff m ν ν : R) = 1 := by
      rw [← hu]
      exact u.inv_mul
    have hmul : monomialSym m R ν
        = ((u⁻¹ : Rˣ) : R) • ((pCoeff m ν ν : R) • monomialSym m R ν) := by
      rw [smul_smul, hu', one_smul]
    rw [hmul, hkey]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.subset_span ⟨⟨ν, hν, hνsum, hνlen⟩, rfl⟩) (Submodule.sum_mem _ hrest))

/-- **The products of power sums span** the module of symmetric homogeneous polynomials of
degree `n` in `m` variables, over a ring containing the rationals. -/
theorem span_pProd [Algebra ℚ R] (m n : ℕ) :
    Submodule.span R (Set.range fun η : PartIdx n m => pProd m R η.1)
      = symHomogeneousSubmodule m n R := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) fun p hp => ?_
  · rintro q ⟨η, rfl⟩
    exact pProd_mem_symHomogeneousSubmodule η
  · obtain ⟨hhom, hsym⟩ := hp
    rw [eq_sum_monomialSym_partsFinset hsym hhom]
    refine Submodule.sum_mem _ fun μ hμ => ?_
    obtain ⟨hμpart, hμsum, hμlen⟩ := mem_partsFinset.1 hμ
    exact Submodule.smul_mem _ _ (monomialSym_mem_span_pProd n hμpart hμsum hμlen)

/-! ### The basis -/

/-- The product `p_η`, as an element of the module of symmetric homogeneous polynomials
of degree `n`. -/
noncomputable def pSub (m n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n m) :
    symHomogeneousSubmodule m n R :=
  ⟨pProd m R η.1, pProd_mem_symHomogeneousSubmodule η⟩

@[simp] lemma coe_pSub (m n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n m) :
    (pSub m n R η : MvPolynomial (Fin m) R) = pProd m R η.1 := rfl

lemma linearIndependent_pSub (m n : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] :
    LinearIndependent R (pSub m n R) :=
  LinearIndependent.of_comp (symHomogeneousSubmodule m n R).subtype
    (linearIndependent_pProd m n R)

lemma span_pSub (m n : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] :
    ⊤ ≤ Submodule.span R (Set.range (pSub m n R)) := by
  intro p _
  have hmap : Submodule.map (symHomogeneousSubmodule m n R).subtype
      (Submodule.span R (Set.range (pSub m n R))) = symHomogeneousSubmodule m n R := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact span_pProd m n
  have hp : (p : MvPolynomial (Fin m) R) ∈ Submodule.map
      (symHomogeneousSubmodule m n R).subtype
      (Submodule.span R (Set.range (pSub m n R))) := by
    rw [hmap]
    exact p.2
  obtain ⟨q, hq, hqp⟩ := hp
  have hqp' : q = p := Subtype.ext hqp
  rwa [hqp'] at hq

/-- **The products of power sums form a basis** of the module of symmetric homogeneous
polynomials of degree `n` in `m` variables over a ring containing the rationals, indexed
by the partitions of `n` with at most `m` parts. -/
noncomputable def pBasis (m n : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] :
    Module.Basis (PartIdx n m) R (symHomogeneousSubmodule m n R) :=
  Module.Basis.mk (linearIndependent_pSub m n R) (span_pSub m n R)

@[simp] lemma coe_pBasis (m n : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R]
    (η : PartIdx n m) :
    (pBasis m n R η : MvPolynomial (Fin m) R) = pProd m R η.1 := by
  rw [pBasis, Module.Basis.mk_apply, coe_pSub]

end MvPolynomial
