/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.PowerSum

/-!
# The basis of products of power sums

Following `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove that, over a commutative
ring containing the rationals, the products of power sums

`p_lam = p_{lam_1} * ... * p_{lam_k}`

of the partitions `lam` of `n` with at most `m` parts form a basis of the module of
symmetric homogeneous polynomials of degree `n` in `m` variables.

The proof is the triangularity of the expansion of `p_lam` in the monomial symmetric polynomials
proved in `Mathlib/RingTheory/MvPolynomial/Symmetric/Basis/PowerSum.lean`: only the shapes
dominating `lam` occur, and the leading coefficient is a nonzero natural number, hence invertible in
a `ℚ`-algebra.  (Some invertibility assumption is necessary: already `p_{1,1} = m_{1,1} * 2 + m_2`
in two variables, so the `p_lam` do not form a basis over `ℤ`.)

## Main results

* `MvPolynomial.linearIndependent_pProd` : the `p_lam` are linearly independent.
* `MvPolynomial.span_pProd` : the `p_lam` span the symmetric homogeneous polynomials.
* `MvPolynomial.pBasis` : the resulting basis.
-/

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
    LinearIndependent R fun lam : PartIdx n m => monomialSym m R lam.1 := by
  classical
  rw [linearIndependent_iff']
  intro s g hg lam hlam
  have hcoeff := congrArg (coeff (shapeContent m lam.1)) hg
  rw [coeff_zero, coeff_sum] at hcoeff
  have hsingle : ∀ nu ∈ s, nu ≠ lam →
      coeff (shapeContent m lam.1) (g nu • monomialSym m R nu.1) = 0 := by
    intro nu _ hne
    rw [coeff_smul, smul_eq_mul, coeff_monomialSym, ite_eq_right, mul_zero]
    intro hmem
    refine hne (Subtype.ext ?_)
    have h2 := degShape_eq_iff.2 (mem_degOrbit_iff.1 hmem)
    rw [degShape_shapeContent lam.2.1 lam.2.2.2, degShape_shapeContent nu.2.1 nu.2.2.2] at h2
    exact h2.symm
  rw [Finset.sum_eq_single lam hsingle (fun h => absurd hlam h), coeff_smul, smul_eq_mul,
    coeff_monomialSym_shapeContent, mul_one] at hcoeff
  exact hcoeff

/-- The expansion of `p_lam` in the monomial symmetric polynomials, indexed by
`PartIdx n m`. -/
lemma pProd_eq_sum_partIdx {n : ℕ} (lam : PartIdx n m) :
    pProd m R lam.1
      = ∑ mu : PartIdx n m, (pCoeff m lam.1 mu.1 : R) • monomialSym m R mu.1 := by
  classical
  rw [pProd_eq_sum_monomialSym lam.1, lam.2.2.1, partsFinset,
    Finset.sum_image fun x _ y _ h => Subtype.ext h]

lemma pProd_mem_symHomogeneousSubmodule {n : ℕ} (lam : PartIdx n m) :
    pProd m R lam.1 ∈ symHomogeneousSubmodule m n R := by
  refine ⟨?_, pProd_isSymmetric lam.1⟩
  have h := isHomogeneous_pProd (m := m) (R := R) lam.1
  rwa [lam.2.2.1] at h

/-! ### Linear independence -/

/-- **The products of power sums are linearly independent** over a ring containing the
rationals: the `p_lam` for `lam` a partition of `n` with at most `m` parts. -/
theorem linearIndependent_pProd (m n : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] :
    LinearIndependent R fun lam : PartIdx n m => pProd m R lam.1 := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg lam
  have hexp : ∑ mu : PartIdx n m, g mu • pProd m R mu.1
      = ∑ nu : PartIdx n m,
          (∑ mu : PartIdx n m, g mu * (pCoeff m mu.1 nu.1 : R)) • monomialSym m R nu.1 := by
    simp only [pProd_eq_sum_partIdx, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have hcoef : ∀ nu : PartIdx n m, ∑ mu : PartIdx n m, g mu * (pCoeff m mu.1 nu.1 : R) = 0 :=
    Fintype.linearIndependent_iff.1 (linearIndependent_monomialSym_partIdx m n R) _
      (by rw [← hexp, hg])
  by_contra hne
  obtain ⟨nu, hnut, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun mu : PartIdx n m => g mu ≠ 0) (fun mu => domWeight n mu.1)
    ⟨lam, Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩⟩
  obtain ⟨-, hnu0⟩ := Finset.mem_filter.1 hnut
  have hsingle : ∀ mu ∈ (Finset.univ : Finset (PartIdx n m)), mu ≠ nu →
      g mu * (pCoeff m mu.1 nu.1 : R) = 0 := by
    intro mu _ hmune
    by_cases hgmu : g mu = 0
    · rw [hgmu, zero_mul]
    · have hmut : mu ∈ Finset.univ.filter fun mu : PartIdx n m => g mu ≠ 0 :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hgmu⟩
      have hzero : pCoeff m mu.1 nu.1 = 0 := by
        by_contra hk
        have hdom : Partdom mu.1 nu.1 := partdom_of_pCoeff_ne_zero mu.2.1 nu.2.1 nu.2.2.2
          (by rw [mu.2.2.1, nu.2.2.1]) hk
        exact hmune (Subtype.ext (eq_of_partdom_of_domWeight_eq mu.2.1 nu.2.1 mu.2.2.1
          nu.2.2.1 hdom (hmin mu hmut)))
      rw [hzero, Nat.cast_zero, mul_zero]
  have hzero := hcoef nu
  rw [Finset.sum_eq_single nu hsingle (fun h => absurd (Finset.mem_univ nu) h)] at hzero
  obtain ⟨u, hu⟩ := isUnit_natCast_of_ne_zero (R := R) (pCoeff_self_ne_zero nu.2.2.2)
  refine hnu0 ?_
  have hprod : g nu * (pCoeff m nu.1 nu.1 : R) * ((u⁻¹ : Rˣ) : R) = 0 := by
    rw [hzero, zero_mul]
  rwa [← hu, mul_assoc, u.mul_inv, mul_one] at hprod

/-! ### Spanning -/

/-- Every monomial symmetric polynomial of a partition of `n` with at most `m` parts is a
linear combination of the products of power sums. -/
theorem monomialSym_mem_span_pProd [Algebra ℚ R] (n : ℕ) {lam : List ℕ} (hlam : IsPart lam)
    (hsum : lam.sum = n) (hlen : lam.length ≤ m) :
    monomialSym m R lam
      ∈ Submodule.span R (Set.range fun mu : PartIdx n m => pProd m R mu.1) := by
  classical
  set W := Submodule.span R (Set.range fun mu : PartIdx n m => pProd m R mu.1) with hW
  suffices H : ∀ k : ℕ, ∀ nu : List ℕ, IsPart nu → nu.sum = n → nu.length ≤ m →
      (n + 1) * n - domWeight n nu ≤ k → monomialSym m R nu ∈ W by
    exact H _ lam hlam hsum hlen le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro nu hnu hnusum hnulen hk
    have hexp := pProd_eq_sum_monomialSym (R := R) (m := m) nu
    rw [hnusum] at hexp
    have hmem : nu ∈ partsFinset n m := mem_partsFinset.2 ⟨hnu, hnusum, hnulen⟩
    have hsplit := Finset.add_sum_erase (partsFinset n m)
      (fun mu => (pCoeff m nu mu : R) • monomialSym m R mu) hmem
    have hrest : ∀ mu ∈ (partsFinset n m).erase nu,
        (pCoeff m nu mu : R) • monomialSym m R mu ∈ W := by
      intro mu hmu
      have hmune : mu ≠ nu := Finset.ne_of_mem_erase hmu
      obtain ⟨hmupart, hmusum, hmulen⟩ := mem_partsFinset.1 (Finset.mem_of_mem_erase hmu)
      by_cases hk0 : pCoeff m nu mu = 0
      · rw [hk0, Nat.cast_zero, zero_smul]
        exact Submodule.zero_mem _
      · have hdom : Partdom nu mu :=
          partdom_of_pCoeff_ne_zero hnu hmupart hmulen (by rw [hnusum, hmusum]) hk0
        have hlt : domWeight n nu < domWeight n mu := by
          rcases lt_or_eq_of_le (domWeight_le_domWeight (n := n) hdom) with h | h
          · exact h
          · exact absurd (eq_of_partdom_of_domWeight_eq hnu hmupart hnusum hmusum hdom
              (le_of_eq h.symm)) (Ne.symm hmune)
        have hbd : domWeight n mu ≤ (n + 1) * n := by
          rw [domWeight]
          calc ∑ j ∈ Finset.range (n + 1), (mu.take j).sum
              ≤ ∑ _j ∈ Finset.range (n + 1), n :=
                Finset.sum_le_sum fun j _ => hmusum ▸ sum_take_le_sum mu j
            _ = (n + 1) * n := by simp [mul_comm]
        exact Submodule.smul_mem _ _
          (ih ((n + 1) * n - domWeight n mu) (by omega) mu hmupart hmusum hmulen le_rfl)
    have hkey : (pCoeff m nu nu : R) • monomialSym m R nu
        = pProd m R nu - ∑ mu ∈ (partsFinset n m).erase nu,
            (pCoeff m nu mu : R) • monomialSym m R mu :=
      eq_sub_of_add_eq (hsplit.trans hexp.symm)
    obtain ⟨u, hu⟩ := isUnit_natCast_of_ne_zero (R := R) (pCoeff_self_ne_zero (m := m) hnulen)
    have hu' : ((u⁻¹ : Rˣ) : R) * (pCoeff m nu nu : R) = 1 := by
      rw [← hu]
      exact u.inv_mul
    have hmul : monomialSym m R nu
        = ((u⁻¹ : Rˣ) : R) • ((pCoeff m nu nu : R) • monomialSym m R nu) := by
      rw [smul_smul, hu', one_smul]
    rw [hmul, hkey]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.subset_span ⟨⟨nu, hnu, hnusum, hnulen⟩, rfl⟩) (Submodule.sum_mem _ hrest))

/-- **The products of power sums span** the module of symmetric homogeneous polynomials of
degree `n` in `m` variables, over a ring containing the rationals. -/
theorem span_pProd [Algebra ℚ R] (m n : ℕ) :
    Submodule.span R (Set.range fun lam : PartIdx n m => pProd m R lam.1)
      = symHomogeneousSubmodule m n R := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) fun p hp => ?_
  · rintro q ⟨lam, rfl⟩
    exact pProd_mem_symHomogeneousSubmodule lam
  · obtain ⟨hhom, hsym⟩ := hp
    rw [eq_sum_monomialSym_partsFinset hsym hhom]
    refine Submodule.sum_mem _ fun mu hmu => ?_
    obtain ⟨hmupart, hmusum, hmulen⟩ := mem_partsFinset.1 hmu
    exact Submodule.smul_mem _ _ (monomialSym_mem_span_pProd n hmupart hmusum hmulen)

/-! ### The basis -/

/-- The product `p_lam`, as an element of the module of symmetric homogeneous polynomials
of degree `n`. -/
noncomputable def pSub (m n : ℕ) (R : Type*) [CommRing R] (lam : PartIdx n m) :
    symHomogeneousSubmodule m n R :=
  ⟨pProd m R lam.1, pProd_mem_symHomogeneousSubmodule lam⟩

@[simp] lemma coe_pSub (m n : ℕ) (R : Type*) [CommRing R] (lam : PartIdx n m) :
    (pSub m n R lam : MvPolynomial (Fin m) R) = pProd m R lam.1 := rfl

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
    (lam : PartIdx n m) :
    (pBasis m n R lam : MvPolynomial (Fin m) R) = pProd m R lam.1 := by
  rw [pBasis, Module.Basis.mk_apply, coe_pSub]

end MvPolynomial
