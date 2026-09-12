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

`p_μ = p_{μ_1} * ... * p_{μ_k}`

of the partitions `μ` of `n` with at most `m` parts form a basis of the module of
symmetric homogeneous polynomials of degree `n` in `m` variables.

The proof is the triangularity of the expansion of `p_μ` in the monomial symmetric polynomials
proved in `Mathlib/RingTheory/MvPolynomial/Symmetric/Basis/PowerSum.lean`: only the shapes
dominating `μ` occur, and the leading coefficient is a nonzero natural number, hence invertible in
a `ℚ`-algebra.  (Some invertibility assumption is necessary: already `p_{1,1} = m_{1,1} * 2 + m_2`
in two variables, so the `p_μ` do not form a basis over `ℤ`.)

## Main results

* `MvPolynomial.linearIndependent_pProd` : the `p_μ` are linearly independent.
* `MvPolynomial.span_pProd` : the `p_μ` span the symmetric homogeneous polynomials.
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

lemma linearIndependent_monomialSym_partLengthLe (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R fun μ : PartLengthLe n m => monomialSym m R μ.1 := by
  classical
  rw [linearIndependent_iff']
  intro s g hg μ hμ
  have hcoeff := congrArg (coeff (shapeContent m μ.1)) hg
  rw [coeff_zero, coeff_sum] at hcoeff
  have hsingle : ∀ ν ∈ s, ν ≠ μ →
      coeff (shapeContent m μ.1) (g ν • monomialSym m R ν.1) = 0 := by
    intro ν _ hne
    rw [coeff_smul, smul_eq_mul, coeff_monomialSym, ite_eq_right, mul_zero]
    intro hmem
    refine hne (Subtype.ext ?_)
    have h2 := degShape_eq_iff.2 (mem_degOrbit_iff.1 hmem)
    rw [degShape_shapeContent μ.2.1 μ.2.2.2, degShape_shapeContent ν.2.1 ν.2.2.2] at h2
    exact h2.symm
  rw [Finset.sum_eq_single μ hsingle (fun h => absurd hμ h), coeff_smul, smul_eq_mul,
    coeff_monomialSym_shapeContent, mul_one] at hcoeff
  exact hcoeff

/-- The expansion of `p_μ` in the monomial symmetric polynomials, indexed by
`PartLengthLe n m`. -/
lemma pProd_eq_sum_partLengthLe {n : ℕ} (μ : PartLengthLe n m) :
    pProd m R μ.1
      = ∑ ν : PartLengthLe n m, (pCoeff m μ.1 ν.1 : R) • monomialSym m R ν.1 := by
  classical
  rw [pProd_eq_sum_monomialSym μ.1, μ.2.2.1, partFinsetLengthLe,
    Finset.sum_image fun x _ y _ h => Subtype.ext h]

lemma pProd_mem_symHomogeneousSubmodule {n : ℕ} (μ : PartLengthLe n m) :
    pProd m R μ.1 ∈ symHomogeneousSubmodule m n R := by
  refine ⟨?_, pProd_isSymmetric μ.1⟩
  have h := isHomogeneous_pProd (m := m) (R := R) μ.1
  rwa [μ.2.2.1] at h

/-! ### Linear independence -/

/-- **The products of power sums are linearly independent** over a ring containing the
rationals: the `p_μ` for `μ` a partition of `n` with at most `m` parts. -/
theorem linearIndependent_pProd (m n : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] :
    LinearIndependent R fun μ : PartLengthLe n m => pProd m R μ.1 := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg μ
  have hexp : ∑ ν : PartLengthLe n m, g ν • pProd m R ν.1
      = ∑ ρ : PartLengthLe n m,
          (∑ ν : PartLengthLe n m, g ν * (pCoeff m ν.1 ρ.1 : R)) • monomialSym m R ρ.1 := by
    simp only [pProd_eq_sum_partLengthLe, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have hcoef : ∀ ρ : PartLengthLe n m, ∑ ν : PartLengthLe n m, g ν * (pCoeff m ν.1 ρ.1 : R) = 0 :=
    Fintype.linearIndependent_iff.1 (linearIndependent_monomialSym_partLengthLe m n R) _
      (by rw [← hexp, hg])
  by_contra hne
  obtain ⟨ρ, hρt, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun ν : PartLengthLe n m => g ν ≠ 0) (fun ν => domWeight n ν.1)
    ⟨μ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩⟩
  obtain ⟨-, hρ0⟩ := Finset.mem_filter.1 hρt
  have hsingle : ∀ ν ∈ (Finset.univ : Finset (PartLengthLe n m)), ν ≠ ρ →
      g ν * (pCoeff m ν.1 ρ.1 : R) = 0 := by
    intro ν _ hνne
    by_cases hgmu : g ν = 0
    · rw [hgmu, zero_mul]
    · have hνt : ν ∈ Finset.univ.filter fun ν : PartLengthLe n m => g ν ≠ 0 :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hgmu⟩
      have hzero : pCoeff m ν.1 ρ.1 = 0 := by
        by_contra hk
        have hdom : Partdom ν.1 ρ.1 := partdom_of_pCoeff_ne_zero ν.2.1 ρ.2.1 ρ.2.2.2
          (by rw [ν.2.2.1, ρ.2.2.1]) hk
        exact hνne (Subtype.ext (eq_of_partdom_of_domWeight_eq ν.2.1 ρ.2.1 ν.2.2.1
          ρ.2.2.1 hdom (hmin ν hνt)))
      rw [hzero, Nat.cast_zero, mul_zero]
  have hzero := hcoef ρ
  rw [Finset.sum_eq_single ρ hsingle (fun h => absurd (Finset.mem_univ ρ) h)] at hzero
  obtain ⟨u, hu⟩ := isUnit_natCast_of_ne_zero (R := R) (pCoeff_self_ne_zero ρ.2.2.2)
  refine hρ0 ?_
  have hprod : g ρ * (pCoeff m ρ.1 ρ.1 : R) * ((u⁻¹ : Rˣ) : R) = 0 := by
    rw [hzero, zero_mul]
  rwa [← hu, mul_assoc, u.mul_inv, mul_one] at hprod

/-! ### Spanning -/

/-- Every monomial symmetric polynomial of a partition of `n` with at most `m` parts is a
linear combination of the products of power sums. -/
theorem monomialSym_mem_span_pProd [Algebra ℚ R] (n : ℕ) {μ : List ℕ} (hμ : IsPart μ)
    (hsum : μ.sum = n) (hlen : μ.length ≤ m) :
    monomialSym m R μ
      ∈ Submodule.span R (Set.range fun ν : PartLengthLe n m => pProd m R ν.1) := by
  classical
  set W := Submodule.span R (Set.range fun ν : PartLengthLe n m => pProd m R ν.1) with hW
  suffices H : ∀ k : ℕ, ∀ ρ : List ℕ, IsPart ρ → ρ.sum = n → ρ.length ≤ m →
      (n + 1) * n - domWeight n ρ ≤ k → monomialSym m R ρ ∈ W by
    exact H _ μ hμ hsum hlen le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro ρ hρ hρsum hρlen hk
    have hexp := pProd_eq_sum_monomialSym (R := R) (m := m) ρ
    rw [hρsum] at hexp
    have hmem : ρ ∈ partFinsetLengthLe n m := mem_partFinsetLengthLe.2 ⟨hρ, hρsum, hρlen⟩
    have hsplit := Finset.add_sum_erase (partFinsetLengthLe n m)
      (fun ν => (pCoeff m ρ ν : R) • monomialSym m R ν) hmem
    have hrest : ∀ ν ∈ (partFinsetLengthLe n m).erase ρ,
        (pCoeff m ρ ν : R) • monomialSym m R ν ∈ W := by
      intro ν hν
      have hνne : ν ≠ ρ := Finset.ne_of_mem_erase hν
      obtain ⟨hνpart, hνsum, hνlen⟩ := mem_partFinsetLengthLe.1 (Finset.mem_of_mem_erase hν)
      by_cases hk0 : pCoeff m ρ ν = 0
      · rw [hk0, Nat.cast_zero, zero_smul]
        exact Submodule.zero_mem _
      · have hdom : Partdom ρ ν :=
          partdom_of_pCoeff_ne_zero hρ hνpart hνlen (by rw [hρsum, hνsum]) hk0
        have hlt : domWeight n ρ < domWeight n ν := by
          rcases lt_or_eq_of_le (domWeight_le_domWeight (n := n) hdom) with h | h
          · exact h
          · exact absurd (eq_of_partdom_of_domWeight_eq hρ hνpart hρsum hνsum hdom
              (le_of_eq h.symm)) (Ne.symm hνne)
        have hbd : domWeight n ν ≤ (n + 1) * n := by
          rw [domWeight]
          calc ∑ j ∈ Finset.range (n + 1), (ν.take j).sum
              ≤ ∑ _j ∈ Finset.range (n + 1), n :=
                Finset.sum_le_sum fun j _ => hνsum ▸ sum_take_le_sum ν j
            _ = (n + 1) * n := by simp [mul_comm]
        exact Submodule.smul_mem _ _
          (ih ((n + 1) * n - domWeight n ν) (by omega) ν hνpart hνsum hνlen le_rfl)
    have hkey : (pCoeff m ρ ρ : R) • monomialSym m R ρ
        = pProd m R ρ - ∑ ν ∈ (partFinsetLengthLe n m).erase ρ,
            (pCoeff m ρ ν : R) • monomialSym m R ν :=
      eq_sub_of_add_eq (hsplit.trans hexp.symm)
    obtain ⟨u, hu⟩ := isUnit_natCast_of_ne_zero (R := R) (pCoeff_self_ne_zero (m := m) hρlen)
    have hu' : ((u⁻¹ : Rˣ) : R) * (pCoeff m ρ ρ : R) = 1 := by
      rw [← hu]
      exact u.inv_mul
    have hmul : monomialSym m R ρ
        = ((u⁻¹ : Rˣ) : R) • ((pCoeff m ρ ρ : R) • monomialSym m R ρ) := by
      rw [smul_smul, hu', one_smul]
    rw [hmul, hkey]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.subset_span ⟨⟨ρ, hρ, hρsum, hρlen⟩, rfl⟩) (Submodule.sum_mem _ hrest))

/-- **The products of power sums span** the module of symmetric homogeneous polynomials of
degree `n` in `m` variables, over a ring containing the rationals. -/
theorem span_pProd [Algebra ℚ R] (m n : ℕ) :
    Submodule.span R (Set.range fun μ : PartLengthLe n m => pProd m R μ.1)
      = symHomogeneousSubmodule m n R := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) fun p hp => ?_
  · rintro q ⟨μ, rfl⟩
    exact pProd_mem_symHomogeneousSubmodule μ
  · obtain ⟨hhom, hsym⟩ := hp
    rw [eq_sum_monomialSym_partFinsetLengthLe hsym hhom]
    refine Submodule.sum_mem _ fun ν hν => ?_
    obtain ⟨hνpart, hνsum, hνlen⟩ := mem_partFinsetLengthLe.1 hν
    exact Submodule.smul_mem _ _ (monomialSym_mem_span_pProd n hνpart hνsum hνlen)

/-! ### The basis -/

/-- The product `p_μ`, as an element of the module of symmetric homogeneous polynomials
of degree `n`. -/
noncomputable def pSub (m n : ℕ) (R : Type*) [CommRing R] (μ : PartLengthLe n m) :
    symHomogeneousSubmodule m n R :=
  ⟨pProd m R μ.1, pProd_mem_symHomogeneousSubmodule μ⟩

@[simp] lemma coe_pSub (m n : ℕ) (R : Type*) [CommRing R] (μ : PartLengthLe n m) :
    (pSub m n R μ : MvPolynomial (Fin m) R) = pProd m R μ.1 := rfl

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
    Module.Basis (PartLengthLe n m) R (symHomogeneousSubmodule m n R) :=
  Module.Basis.mk (linearIndependent_pSub m n R) (span_pSub m n R)

@[simp] lemma coe_pBasis (m n : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R]
    (μ : PartLengthLe n m) :
    (pBasis m n R μ : MvPolynomial (Fin m) R) = pProd m R μ.1 := by
  rw [pBasis, Module.Basis.mk_apply, coe_pSub]

end MvPolynomial
