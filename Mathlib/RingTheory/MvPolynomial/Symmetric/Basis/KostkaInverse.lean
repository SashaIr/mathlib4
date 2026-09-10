/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.CompleteHomogeneous

/-!
# Inverse Kostka numbers

A Lean 4 port of the inverse Kostka numbers `'K^-1(la, μ)` of `theories/MPoly/Schur_altdef.v`
from [Coq-Combi](https://github.com/math-comp/Coq-Combi).

The Kostka numbers give the expansion `h_μ = ∑_nu K_{ν μ} s_ν` of a product of complete
homogeneous symmetric polynomials in the Schur basis
(`MvPolynomial.hProd_eq_sum_kostka`).  Since `K_{ν μ}` vanishes unless `μ` is dominated
by `ν`, and `K_{μ μ} = 1`, the Kostka matrix is unitriangular for the dominance order,
hence invertible over `ℤ`.  Its inverse is the matrix of the *inverse Kostka numbers*, and
it expands a Schur polynomial in the products of complete homogeneous symmetric
polynomials.

## Main definitions

* `MvPolynomial.kostkaInv n η μ` : the inverse Kostka number `K⁻¹_{η μ}`, that is, the
  coefficient of `h_μ` in the expansion of the Schur polynomial `s_η`.

## Main results

* `MvPolynomial.sum_kostka_mul_kostkaInv` : the two matrices are inverse to each other.
* `MvPolynomial.partdom_of_kostkaInv_ne_zero`, `MvPolynomial.kostkaInv_self` : the inverse
  Kostka matrix is again unitriangular for the dominance order.
* `MvPolynomial.schurPoly_eq_sum_kostkaInv` : `s_η = ∑_mu K⁻¹_{η μ} h_μ`, over any
  commutative ring and in any number of variables.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {n : ℕ} {R : Type*}

/-! ### Partitions of `n`, as an index type and as a finite set of lists -/

/-- A partition of `n`, as an element of the index type `PartIdx n n`. -/
def partIdxOfMem {η : List ℕ} (hη : IsPart η) (hsum : η.sum = n) : PartIdx n n :=
  ⟨η, hη, hsum, hsum ▸ hη.length_le_sum⟩

@[simp] lemma partIdxOfMem_val {η : List ℕ} (hη : IsPart η) (hsum : η.sum = n) :
    (partIdxOfMem hη hsum).1 = η := rfl

/-! ### The Kostka matrix as a change of basis -/

/-- The matrix of the basis of Schur polynomials against the basis of the products of
complete homogeneous symmetric polynomials is the Kostka matrix. -/
lemma schurBasis_toMatrix_hBasis (ν μ : PartIdx n n) :
    (schurBasis n n ℤ).toMatrix (hBasis n n ℤ) ν μ = (kostka ν.1 μ.1 : ℤ) := by
  have hexp : hBasis n n ℤ μ
      = ∑ ν' : PartIdx n n, (kostka ν'.1 μ.1 : ℤ) • schurBasis n n ℤ ν' := by
    refine Subtype.ext ?_
    rw [coe_hBasis, hProd_eq_sum_partIdx μ]
    push_cast
    exact Finset.sum_congr rfl fun ν' _ => by rw [coe_schurBasis]
  rw [Module.Basis.toMatrix_apply, hexp, map_sum]
  simp [Finsupp.single_apply, eq_comm]

/-! ### The inverse Kostka numbers -/

/-- The inverse Kostka number `K⁻¹_{η μ}`: the coefficient of `h_μ` in the expansion of
the Schur polynomial `s_η` in the products of complete homogeneous symmetric polynomials.
It is zero unless both `η` and `μ` are partitions of `n`. -/
noncomputable def kostkaInv (n : ℕ) (η μ : List ℕ) : ℤ :=
  if hη : IsPart η ∧ η.sum = n then
    if hμ : IsPart μ ∧ μ.sum = n then
      (hBasis n n ℤ).toMatrix (schurBasis n n ℤ) (partIdxOfMem hμ.1 hμ.2)
        (partIdxOfMem hη.1 hη.2)
    else 0
  else 0

lemma kostkaInv_apply (η μ : PartIdx n n) :
    kostkaInv n η.1 μ.1 = (hBasis n n ℤ).toMatrix (schurBasis n n ℤ) μ η := by
  rw [kostkaInv, dite_eq_left ⟨η.2.1, η.2.2.1⟩, dite_eq_left ⟨μ.2.1, μ.2.2.1⟩]
  rfl

lemma kostkaInv_eq_zero_of_left {η μ : List ℕ} (h : ¬ (IsPart η ∧ η.sum = n)) :
    kostkaInv n η μ = 0 := by
  rw [kostkaInv, dite_eq_right h]

lemma kostkaInv_eq_zero_of_right {η μ : List ℕ} (h : ¬ (IsPart μ ∧ μ.sum = n)) :
    kostkaInv n η μ = 0 := by
  simp only [kostkaInv, dite_eq_right h, dite_eq_ite, ite_self]

/-! ### Orthogonality -/

/-- **The Kostka matrix and the inverse Kostka matrix are inverse to each other**, in the
form indexed by `PartIdx n n`. -/
theorem sum_kostka_mul_kostkaInv_partIdx (ν η : PartIdx n n) :
    ∑ μ : PartIdx n n, (kostka ν.1 μ.1 : ℤ) * kostkaInv n η.1 μ.1
      = if ν = η then 1 else 0 := by
  have h := congrFun (congrFun
    (Module.Basis.toMatrix_mul_toMatrix_flip (schurBasis n n ℤ) (hBasis n n ℤ)) ν) η
  rw [Matrix.mul_apply] at h
  simp only [schurBasis_toMatrix_hBasis, ← kostkaInv_apply, Matrix.one_apply] at h
  exact h

/-- **The Kostka matrix and the inverse Kostka matrix are inverse to each other.** -/
theorem sum_kostka_mul_kostkaInv {ν η : List ℕ} (hν : IsPart ν) (hνsum : ν.sum = n)
    (hη : IsPart η) (hηsum : η.sum = n) :
    ∑ μ ∈ partFinset n, (kostka ν μ : ℤ) * kostkaInv n η μ
      = if ν = η then 1 else 0 := by
  rw [sum_partFinset_eq_sum_partIdx (m := n) le_rfl]
  have hkey := sum_kostka_mul_kostkaInv_partIdx (partIdxOfMem hν hνsum)
    (partIdxOfMem hη hηsum)
  simp only [partIdxOfMem_val] at hkey
  rw [hkey]
  exact if_congr ⟨fun hh => congrArg Subtype.val hh, fun hh => Subtype.ext hh⟩ rfl rfl

/-! ### Unitriangularity of the inverse Kostka matrix -/

/-- An inverse Kostka number `K⁻¹_{η μ}` is nonzero only if `η` is dominated by
`μ`. -/
theorem partdom_of_kostkaInv_ne_zero {η μ : List ℕ} (h : kostkaInv n η μ ≠ 0) :
    Partdom η μ := by
  classical
  by_cases hη : IsPart η ∧ η.sum = n
  swap
  · exact absurd (kostkaInv_eq_zero_of_left hη) h
  by_cases hμ : IsPart μ ∧ μ.sum = n
  swap
  · exact absurd (kostkaInv_eq_zero_of_right hμ) h
  by_contra hdom
  set T := Finset.univ.filter
    (fun k : PartIdx n n => kostkaInv n η k.1 ≠ 0 ∧ ¬ Partdom η k.1) with hT
  have hTne : T.Nonempty := ⟨partIdxOfMem hμ.1 hμ.2, by simp [hT, h, hdom]⟩
  obtain ⟨k, hkT, hkmin⟩ := Finset.exists_min_image T (fun k => domWeight n k.1) hTne
  obtain ⟨-, hk0, hkdom⟩ := Finset.mem_filter.1 hkT
  have hkne : k ≠ partIdxOfMem hη.1 hη.2 := fun he => hkdom (he ▸ Partdom.refl η)
  have horth := sum_kostka_mul_kostkaInv_partIdx k (partIdxOfMem hη.1 hη.2)
  simp only [partIdxOfMem_val] at horth
  rw [ite_eq_right hkne] at horth
  have hsingle : ∀ μ' ∈ (Finset.univ : Finset (PartIdx n n)), μ' ≠ k →
      (kostka k.1 μ'.1 : ℤ) * kostkaInv n η μ'.1 = 0 := by
    intro μ' _ hne
    by_cases hB : kostkaInv n η μ'.1 = 0
    · rw [hB, mul_zero]
    by_cases hK : kostka k.1 μ'.1 = 0
    · rw [hK, Nat.cast_zero, zero_mul]
    have hmk : Partdom μ'.1 k.1 := partdom_of_kostka_ne_zero hK
    have hmT : μ' ∈ T :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hB, fun hcon => hkdom (hcon.trans hmk)⟩
    have hle : domWeight n k.1 ≤ domWeight n μ'.1 := hkmin μ' hmT
    exact absurd (Subtype.ext (eq_of_partdom_of_domWeight_eq μ'.2.1 k.2.1 μ'.2.2.1 k.2.2.1
      hmk hle)) hne
  rw [Finset.sum_eq_single k hsingle (fun hcon => absurd (Finset.mem_univ k) hcon),
    kostka_self k.2.1, Nat.cast_one, one_mul] at horth
  exact hk0 horth

/-- The diagonal inverse Kostka numbers are `1`. -/
theorem kostkaInv_self {η : List ℕ} (hη : IsPart η) (hsum : η.sum = n) :
    kostkaInv n η η = 1 := by
  classical
  have horth := sum_kostka_mul_kostkaInv_partIdx (partIdxOfMem hη hsum)
    (partIdxOfMem hη hsum)
  simp only [partIdxOfMem_val, ite_true] at horth
  have hsingle : ∀ μ' ∈ (Finset.univ : Finset (PartIdx n n)), μ' ≠ partIdxOfMem hη hsum →
      (kostka η μ'.1 : ℤ) * kostkaInv n η μ'.1 = 0 := by
    intro μ' _ hne
    by_cases hB : kostkaInv n η μ'.1 = 0
    · rw [hB, mul_zero]
    by_cases hK : kostka η μ'.1 = 0
    · rw [hK, Nat.cast_zero, zero_mul]
    exact absurd (Subtype.ext (Partdom.antisymm μ'.2.1 hη (partdom_of_kostka_ne_zero hK)
      (partdom_of_kostkaInv_ne_zero hB))) hne
  rw [Finset.sum_eq_single (partIdxOfMem hη hsum) hsingle
    (fun hcon => absurd (Finset.mem_univ (partIdxOfMem hη hsum)) hcon)] at horth
  simp only [partIdxOfMem_val] at horth
  rwa [kostka_self hη, Nat.cast_one, one_mul] at horth

/-! ### The expansion of a Schur polynomial -/

/-- **The expansion of a Schur polynomial in the products of complete homogeneous symmetric
polynomials**, `s_η = ∑_mu K⁻¹_{η μ} h_μ`. -/
theorem schurPoly_eq_sum_kostkaInv [CommRing R] (m : ℕ) {η : List ℕ} (hη : IsPart η)
    (hsum : η.sum = n) :
    schurPoly (Fin m) R η
      = ∑ μ ∈ partFinset n, (kostkaInv n η μ : R) • hProd m R μ := by
  classical
  rw [sum_partFinset_eq_sum_partIdx (m := n) le_rfl]
  have hh : ∀ μ : PartIdx n n, hProd m R μ.1
      = ∑ ν : PartIdx n n, (kostka ν.1 μ.1 : R) • schurPoly (Fin m) R ν.1 := by
    intro μ
    rw [hProd_eq_sum_kostka m μ.2.1, μ.2.2.1, sum_partFinset_eq_sum_partIdx (m := n) le_rfl]
  simp_rw [hh, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hcoef : ∀ ν : PartIdx n n,
      ∑ μ : PartIdx n n, (kostkaInv n η μ.1 : R) * (kostka ν.1 μ.1 : R)
        = if ν = partIdxOfMem hη hsum then 1 else 0 := by
    intro ν
    have := congrArg (fun z : ℤ => (z : R))
      (sum_kostka_mul_kostkaInv_partIdx ν (partIdxOfMem hη hsum))
    push_cast at this
    rw [← this]
    exact Finset.sum_congr rfl fun μ _ => mul_comm _ _
  simp_rw [hcoef, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ (partIdxOfMem hη hsum)
    (fun ν : PartIdx n n => schurPoly (Fin m) R ν.1)]
  simp

end MvPolynomial
