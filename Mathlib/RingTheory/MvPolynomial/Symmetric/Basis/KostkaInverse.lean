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

A Lean 4 port of the inverse Kostka numbers `'K^-1(la, ν)` of `theories/MPoly/Schur_altdef.v`
from [Coq-Combi](https://github.com/math-comp/Coq-Combi).

The Kostka numbers give the expansion `h_ν = ∑_ρ K_{ρ ν} s_ρ` of a product of complete
homogeneous symmetric polynomials in the Schur basis
(`MvPolynomial.hProd_eq_sum_kostka`).  Since `K_{ρ ν}` vanishes unless `ν` is dominated
by `ρ`, and `K_{ν ν} = 1`, the Kostka matrix is unitriangular for the dominance order,
hence invertible over `ℤ`.  Its inverse is the matrix of the *inverse Kostka numbers*, and
it expands a Schur polynomial in the products of complete homogeneous symmetric
polynomials.

## Main definitions

* `MvPolynomial.kostkaInv n μ ν` : the inverse Kostka number `K⁻¹_{μ ν}`, that is, the
  coefficient of `h_ν` in the expansion of the Schur polynomial `s_μ`.

## Main results

* `MvPolynomial.sum_kostka_mul_kostkaInv` : the two matrices are inverse to each other.
* `MvPolynomial.partdom_of_kostkaInv_ne_zero`, `MvPolynomial.kostkaInv_self` : the inverse
  Kostka matrix is again unitriangular for the dominance order.
* `MvPolynomial.schurPoly_eq_sum_kostkaInv` : `s_μ = ∑_ν K⁻¹_{μ ν} h_ν`, over any
  commutative ring and in any number of variables.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {n : ℕ} {R : Type*}

/-! ### The Kostka matrix as a change of basis -/

/-- The matrix of the basis of Schur polynomials against the basis of the products of
complete homogeneous symmetric polynomials is the Kostka matrix. -/
lemma schurBasis_toMatrix_hBasis (ν μ : PartLengthLe n n) :
    (schurBasis n n ℤ).toMatrix (hBasis n n ℤ) ν μ = (kostka ν.1 μ.1 : ℤ) := by
  have hexp : hBasis n n ℤ μ
      = ∑ ν' : PartLengthLe n n, (kostka ν'.1 μ.1 : ℤ) • schurBasis n n ℤ ν' := by
    refine Subtype.ext ?_
    rw [coe_hBasis, hProd_eq_sum_partLengthLe μ]
    push_cast
    exact Finset.sum_congr rfl fun ν' _ => by rw [coe_schurBasis]
  rw [Module.Basis.toMatrix_apply, hexp, map_sum]
  simp [Finsupp.single_apply, eq_comm]

/-! ### The inverse Kostka numbers -/

/-- The inverse Kostka number `K⁻¹_{μ ν}`: the coefficient of `h_ν` in the expansion of
the Schur polynomial `s_μ` in the products of complete homogeneous symmetric polynomials.
It is zero unless both `μ` and `ν` are partitions of `n`. -/
noncomputable def kostkaInv (n : ℕ) (μ ν : List ℕ) : ℤ :=
  if hμ : IsPart μ ∧ μ.sum = n then
    if hν : IsPart ν ∧ ν.sum = n then
      (hBasis n n ℤ).toMatrix (schurBasis n n ℤ) (PartLengthLe.ofList hν.1 hν.2)
        (PartLengthLe.ofList hμ.1 hμ.2)
    else 0
  else 0

lemma kostkaInv_apply (μ ν : PartLengthLe n n) :
    kostkaInv n μ.1 ν.1 = (hBasis n n ℤ).toMatrix (schurBasis n n ℤ) ν μ := by
  rw [kostkaInv, dite_eq_left ⟨μ.2.1, μ.2.2.1⟩, dite_eq_left ⟨ν.2.1, ν.2.2.1⟩]
  rfl

lemma kostkaInv_eq_zero_of_left {μ ν : List ℕ} (h : ¬ (IsPart μ ∧ μ.sum = n)) :
    kostkaInv n μ ν = 0 := by
  rw [kostkaInv, dite_eq_right h]

lemma kostkaInv_eq_zero_of_right {μ ν : List ℕ} (h : ¬ (IsPart ν ∧ ν.sum = n)) :
    kostkaInv n μ ν = 0 := by
  simp only [kostkaInv, dite_eq_right h, dite_eq_ite, ite_self]

/-! ### Orthogonality -/

/-- **The Kostka matrix and the inverse Kostka matrix are inverse to each other**, in the
form indexed by `PartLengthLe n n`. -/
theorem sum_kostka_mul_kostkaInv_partLengthLe (ρ μ : PartLengthLe n n) :
    ∑ ν : PartLengthLe n n, (kostka ρ.1 ν.1 : ℤ) * kostkaInv n μ.1 ν.1
      = if ρ = μ then 1 else 0 := by
  have h := congrFun (congrFun
    (Module.Basis.toMatrix_mul_toMatrix_flip (schurBasis n n ℤ) (hBasis n n ℤ)) ρ) μ
  rw [Matrix.mul_apply] at h
  simp only [schurBasis_toMatrix_hBasis, ← kostkaInv_apply, Matrix.one_apply] at h
  exact h

/-- **The Kostka matrix and the inverse Kostka matrix are inverse to each other.** -/
theorem sum_kostka_mul_kostkaInv {ρ μ : List ℕ} (hρ : IsPart ρ) (hρsum : ρ.sum = n)
    (hμ : IsPart μ) (hμsum : μ.sum = n) :
    ∑ ν ∈ partFinset n, (kostka ρ ν : ℤ) * kostkaInv n μ ν
      = if ρ = μ then 1 else 0 := by
  rw [sum_partFinset_eq_sum_partLengthLe (m := n) le_rfl]
  have hkey := sum_kostka_mul_kostkaInv_partLengthLe (PartLengthLe.ofList hρ hρsum)
    (PartLengthLe.ofList hμ hμsum)
  simp only [PartLengthLe.ofList_val] at hkey
  rw [hkey]
  exact if_congr ⟨fun hh => congrArg Subtype.val hh, fun hh => Subtype.ext hh⟩ rfl rfl

/-! ### Unitriangularity of the inverse Kostka matrix -/

/-- An inverse Kostka number `K⁻¹_{μ ν}` is nonzero only if `μ` is dominated by
`ν`. -/
theorem partdom_of_kostkaInv_ne_zero {μ ν : List ℕ} (h : kostkaInv n μ ν ≠ 0) :
    Partdom μ ν := by
  classical
  by_cases hμ : IsPart μ ∧ μ.sum = n
  swap
  · exact absurd (kostkaInv_eq_zero_of_left hμ) h
  by_cases hν : IsPart ν ∧ ν.sum = n
  swap
  · exact absurd (kostkaInv_eq_zero_of_right hν) h
  by_contra hdom
  set T := Finset.univ.filter
    (fun k : PartLengthLe n n => kostkaInv n μ k.1 ≠ 0 ∧ ¬ Partdom μ k.1) with hT
  have hTne : T.Nonempty := ⟨PartLengthLe.ofList hν.1 hν.2, by simp [hT, h, hdom]⟩
  obtain ⟨k, hkT, hkmin⟩ := Finset.exists_min_image T (fun k => domWeight n k.1) hTne
  obtain ⟨-, hk0, hkdom⟩ := Finset.mem_filter.1 hkT
  have hkne : k ≠ PartLengthLe.ofList hμ.1 hμ.2 := fun he => hkdom (he ▸ Partdom.refl μ)
  have horth := sum_kostka_mul_kostkaInv_partLengthLe k (PartLengthLe.ofList hμ.1 hμ.2)
  simp only [PartLengthLe.ofList_val] at horth
  rw [ite_eq_right hkne] at horth
  have hsingle : ∀ ν' ∈ (Finset.univ : Finset (PartLengthLe n n)), ν' ≠ k →
      (kostka k.1 ν'.1 : ℤ) * kostkaInv n μ ν'.1 = 0 := by
    intro ν' _ hne
    by_cases hB : kostkaInv n μ ν'.1 = 0
    · rw [hB, mul_zero]
    by_cases hK : kostka k.1 ν'.1 = 0
    · rw [hK, Nat.cast_zero, zero_mul]
    have hmk : Partdom ν'.1 k.1 := partdom_of_kostka_ne_zero hK
    have hmT : ν' ∈ T :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hB, fun hcon => hkdom (hcon.trans hmk)⟩
    have hle : domWeight n k.1 ≤ domWeight n ν'.1 := hkmin ν' hmT
    exact absurd (Subtype.ext (eq_of_partdom_of_domWeight_eq ν'.2.1 k.2.1 ν'.2.2.1 k.2.2.1
      hmk hle)) hne
  rw [Finset.sum_eq_single k hsingle (fun hcon => absurd (Finset.mem_univ k) hcon),
    kostka_self k.2.1, Nat.cast_one, one_mul] at horth
  exact hk0 horth

/-- The diagonal inverse Kostka numbers are `1`. -/
theorem kostkaInv_self {μ : List ℕ} (hμ : IsPart μ) (hsum : μ.sum = n) :
    kostkaInv n μ μ = 1 := by
  classical
  have horth := sum_kostka_mul_kostkaInv_partLengthLe (PartLengthLe.ofList hμ hsum)
    (PartLengthLe.ofList hμ hsum)
  simp only [PartLengthLe.ofList_val, ite_true] at horth
  have hsingle : ∀ ν' ∈ (Finset.univ : Finset (PartLengthLe n n)),
      ν' ≠ PartLengthLe.ofList hμ hsum →
      (kostka μ ν'.1 : ℤ) * kostkaInv n μ ν'.1 = 0 := by
    intro ν' _ hne
    by_cases hB : kostkaInv n μ ν'.1 = 0
    · rw [hB, mul_zero]
    by_cases hK : kostka μ ν'.1 = 0
    · rw [hK, Nat.cast_zero, zero_mul]
    exact absurd (Subtype.ext (Partdom.antisymm ν'.2.1 hμ (partdom_of_kostka_ne_zero hK)
      (partdom_of_kostkaInv_ne_zero hB))) hne
  rw [Finset.sum_eq_single (PartLengthLe.ofList hμ hsum) hsingle
    (fun hcon => absurd (Finset.mem_univ (PartLengthLe.ofList hμ hsum)) hcon)] at horth
  simp only [PartLengthLe.ofList_val] at horth
  rwa [kostka_self hμ, Nat.cast_one, one_mul] at horth

/-! ### The expansion of a Schur polynomial -/

/-- **The expansion of a Schur polynomial in the products of complete homogeneous symmetric
polynomials**, `s_μ = ∑_ν K⁻¹_{μ ν} h_ν`. -/
theorem schurPoly_eq_sum_kostkaInv [CommRing R] (m : ℕ) {μ : List ℕ} (hμ : IsPart μ)
    (hsum : μ.sum = n) :
    schurPoly (Fin m) R μ
      = ∑ ν ∈ partFinset n, (kostkaInv n μ ν : R) • hProd m R ν := by
  classical
  rw [sum_partFinset_eq_sum_partLengthLe (m := n) le_rfl]
  have hh : ∀ ν : PartLengthLe n n, hProd m R ν.1
      = ∑ ρ : PartLengthLe n n, (kostka ρ.1 ν.1 : R) • schurPoly (Fin m) R ρ.1 := by
    intro ν
    rw [hProd_eq_sum_kostka m ν.2.1, ν.2.2.1, sum_partFinset_eq_sum_partLengthLe (m := n) le_rfl]
  simp_rw [hh, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hcoef : ∀ ρ : PartLengthLe n n,
      ∑ ν : PartLengthLe n n, (kostkaInv n μ ν.1 : R) * (kostka ρ.1 ν.1 : R)
        = if ρ = PartLengthLe.ofList hμ hsum then 1 else 0 := by
    intro ρ
    have := congrArg (fun z : ℤ => (z : R))
      (sum_kostka_mul_kostkaInv_partLengthLe ρ (PartLengthLe.ofList hμ hsum))
    push_cast at this
    rw [← this]
    exact Finset.sum_congr rfl fun ν _ => mul_comm _ _
  simp_rw [hcoef, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ (PartLengthLe.ofList hμ hsum)
    (fun ρ : PartLengthLe n n => schurPoly (Fin m) R ρ.1)]
  simp

end MvPolynomial
