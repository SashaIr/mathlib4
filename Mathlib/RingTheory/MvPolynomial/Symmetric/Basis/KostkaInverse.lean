/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.CompleteHomogeneous

/-!
# Inverse Kostka numbers

A Lean 4 port of the inverse Kostka numbers `'K^-1(la, mu)` of `theories/MPoly/Schur_altdef.v`
from [Coq-Combi](https://github.com/math-comp/Coq-Combi).

The Kostka numbers give the expansion `h_mu = ∑_nu K_{nu mu} s_nu` of a product of complete
homogeneous symmetric polynomials in the Schur basis
(`MvPolynomial.hProd_eq_sum_kostka`).  Since `K_{nu mu}` vanishes unless `mu` is dominated
by `nu`, and `K_{mu mu} = 1`, the Kostka matrix is unitriangular for the dominance order,
hence invertible over `ℤ`.  Its inverse is the matrix of the *inverse Kostka numbers*, and
it expands a Schur polynomial in the products of complete homogeneous symmetric
polynomials.

## Main definitions

* `MvPolynomial.kostkaInv n lam mu` : the inverse Kostka number `K⁻¹_{lam mu}`, that is, the
  coefficient of `h_mu` in the expansion of the Schur polynomial `s_lam`.

## Main results

* `MvPolynomial.sum_kostka_mul_kostkaInv` : the two matrices are inverse to each other.
* `MvPolynomial.partdom_of_kostkaInv_ne_zero`, `MvPolynomial.kostkaInv_self` : the inverse
  Kostka matrix is again unitriangular for the dominance order.
* `MvPolynomial.schurPoly_eq_sum_kostkaInv` : `s_lam = ∑_mu K⁻¹_{lam mu} h_mu`, over any
  commutative ring and in any number of variables.
-/

namespace MvPolynomial

open List MvPolynomial

variable {n : ℕ} {R : Type*}

/-! ### Partitions of `n`, as an index type and as a finite set of lists -/

/-- A partition of `n`, as an element of the index type `PartIdx n n`. -/
def partIdxOfMem {lam : List ℕ} (hlam : IsPart lam) (hsum : lam.sum = n) : PartIdx n n :=
  ⟨lam, hlam, hsum, hsum ▸ hlam.length_le_sum⟩

@[simp] lemma partIdxOfMem_val {lam : List ℕ} (hlam : IsPart lam) (hsum : lam.sum = n) :
    (partIdxOfMem hlam hsum).1 = lam := rfl

/-! ### The Kostka matrix as a change of basis -/

/-- The matrix of the basis of Schur polynomials against the basis of the products of
complete homogeneous symmetric polynomials is the Kostka matrix. -/
lemma schurBasis_toMatrix_hBasis (nu mu : PartIdx n n) :
    (schurBasis n n ℤ).toMatrix (hBasis n n ℤ) nu mu = (kostka nu.1 mu.1 : ℤ) := by
  have hexp : hBasis n n ℤ mu
      = ∑ nu' : PartIdx n n, (kostka nu'.1 mu.1 : ℤ) • schurBasis n n ℤ nu' := by
    refine Subtype.ext ?_
    rw [coe_hBasis, hProd_eq_sum_partIdx mu]
    push_cast
    exact Finset.sum_congr rfl fun nu' _ => by rw [coe_schurBasis]
  rw [Module.Basis.toMatrix_apply, hexp, map_sum]
  simp [Finsupp.single_apply, eq_comm]

/-! ### The inverse Kostka numbers -/

/-- The inverse Kostka number `K⁻¹_{lam mu}`: the coefficient of `h_mu` in the expansion of
the Schur polynomial `s_lam` in the products of complete homogeneous symmetric polynomials.
It is zero unless both `lam` and `mu` are partitions of `n`. -/
noncomputable def kostkaInv (n : ℕ) (lam mu : List ℕ) : ℤ :=
  if hlam : IsPart lam ∧ lam.sum = n then
    if hmu : IsPart mu ∧ mu.sum = n then
      (hBasis n n ℤ).toMatrix (schurBasis n n ℤ) (partIdxOfMem hmu.1 hmu.2)
        (partIdxOfMem hlam.1 hlam.2)
    else 0
  else 0

lemma kostkaInv_apply (lam mu : PartIdx n n) :
    kostkaInv n lam.1 mu.1 = (hBasis n n ℤ).toMatrix (schurBasis n n ℤ) mu lam := by
  rw [kostkaInv, dif_pos ⟨lam.2.1, lam.2.2.1⟩, dif_pos ⟨mu.2.1, mu.2.2.1⟩]
  rfl

lemma kostkaInv_eq_zero_of_left {lam mu : List ℕ} (h : ¬ (IsPart lam ∧ lam.sum = n)) :
    kostkaInv n lam mu = 0 := by
  rw [kostkaInv, dif_neg h]

lemma kostkaInv_eq_zero_of_right {lam mu : List ℕ} (h : ¬ (IsPart mu ∧ mu.sum = n)) :
    kostkaInv n lam mu = 0 := by
  simp only [kostkaInv, dif_neg h, dite_eq_ite, ite_self]

/-! ### Orthogonality -/

/-- **The Kostka matrix and the inverse Kostka matrix are inverse to each other**, in the
form indexed by `PartIdx n n`. -/
theorem sum_kostka_mul_kostkaInv_partIdx (nu lam : PartIdx n n) :
    ∑ mu : PartIdx n n, (kostka nu.1 mu.1 : ℤ) * kostkaInv n lam.1 mu.1
      = if nu = lam then 1 else 0 := by
  have h := congrFun (congrFun
    (Module.Basis.toMatrix_mul_toMatrix_flip (schurBasis n n ℤ) (hBasis n n ℤ)) nu) lam
  rw [Matrix.mul_apply] at h
  simp only [schurBasis_toMatrix_hBasis, ← kostkaInv_apply, Matrix.one_apply] at h
  exact h

/-- **The Kostka matrix and the inverse Kostka matrix are inverse to each other.** -/
theorem sum_kostka_mul_kostkaInv {nu lam : List ℕ} (hnu : IsPart nu) (hnusum : nu.sum = n)
    (hlam : IsPart lam) (hlamsum : lam.sum = n) :
    ∑ mu ∈ partFinset n, (kostka nu mu : ℤ) * kostkaInv n lam mu
      = if nu = lam then 1 else 0 := by
  rw [sum_partFinset_eq_sum_partIdx (m := n) le_rfl]
  have hkey := sum_kostka_mul_kostkaInv_partIdx (partIdxOfMem hnu hnusum)
    (partIdxOfMem hlam hlamsum)
  simp only [partIdxOfMem_val] at hkey
  rw [hkey]
  exact if_congr ⟨fun hh => congrArg Subtype.val hh, fun hh => Subtype.ext hh⟩ rfl rfl

/-! ### Unitriangularity of the inverse Kostka matrix -/

/-- An inverse Kostka number `K⁻¹_{lam mu}` is nonzero only if `lam` is dominated by
`mu`. -/
theorem partdom_of_kostkaInv_ne_zero {lam mu : List ℕ} (h : kostkaInv n lam mu ≠ 0) :
    Partdom lam mu := by
  classical
  by_cases hlam : IsPart lam ∧ lam.sum = n
  swap
  · exact absurd (kostkaInv_eq_zero_of_left hlam) h
  by_cases hmu : IsPart mu ∧ mu.sum = n
  swap
  · exact absurd (kostkaInv_eq_zero_of_right hmu) h
  by_contra hdom
  set T := Finset.univ.filter
    (fun k : PartIdx n n => kostkaInv n lam k.1 ≠ 0 ∧ ¬ Partdom lam k.1) with hT
  have hTne : T.Nonempty := ⟨partIdxOfMem hmu.1 hmu.2, by simp [hT, h, hdom]⟩
  obtain ⟨k, hkT, hkmin⟩ := Finset.exists_min_image T (fun k => domWeight n k.1) hTne
  obtain ⟨-, hk0, hkdom⟩ := Finset.mem_filter.1 hkT
  have hkne : k ≠ partIdxOfMem hlam.1 hlam.2 := fun he => hkdom (he ▸ Partdom.refl lam)
  have horth := sum_kostka_mul_kostkaInv_partIdx k (partIdxOfMem hlam.1 hlam.2)
  simp only [partIdxOfMem_val] at horth
  rw [if_neg hkne] at horth
  have hsingle : ∀ mu' ∈ (Finset.univ : Finset (PartIdx n n)), mu' ≠ k →
      (kostka k.1 mu'.1 : ℤ) * kostkaInv n lam mu'.1 = 0 := by
    intro mu' _ hne
    by_cases hB : kostkaInv n lam mu'.1 = 0
    · rw [hB, mul_zero]
    by_cases hK : kostka k.1 mu'.1 = 0
    · rw [hK, Nat.cast_zero, zero_mul]
    have hmk : Partdom mu'.1 k.1 := partdom_of_kostka_ne_zero hK
    have hmT : mu' ∈ T :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hB, fun hcon => hkdom (hcon.trans hmk)⟩
    have hle : domWeight n k.1 ≤ domWeight n mu'.1 := hkmin mu' hmT
    exact absurd (Subtype.ext (eq_of_partdom_of_domWeight_eq mu'.2.1 k.2.1 mu'.2.2.1 k.2.2.1
      hmk hle)) hne
  rw [Finset.sum_eq_single k hsingle (fun hcon => absurd (Finset.mem_univ k) hcon),
    kostka_self k.2.1, Nat.cast_one, one_mul] at horth
  exact hk0 horth

/-- The diagonal inverse Kostka numbers are `1`. -/
theorem kostkaInv_self {lam : List ℕ} (hlam : IsPart lam) (hsum : lam.sum = n) :
    kostkaInv n lam lam = 1 := by
  classical
  have horth := sum_kostka_mul_kostkaInv_partIdx (partIdxOfMem hlam hsum)
    (partIdxOfMem hlam hsum)
  simp only [partIdxOfMem_val, if_true] at horth
  have hsingle : ∀ mu' ∈ (Finset.univ : Finset (PartIdx n n)), mu' ≠ partIdxOfMem hlam hsum →
      (kostka lam mu'.1 : ℤ) * kostkaInv n lam mu'.1 = 0 := by
    intro mu' _ hne
    by_cases hB : kostkaInv n lam mu'.1 = 0
    · rw [hB, mul_zero]
    by_cases hK : kostka lam mu'.1 = 0
    · rw [hK, Nat.cast_zero, zero_mul]
    exact absurd (Subtype.ext (Partdom.antisymm mu'.2.1 hlam (partdom_of_kostka_ne_zero hK)
      (partdom_of_kostkaInv_ne_zero hB))) hne
  rw [Finset.sum_eq_single (partIdxOfMem hlam hsum) hsingle
    (fun hcon => absurd (Finset.mem_univ (partIdxOfMem hlam hsum)) hcon)] at horth
  simp only [partIdxOfMem_val] at horth
  rwa [kostka_self hlam, Nat.cast_one, one_mul] at horth

/-! ### The expansion of a Schur polynomial -/

/-- **The expansion of a Schur polynomial in the products of complete homogeneous symmetric
polynomials**, `s_lam = ∑_mu K⁻¹_{lam mu} h_mu`. -/
theorem schurPoly_eq_sum_kostkaInv [CommRing R] (m : ℕ) {lam : List ℕ} (hlam : IsPart lam)
    (hsum : lam.sum = n) :
    schurPoly (Fin m) R lam
      = ∑ mu ∈ partFinset n, (kostkaInv n lam mu : R) • hProd m R mu := by
  classical
  rw [sum_partFinset_eq_sum_partIdx (m := n) le_rfl]
  have hh : ∀ mu : PartIdx n n, hProd m R mu.1
      = ∑ nu : PartIdx n n, (kostka nu.1 mu.1 : R) • schurPoly (Fin m) R nu.1 := by
    intro mu
    rw [hProd_eq_sum_kostka m mu.2.1, mu.2.2.1, sum_partFinset_eq_sum_partIdx (m := n) le_rfl]
  simp_rw [hh, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hcoef : ∀ nu : PartIdx n n,
      ∑ mu : PartIdx n n, (kostkaInv n lam mu.1 : R) * (kostka nu.1 mu.1 : R)
        = if nu = partIdxOfMem hlam hsum then 1 else 0 := by
    intro nu
    have := congrArg (fun z : ℤ => (z : R))
      (sum_kostka_mul_kostkaInv_partIdx nu (partIdxOfMem hlam hsum))
    push_cast at this
    rw [← this]
    exact Finset.sum_congr rfl fun mu _ => mul_comm _ _
  simp_rw [hcoef, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ (partIdxOfMem hlam hsum)
    (fun nu : PartIdx n n => schurPoly (Fin m) R nu.1)]
  simp

end MvPolynomial
