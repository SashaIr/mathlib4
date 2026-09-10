/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.FreeSchur
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.LRSymmetry

/-!
# Counting the tableaux of a Littlewood–Richardson support

Following `theories/LRrule/freeSchur.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we count the standard tableaux
completing two standard tableaux `Q₁` and `Q₂` into a Littlewood–Richardson triple of a given
shape.

The Littlewood–Richardson rule for tableaux
`MvPolynomial.schurPoly_mul_eq_sum_LRtriple` expands the product of two Schur polynomials
over that support; comparing it with the expansion of the same product in the Schur family
identifies the number of tableaux of a given shape in the support with the corresponding
Littlewood–Richardson coefficient.  In particular that number depends on `Q₁` and `Q₂` only
through their shapes (Coq `LRtab_coeff_shapeE`).

## Main definitions

* `MvPolynomial.LRtabCoeff Q₁ Q₂ ν` : the number of standard tableaux of shape `ν`
  completing `Q₁` and `Q₂` into a Littlewood–Richardson triple (Coq `LRtab_coeff`).

## Main results

* `MvPolynomial.LRtabCoeff_eq_lrCoeff` : that number is the Littlewood–Richardson coefficient
  `c^ν_{shape Q₁, shape Q₂}` (Coq `LRtab_coeffP`).
* `MvPolynomial.LRtabCoeff_eq_of_shape_eq` : it only depends on the shapes of `Q₁` and `Q₂`
  (Coq `LRtab_coeff_shapeE`).
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {Q₁ Q₂ T₁ T₂ : List (List ℕ)}

/-- The number of standard tableaux of shape `ν` completing `Q₁` and `Q₂` into a
Littlewood–Richardson triple (Coq `LRtab_coeff`). -/
noncomputable def LRtabCoeff (Q₁ Q₂ : List (List ℕ)) (ν : List ℕ) : ℕ :=
  Nat.card {Q : LRsupport Q₁ Q₂ // shape Q.1 = ν}

/-- The shape of a tableau of the Littlewood–Richardson support of `Q₁` and `Q₂` is a
partition of `sizeTab Q₁ + sizeTab Q₂` with at most that many parts. -/
lemma shape_mem_partIdx (Q : LRsupport Q₁ Q₂) :
    IsPart (shape Q.1) ∧ (shape Q.1).sum = sizeTab Q₁ + sizeTab Q₂ ∧
      (shape Q.1).length ≤ sizeTab Q₁ + sizeTab Q₂ := by
  have hpart : IsPart (shape Q.1) := isPart_shape_of_isStdTab Q.2.1.1
  have hsum : (shape Q.1).sum = sizeTab Q₁ + sizeTab Q₂ := Q.2.1.2
  exact ⟨hpart, hsum, le_trans hpart.length_le_sum (le_of_eq hsum)⟩

/-- **The number of tableaux of shape `ν` in the Littlewood–Richardson support of `Q₁` and
`Q₂` is the Littlewood–Richardson coefficient `c^ν_{shape Q₁, shape Q₂}`** (Coq
`LRtab_coeffP`). -/
theorem LRtabCoeff_eq_lrCoeff (hQ₁ : IsStdTab Q₁) (hQ₂ : IsStdTab Q₂) {ν : List ℕ}
    (hν : IsPart ν) (hsum : ν.sum = sizeTab Q₁ + sizeTab Q₂) :
    LRtabCoeff Q₁ Q₂ ν = lrCoeff (shape Q₁) (shape Q₂) ν := by
  classical
  set n := sizeTab Q₁ + sizeTab Q₂ with hn
  set g : LRsupport Q₁ Q₂ → PartIdx n n := fun Q => ⟨shape Q.1, shape_mem_partIdx Q⟩
  have hcard : ∀ ν : PartIdx n n,
      ∑ _Q : {Q : LRsupport Q₁ Q₂ // g Q = ν}, schurPoly (Fin n) ℤ ν.1
        = Fintype.card {Q : LRsupport Q₁ Q₂ // g Q = ν} • schurPoly (Fin n) ℤ ν.1 := by
    intro ν
    simp [Finset.card_univ]
  have hmul : ∑ ν : PartIdx n n,
      Fintype.card {Q : LRsupport Q₁ Q₂ // g Q = ν} • schurPoly (Fin n) ℤ ν.1
      = ∑ ν : PartIdx n n, lrCoeff (shape Q₁) (shape Q₂) ν.1 • schurPoly (Fin n) ℤ ν.1 := by
    rw [← schurPoly_mul_eq_sum_partIdx (R := ℤ)
      (by rw [hn, ← sizeTab, ← sizeTab] : (shape Q₁).sum + (shape Q₂).sum = n) le_rfl,
      schurPoly_mul_eq_sum_LRtriple (R := ℤ) hQ₁ hQ₂,
      ← Fintype.sum_fiberwise g (fun Q => schurPoly (Fin n) ℤ (shape Q.1))]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← hcard ν]
    refine Finset.sum_congr rfl fun Q _ => ?_
    exact congrArg (schurPoly (Fin n) ℤ) (congrArg Subtype.val Q.2).symm
  have hνlen : ν.length ≤ n := by rw [← hsum]; exact hν.length_le_sum
  set νIdx : PartIdx n n := ⟨ν, hν, hsum, hνlen⟩
  have hfun := congrFun (eq_of_sum_nsmul_schurPoly_eq hmul) νIdx
  have hequiv : {Q : LRsupport Q₁ Q₂ // shape Q.1 = ν} ≃ {Q : LRsupport Q₁ Q₂ // g Q = νIdx} :=
    Equiv.subtypeEquivRight fun Q =>
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [LRtabCoeff, ← hfun, Nat.card_congr hequiv, Nat.card_eq_fintype_card]

/-- Outside the partitions of `sizeTab Q₁ + sizeTab Q₂`, the Littlewood–Richardson support is
empty. -/
lemma LRtabCoeff_eq_zero {ν : List ℕ} (h : ¬ (IsPart ν ∧ ν.sum = sizeTab Q₁ + sizeTab Q₂)) :
    LRtabCoeff Q₁ Q₂ ν = 0 := by
  rw [LRtabCoeff, Nat.card_eq_zero]
  refine Or.inl ⟨fun Q => ?_⟩
  obtain ⟨hpart, hsum, -⟩ := shape_mem_partIdx Q.1
  exact h ⟨Q.2 ▸ hpart, Q.2 ▸ hsum⟩

/-- **The number of tableaux of a given shape in the Littlewood–Richardson support depends on
the two tableaux only through their shapes** (Coq `LRtab_coeff_shapeE`). -/
theorem LRtabCoeff_eq_of_shape_eq (hQ₁ : IsStdTab Q₁) (hQ₂ : IsStdTab Q₂) (hT₁ : IsStdTab T₁)
    (hT₂ : IsStdTab T₂) (h₁ : shape Q₁ = shape T₁) (h₂ : shape Q₂ = shape T₂) (ν : List ℕ) :
    LRtabCoeff Q₁ Q₂ ν = LRtabCoeff T₁ T₂ ν := by
  have hs₁ : sizeTab Q₁ = sizeTab T₁ := congrArg List.sum h₁
  have hs₂ : sizeTab Q₂ = sizeTab T₂ := congrArg List.sum h₂
  by_cases h : IsPart ν ∧ ν.sum = sizeTab Q₁ + sizeTab Q₂
  · rw [LRtabCoeff_eq_lrCoeff hQ₁ hQ₂ h.1 h.2,
      LRtabCoeff_eq_lrCoeff hT₁ hT₂ h.1 (by rw [h.2, hs₁, hs₂]), h₁, h₂]
  · rw [LRtabCoeff_eq_zero h, LRtabCoeff_eq_zero (by rwa [← hs₁, ← hs₂])]

end MvPolynomial
