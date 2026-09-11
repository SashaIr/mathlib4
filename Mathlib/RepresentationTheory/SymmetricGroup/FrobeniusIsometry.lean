/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RepresentationTheory.SymmetricGroup.FrobeniusCharacteristic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.PowerSumOrtho

/-!
# The Frobenius characteristic is an isometry

Continuing the port of Coq-Combi's `SymGroup/Frobenius_char.v`, we prove that the Frobenius
characteristic map takes the usual scalar product of class functions of the symmetric group
`S_n` to the Hall scalar product of symmetric polynomials.

## Main definitions

* `Equiv.Perm.classInner f g` : the scalar product `(1 / n !) ∑_σ f(σ) g(σ)` of two class
  functions on `S_n`.
* `Equiv.Perm.frobCharSub` : the Frobenius characteristic, as an element of the module of
  symmetric homogeneous polynomials of degree `n` (in at least `n` variables).

## Main results

* `Equiv.Perm.exists_comp_cycleTypeList` : a class function is a function of the cycle type.
* `Equiv.Perm.hallInner_frobCharSub` : **the Frobenius characteristic is an isometry**,
  `⟨ch f, ch g⟩ = (1 / n !) ∑_σ f(σ) g(σ)`.
* `Equiv.Perm.eq_zero_of_frobChar_eq_zero` : the Frobenius characteristic is injective on class
  functions.
* `Equiv.Perm.exists_isClassFun_frobCharSub_eq` : it is also surjective onto the symmetric
  homogeneous polynomials of degree `n`.
-/

@[expose] public section

open Young

open Equiv MvPolynomial List

namespace Equiv.Perm


variable {n k : ℕ}

/-! ### Class functions as functions of the cycle type -/

/-- Two permutations with the same cycle type take the same value under a class
function. -/
lemma IsClassFun.apply_eq_of_cycleTypeList_eq {f : Perm (Fin n) → ℚ} (hf : IsClassFun f)
    {σ τ : Perm (Fin n)} (h : cycleTypeList σ = cycleTypeList τ) :
    f σ = f τ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (cycleTypeList_eq_iff_isConj.1 h)
  rw [← hc]
  simpa using (hf σ c⁻¹).symm

/-- A class function on the symmetric group is a function of the cycle type. -/
lemma exists_comp_cycleTypeList {f : Perm (Fin n) → ℚ} (hf : IsClassFun f) :
    ∃ c : List ℕ → ℚ, ∀ σ, f σ = c (cycleTypeList σ) := by
  classical
  refine ⟨fun μ => if h : ∃ σ : Perm (Fin n), cycleTypeList σ = μ then f h.choose
    else 0, fun σ => ?_⟩
  have hex : ∃ τ : Perm (Fin n), cycleTypeList τ = cycleTypeList σ := ⟨σ, rfl⟩
  change f σ = if h : ∃ τ : Perm (Fin n), cycleTypeList τ = cycleTypeList σ
    then f h.choose else 0
  rw [dite_eq_left hex]
  exact hf.apply_eq_of_cycleTypeList_eq hex.choose_spec.symm

/-- Averaging a function of the cycle type over the symmetric group. -/
lemma sum_comp_cycleTypeList (c : List ℕ → ℚ) :
    ((Nat.factorial n : ℚ))⁻¹ * ∑ σ : Perm (Fin n), c (cycleTypeList σ)
      = ∑ μ ∈ partFinset n, c μ * ((zcard μ : ℚ))⁻¹ := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (fun σ _ => cycleTypeList_mem_partFinset σ)
    (fun σ : Perm (Fin n) => c (cycleTypeList σ)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hμ
  have hz : (zcard μ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (zcard_pos hpart).ne'
  have hne : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hc : ((Finset.univ.filter fun σ : Perm (Fin n) => cycleTypeList σ = μ).card : ℚ)
      * (zcard μ : ℚ) = (Nat.factorial n : ℚ) := by
    exact_mod_cast card_cycleTypeList_mul_zcard (n := n) hpart hsum
  rw [Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2],
    Finset.sum_const, nsmul_eq_mul]
  field_simp
  linear_combination c μ * hc

/-! ### The characteristic as an element of the module of symmetric polynomials -/

/-- The cycle type of a permutation of `Fin n`, as a partition of `n` with at most `k`
parts. -/
noncomputable def cycleTypeIdx (hnk : n ≤ k) (σ : Perm (Fin n)) : PartIdx n k :=
  ⟨cycleTypeList σ, isPart_cycleTypeList σ, sum_cycleTypeList σ,
    le_trans (le_trans (isPart_cycleTypeList σ).length_le_sum
      (le_of_eq (sum_cycleTypeList σ))) hnk⟩

/-- The Frobenius characteristic is a symmetric polynomial, homogeneous of degree `n`. -/
lemma frobChar_mem_symHomogeneousSubmodule (hnk : n ≤ k) (f : Perm (Fin n) → ℚ) :
    frobChar k f ∈ symHomogeneousSubmodule k n ℚ := by
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _ ?_)
  exact pProd_mem_symHomogeneousSubmodule (cycleTypeIdx hnk σ)

/-- The Frobenius characteristic of a class function on `S_n`, as an element of the module
of symmetric homogeneous polynomials of degree `n` in `k ≥ n` variables. -/
noncomputable def frobCharSub (hnk : n ≤ k) (f : Perm (Fin n) → ℚ) :
    symHomogeneousSubmodule k n ℚ :=
  ⟨frobChar k f, frobChar_mem_symHomogeneousSubmodule hnk f⟩

/-- The underlying polynomial of `frobCharSub` is the Frobenius characteristic. -/
@[simp] lemma coe_frobCharSub (hnk : n ≤ k) (f : Perm (Fin n) → ℚ) :
    (frobCharSub hnk f : MvPolynomial (Fin k) ℚ) = frobChar k f := rfl

/-- The expansion of the Frobenius characteristic of a function of the cycle type in the
power sum basis. -/
lemma frobCharSub_comp_cycleTypeList (hnk : n ≤ k) (c : List ℕ → ℚ) :
    frobCharSub hnk (fun σ : Perm (Fin n) => c (cycleTypeList σ))
      = ∑ μ : PartIdx n k, (c μ.1 * ((zcard μ.1 : ℚ))⁻¹) • pSub k n ℚ μ := by
  refine Subtype.ext ?_
  rw [coe_frobCharSub, frobChar_comp_cycleTypeList,
    sum_partFinset_eq_sum_partIdx hnk fun μ => (c μ * ((zcard μ : ℚ))⁻¹) • pProd k ℚ μ]
  rw [Submodule.coe_sum]
  rfl

/-! ### The isometry -/

/-- The scalar product of two class functions of the symmetric group. -/
noncomputable def classInner (f g : Perm (Fin n) → ℚ) : ℚ :=
  ((Nat.factorial n : ℚ))⁻¹ * ∑ σ : Perm (Fin n), f σ * g σ

/-- **The Frobenius characteristic is an isometry**: the Hall scalar product of the
characteristics of two class functions is their scalar product as class functions. -/
theorem hallInner_frobCharSub (hnk : n ≤ k) {f g : Perm (Fin n) → ℚ}
    (hf : IsClassFun f) (hg : IsClassFun g) :
    hallInner k n ℚ (frobCharSub hnk f) (frobCharSub hnk g) = classInner f g := by
  classical
  obtain ⟨c, hc⟩ := exists_comp_cycleTypeList hf
  obtain ⟨d, hd⟩ := exists_comp_cycleTypeList hg
  have hfc : f = fun σ : Perm (Fin n) => c (cycleTypeList σ) := funext hc
  have hgd : g = fun σ : Perm (Fin n) => d (cycleTypeList σ) := funext hd
  rw [hfc, hgd, frobCharSub_comp_cycleTypeList, frobCharSub_comp_cycleTypeList]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    hallInner_pSub hnk]
  have hinner : ∀ x : PartIdx n k,
      (∑ y : PartIdx n k, c y.1 * ((zcard y.1 : ℚ))⁻¹ * if y = x then (zcard y.1 : ℚ) else 0)
        = c x.1 := by
    intro x
    have hz : (zcard x.1 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (zcard_pos x.2.1).ne'
    rw [Finset.sum_eq_single x]
    · rw [ite_eq_left rfl]
      field_simp
    · intro y _ hy
      rw [ite_eq_right hy, mul_zero]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  rw [Finset.sum_congr rfl fun x _ => by rw [hinner x], classInner,
    sum_comp_cycleTypeList (n := n) (fun μ => c μ * d μ),
    sum_partFinset_eq_sum_partIdx hnk fun μ => c μ * d μ * ((zcard μ : ℚ))⁻¹]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **The Frobenius characteristic is surjective**: every symmetric homogeneous polynomial
of degree `n` in `k ≥ n` variables is the characteristic of a class function of `S_n`. -/
theorem exists_isClassFun_frobCharSub_eq (hnk : n ≤ k) (F : symHomogeneousSubmodule k n ℚ) :
    ∃ f : Perm (Fin n) → ℚ, IsClassFun f ∧ frobCharSub hnk f = F := by
  classical
  set a : PartIdx n k → ℚ := fun μ => hallInner k n ℚ F (pSubInvZ k n ℚ μ) with ha
  set c : List ℕ → ℚ := fun μ =>
    if h : IsPart μ ∧ μ.sum = n ∧ μ.length ≤ k then (zcard μ : ℚ) * a ⟨μ, h⟩ else 0
    with hcdef
  refine ⟨fun σ => c (cycleTypeList σ), fun σ τ => by
    simp only [cycleTypeList_conj], ?_⟩
  rw [frobCharSub_comp_cycleTypeList hnk c]
  have hterm : ∀ μ : PartIdx n k, c μ.1 * ((zcard μ.1 : ℚ))⁻¹ = a μ := by
    intro μ
    have hz : (zcard μ.1 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (zcard_pos μ.2.1).ne'
    rw [hcdef]
    simp only [dite_eq_left μ.2]
    field_simp
  rw [Finset.sum_congr rfl fun μ _ => by rw [hterm μ]]
  exact (eq_sum_hallInner_pSubInvZ_smul hnk F).symm

/-- The Frobenius characteristic is injective on class functions. -/
theorem eq_zero_of_frobChar_eq_zero (hnk : n ≤ k) {f : Perm (Fin n) → ℚ} (hf : IsClassFun f)
    (h : frobChar k f = 0) : f = 0 := by
  have hzero : frobCharSub hnk f = 0 := Subtype.ext (by rw [coe_frobCharSub, h]; rfl)
  have hiso := hallInner_frobCharSub hnk hf hf
  rw [hzero, map_zero] at hiso
  have hne : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hsum : ∑ σ : Perm (Fin n), f σ * f σ = 0 := by
    rw [classInner] at hiso
    field_simp at hiso
    simpa [sq] using hiso.symm
  funext σ
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun τ _ => mul_self_nonneg (f τ))).1 hsum σ (Finset.mem_univ σ)
  simpa using mul_self_eq_zero.1 this

end Equiv.Perm
