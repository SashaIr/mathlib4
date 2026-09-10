/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.HookLength.Formula
public import Mathlib.RepresentationTheory.SymmetricGroup.FrobeniusIsometry

/-!
# The Schur class functions of the symmetric group

This file finishes the port of Coq-Combi's `SymGroup/Frobenius_char.v`.  Since the
Frobenius characteristic is an isometric isomorphism from the class functions of `S_n`
onto the symmetric homogeneous polynomials of degree `n`, one can *define* a family of
class functions `schurChar η`, indexed by the partitions `η` of `n`, by pulling back
the Schur polynomials.  Over `ℂ` these are exactly the irreducible characters of `S_n`;
irreducibility (which needs representation theory) is not proved here, but all the
combinatorial consequences are:

* they are orthonormal for the scalar product of class functions;
* the power sum `p_{cycleType σ}` expands over the Schur polynomials with the values of
  the `schurChar` as coefficients (the **Frobenius character formula**);
* the "dimension" `schurChar η 1` is the number of standard Young tableaux of shape
  `η`, hence is given by the hook length formula.

## Main definitions

* `Equiv.Perm.schurChar η` : the class function of `S_n` whose Frobenius characteristic is
  the Schur polynomial `s_η`.

## Main results

* `Equiv.Perm.frobChar_schurChar` : `ch (schurChar η) = s_η`.
* `Equiv.Perm.classInner_schurChar` : the family `schurChar` is orthonormal.
* `Equiv.Perm.hallInner_pSub_cycleTypeIdx_schurSub` : `⟨p_{cycleType σ}, s_η⟩ = schurChar η σ`.
* `Equiv.Perm.pSub_cycleTypeIdx_eq_sum`, `Equiv.Perm.pProd_cycleTypeList_eq_sum` : the **Frobenius
  character formula** `p_{cycleType σ} = ∑_lam schurChar η σ · s_η`.
* `Equiv.Perm.eq_of_frobChar_eq` : a class function is determined by its characteristic.
* `Equiv.Perm.schurChar_one` : `schurChar η 1 = f^η`, the number of standard tableaux.
* `Equiv.Perm.schurChar_one_mul_hookProd` : the hook length formula for `schurChar η 1`.
* `Equiv.Perm.schurChar_row`, `Equiv.Perm.schurChar_column` : the class functions of the row and
  column shapes are the trivial and the signature characters.
-/

@[expose] public section

open Young

open Equiv MvPolynomial List

namespace Equiv.Perm


variable {n : ℕ}

/-! ### The Schur class functions -/

/-- The class function of `S_n` whose Frobenius characteristic is the Schur polynomial
`s_η`.  Over `ℂ` this is the irreducible character of `S_n` attached to `η`. -/
noncomputable def schurChar (η : PartIdx n n) : Perm (Fin n) → ℚ :=
  (exists_isClassFun_frobCharSub_eq (le_refl n) (schurSub n n ℚ η)).choose

/-- The Schur class functions are class functions. -/
lemma isClassFun_schurChar (η : PartIdx n n) : IsClassFun (schurChar η) :=
  (exists_isClassFun_frobCharSub_eq (le_refl n) (schurSub n n ℚ η)).choose_spec.1

/-- The Frobenius characteristic of `schurChar η` is the Schur polynomial `s_η`. -/
@[simp] lemma frobCharSub_schurChar (η : PartIdx n n) :
    frobCharSub (le_refl n) (schurChar η) = schurSub n n ℚ η :=
  (exists_isClassFun_frobCharSub_eq (le_refl n) (schurSub n n ℚ η)).choose_spec.2

/-- The Frobenius characteristic of `schurChar η` is the Schur polynomial `s_η`. -/
theorem frobChar_schurChar (η : PartIdx n n) :
    frobChar n (schurChar η) = schurPoly (Fin n) ℚ η.1 := by
  rw [← coe_frobCharSub (le_refl n) (schurChar η), frobCharSub_schurChar, coe_schurSub]

/-- **The Schur class functions are orthonormal** for the scalar product of class
functions. -/
theorem classInner_schurChar (η μ : PartIdx n n) :
    classInner (schurChar η) (schurChar μ) = if η = μ then 1 else 0 := by
  rw [← hallInner_frobCharSub (le_refl n) (isClassFun_schurChar η) (isClassFun_schurChar μ),
    frobCharSub_schurChar, frobCharSub_schurChar, hallInner_schurSub]

/-- A class function is determined by its Frobenius characteristic. -/
theorem eq_of_frobChar_eq {f g : Perm (Fin n) → ℚ} (hf : IsClassFun f) (hg : IsClassFun g)
    (h : frobChar n f = frobChar n g) : f = g := by
  have hsub : IsClassFun (f - g) := fun σ τ => by
    simp only [Pi.sub_apply, hf σ τ, hg σ τ]
  have hzero : frobChar n (f - g) = 0 := by
    have hfg : f - g = f + (-1 : ℚ) • g := by
      funext σ
      simp [sub_eq_add_neg]
    rw [hfg, frobChar_add, frobChar_smul, h, neg_one_smul, add_neg_cancel]
  have hfg := eq_zero_of_frobChar_eq_zero (le_refl n) hsub hzero
  funext σ
  simpa [sub_eq_zero] using congrFun hfg σ

/-! ### The Frobenius character formula -/

/-- The scalar product of the indicator function of a conjugacy class with a class
function. -/
lemma classInner_classIndicator {g : Perm (Fin n) → ℚ} (hg : IsClassFun g)
    (σ : Perm (Fin n)) :
    classInner (fun τ : Perm (Fin n) =>
        if cycleTypeList τ = cycleTypeList σ then (1 : ℚ) else 0) g
      = ((zcard (cycleTypeList σ) : ℚ))⁻¹ * g σ := by
  classical
  have hcard := card_cycleTypeList_mul_zcard (n := n) (isPart_cycleTypeList σ)
    (sum_cycleTypeList σ)
  have hz : (zcard (cycleTypeList σ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (zcard_pos (isPart_cycleTypeList σ)).ne'
  have hne : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hsum : ∑ τ : Perm (Fin n),
      (if cycleTypeList τ = cycleTypeList σ then (1 : ℚ) else 0) * g τ
        = ((Finset.univ.filter
            fun τ : Perm (Fin n) => cycleTypeList τ = cycleTypeList σ).card : ℚ)
          * g σ := by
    rw [Finset.sum_congr rfl fun τ _ => by
      rw [ite_mul, one_mul, zero_mul], Finset.sum_ite, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_congr rfl fun τ hτ =>
      hg.apply_eq_of_cycleTypeList_eq (Finset.mem_filter.1 hτ).2, Finset.sum_const,
      nsmul_eq_mul]
  rw [classInner, hsum]
  have hc : ((Finset.univ.filter
      fun τ : Perm (Fin n) => cycleTypeList τ = cycleTypeList σ).card : ℚ)
      * (zcard (cycleTypeList σ) : ℚ) = (Nat.factorial n : ℚ) := by
    exact_mod_cast hcard
  field_simp
  linear_combination g σ * hc

/-- The Frobenius characteristic of the indicator function of a conjugacy class, as an
element of the module of symmetric polynomials. -/
lemma frobCharSub_classIndicator (σ : Perm (Fin n)) :
    frobCharSub (le_refl n) (fun τ : Perm (Fin n) =>
        if cycleTypeList τ = cycleTypeList σ then (1 : ℚ) else 0)
      = ((zcard (cycleTypeList σ) : ℚ))⁻¹ • pSub n n ℚ (cycleTypeIdx (le_refl n) σ) := by
  refine Subtype.ext ?_
  rw [coe_frobCharSub, frobChar_classIndicator n (isPart_cycleTypeList σ)
    (sum_cycleTypeList σ), SetLike.val_smul, coe_pSub]
  rfl

/-- **The value of a Schur class function is a Hall scalar product**: pairing the power
sum attached to the cycle type of `σ` with the Schur polynomial `s_η` gives the value
`schurChar η σ`. -/
theorem hallInner_pSub_cycleTypeIdx_schurSub (σ : Perm (Fin n)) (η : PartIdx n n) :
    hallInner n n ℚ (pSub n n ℚ (cycleTypeIdx (le_refl n) σ)) (schurSub n n ℚ η)
      = schurChar η σ := by
  classical
  set f : Perm (Fin n) → ℚ := fun τ =>
    if cycleTypeList τ = cycleTypeList σ then (1 : ℚ) else 0 with hf
  have hfclass : IsClassFun f := by
    intro ρ τ
    simp only [hf, cycleTypeList_conj]
  have hz : (zcard (cycleTypeList σ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (zcard_pos (isPart_cycleTypeList σ)).ne'
  have hiso := hallInner_frobCharSub (le_refl n) hfclass (isClassFun_schurChar η)
  rw [frobCharSub_classIndicator σ, frobCharSub_schurChar, map_smul,
    LinearMap.smul_apply, smul_eq_mul,
    classInner_classIndicator (isClassFun_schurChar η) σ] at hiso
  exact mul_left_cancel₀ (inv_ne_zero hz) hiso

/-- **The Frobenius character formula**: the power sum attached to the cycle type of a
permutation `σ` expands over the Schur polynomials with the values of the Schur class
functions at `σ` as coefficients. -/
theorem pSub_cycleTypeIdx_eq_sum (σ : Perm (Fin n)) :
    pSub n n ℚ (cycleTypeIdx (le_refl n) σ)
      = ∑ η : PartIdx n n, schurChar η σ • schurSub n n ℚ η := by
  have hdual : ∀ η μ : PartIdx n n,
      hallInner n n ℚ (schurSub n n ℚ η) (schurSub n n ℚ μ) = if η = μ then 1 else 0 :=
    fun η μ => hallInner_schurSub η μ
  have := eq_sum_hallInner_smul_of_dual (schurSub n n ℚ) (schurSub n n ℚ) hdual
    (pSub n n ℚ (cycleTypeIdx (le_refl n) σ))
  rw [this]
  exact Finset.sum_congr rfl fun η _ => by
    rw [hallInner_pSub_cycleTypeIdx_schurSub]

/-- **The Frobenius character formula**, at the level of polynomials: the power sum
`p_{cycleType σ}` is the combination of the Schur polynomials with the values of the Schur
class functions at `σ` as coefficients. -/
theorem pProd_cycleTypeList_eq_sum (σ : Perm (Fin n)) :
    pProd n ℚ (cycleTypeList σ)
      = ∑ η : PartIdx n n, schurChar η σ • schurPoly (Fin n) ℚ η.1 := by
  have hval := congrArg (Subtype.val) (pSub_cycleTypeIdx_eq_sum σ)
  rw [coe_pSub, Submodule.coe_sum] at hval
  refine hval.trans (Finset.sum_congr rfl fun η _ => ?_)
  rw [SetLike.val_smul, coe_schurSub]

/-! ### The dimension: the number of standard Young tableaux -/

/-- The cycle type of the identity permutation of `Fin n` is `1^n`. -/
lemma cycleTypeList_one : cycleTypeList (1 : Perm (Fin n)) = List.replicate n 1 := by
  rw [cycleTypeList_eq_iff (isPart_replicate_one n) (by simp)]
  rw [Equiv.Perm.cycleType_one, bigParts]
  refine (Multiset.filter_eq_nil.2 ?_).symm
  intro a ha
  simp only [Multiset.mem_coe, List.mem_replicate] at ha
  omega

/-- The Kostka number with content `1^n` is the number of standard Young tableaux. -/
lemma kostka_replicate_one {μ : List ℕ} (hsum : μ.sum = n) :
    kostka μ (List.replicate n 1) = numStdTab μ := by
  rw [numStdTab_eq_kostkaNum, hsum,
    ← kostkaNum_eq_kostka' (m := n) (isPart_replicate_one n) (by simp) μ]
  have hset : tabSet n μ (fun i => (List.replicate n 1).getD i 0) = tabSet n μ (fun _ => 1) := by
    ext P
    simp only [tabSet, Set.mem_ofPred_eq]
    refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
    refine forall_congr' fun i => forall_congr' fun hi => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left hi]
    rfl
  rw [kostkaNum, kostkaNum, hset]

/-- The power sums `p_{1^n}` and the complete homogeneous product `h_{1^n}` agree. -/
lemma pProd_replicate_one (m : ℕ) :
    pProd m ℚ (List.replicate n 1) = hProd m ℚ (List.replicate n 1) := by
  rw [pProd, hProd, List.map_replicate, List.map_replicate]
  congr 1
  rw [psum, hsymm_one]
  simp [pow_one]

/-- **The dimension of the Schur class function**: its value at the identity is the number
of standard Young tableaux of shape `η`. -/
theorem schurChar_one (η : PartIdx n n) : schurChar η 1 = numStdTab η.1 := by
  have hp : IsPart (List.replicate n 1) ∧ (List.replicate n 1).sum = n ∧
      (List.replicate n 1).length ≤ n := ⟨isPart_replicate_one n, by simp, by simp⟩
  have hct : cycleTypeIdx (le_refl n) (1 : Perm (Fin n)) = ⟨List.replicate n 1, hp⟩ :=
    Subtype.ext (by
      change cycleTypeList (1 : Perm (Fin n)) = List.replicate n 1
      exact cycleTypeList_one)
  have hph : pSub n n ℚ ⟨List.replicate n 1, hp⟩ = hSub n n ℚ ⟨List.replicate n 1, hp⟩ :=
    Subtype.ext (by rw [coe_pSub, coe_hSub]; exact pProd_replicate_one n)
  rw [← hallInner_pSub_cycleTypeIdx_schurSub (1 : Perm (Fin n)) η, hct, hph,
    hallInner_hSub_schurSub, kostka_replicate_one η.2.2.1]

/-- **The hook length formula** for the dimension of a Schur class function. -/
theorem schurChar_one_mul_hookProd (η : PartIdx n n) :
    schurChar η 1 * (hookProd η.1 : ℚ) = (Nat.factorial n : ℚ) := by
  rw [schurChar_one]
  have := numStdTab_mul_hookProd η.2.1
  rw [η.2.2.1] at this
  exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) this

/-! ### The row and column shapes -/

/-- The class function of `S_n` attached to the row shape `(n)` is the trivial
character. -/
theorem schurChar_row (hn : 0 < n) (μ : PartIdx n n) (hμ : μ.1 = [n]) :
    schurChar μ = fun _ : Perm (Fin n) => (1 : ℚ) := by
  refine eq_of_frobChar_eq (isClassFun_schurChar μ) (fun _ _ => rfl) ?_
  rw [frobChar_schurChar, hμ, schurPoly_row hn, frobChar_one]

/-- The class function of `S_n` attached to the column shape `(1^n)` is the signature
character. -/
theorem schurChar_column (μ : PartIdx n n) (hμ : μ.1 = List.replicate n 1) :
    schurChar μ = fun σ : Perm (Fin n) => ((Equiv.Perm.sign σ : ℤ) : ℚ) := by
  refine eq_of_frobChar_eq (isClassFun_schurChar μ) (fun σ τ => ?_) ?_
  · rw [map_mul, map_mul, Equiv.Perm.sign_inv]
    have h2 : ((Equiv.Perm.sign τ : ℤ) : ℚ) * ((Equiv.Perm.sign τ : ℤ) : ℚ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> norm_num
    push_cast
    linear_combination ((Equiv.Perm.sign σ : ℤ) : ℚ) * h2
  · rw [frobChar_schurChar, hμ, schurPoly_column, frobChar_sign]

end Equiv.Perm
