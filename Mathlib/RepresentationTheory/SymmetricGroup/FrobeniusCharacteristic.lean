/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.CycleIndex
import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.CompleteHomogeneous
import Mathlib.GroupTheory.Perm.SymmetricGroup.Tower

/-!
# The Frobenius characteristic map

This file ports Coq-Combi's `SymGroup/Frobenius_char.v` together with the class-function
part of `SymGroup/towerSn.v`.

To a class function `f` on the symmetric group `S_n` one associates the symmetric
polynomial `ch(f) = (1 / n !) ∑_{σ ∈ S_n} f(σ) · p_{cycleType σ}`, its *Frobenius
characteristic*.  The main theorem is that the Frobenius characteristic turns the induction
product of class functions (induction from `S_m × S_n`, embedded in `S_{m+n}` by
`Equiv.Perm.tinj`, to `S_{m+n}`) into the product of symmetric polynomials.

## Main definitions

* `Equiv.Perm.IsClassFun` : a function on `S_n` which is constant on conjugacy classes.
* `Equiv.Perm.indProd f g` : the induction product of two class functions
  (Coq: the `'Ind` product of `towerSn.v`).
* `Equiv.Perm.frobChar m f` : the Frobenius characteristic of `f`, as a symmetric polynomial in
  `m` variables over `ℚ` (Coq: `Frobenius_char`).

## Main results

* `Equiv.Perm.indProd_isClassFun` : the induction product is again a class function.
* `Equiv.Perm.frobChar_indProd` : `ch(f ⊗ g) = ch(f) · ch(g)` (Coq: `Frobenius_char_ind_morph`).
* `Equiv.Perm.frobChar_classIndicator` : the characteristic of the indicator function of the
  class of cycle type `λ` is `p_λ / z_λ`.
* `Equiv.Perm.frobChar_comp_cycleTypeList` : the characteristic of a function of the cycle type
  is `∑_{lam ⊢ n} c(lam) · p_lam / z_lam`.
* `Equiv.Perm.frobChar_indTrivYoung` : the characteristic of the trivial character induced from
  a Young subgroup is the product `h_{l_1} ⋯ h_{l_r}`.
* `Equiv.Perm.frobChar_one`, `Equiv.Perm.frobChar_sign` : the characteristics of the trivial and of
  the signature characters are the complete homogeneous and the elementary symmetric
  polynomials `h_n` and `e_n`.
-/

open Equiv MvPolynomial List

namespace Equiv.Perm


/-! ### Products of power sums along the tower of symmetric groups -/

/-- The product of power sums of a concatenation of lists. -/
lemma pProd_append (m : ℕ) (R : Type*) [CommRing R] (l₁ l₂ : List ℕ) :
    pProd m R (l₁ ++ l₂) = pProd m R l₁ * pProd m R l₂ := by
  rw [pProd, pProd, pProd, List.map_append, List.prod_append]

/-- The power sum product attached to the cycle type of a glued pair of permutations is the
product of the two power sum products. -/
lemma pProd_cycleTypeList_tinj (k : ℕ) (R : Type*) [CommRing R] {m n : ℕ}
    (u : Perm (Fin m)) (v : Perm (Fin n)) :
    pProd k R (cycleTypeList (tinj m n (u, v)))
      = pProd k R (cycleTypeList u) * pProd k R (cycleTypeList v) := by
  rw [cycleTypeList_tinj, ← pProd_append]
  refine pProd_of_perm k R (Multiset.coe_eq_coe.mp ?_)
  rw [coe_sortDesc, Multiset.coe_add]

/-- The list-based cycle type is invariant under conjugation. -/
lemma cycleTypeList_conj {n : ℕ} (sigma tau : Perm (Fin n)) :
    cycleTypeList (tau⁻¹ * sigma * tau) = cycleTypeList sigma :=
  cycleTypeList_eq_iff_isConj.2 (isConj_iff.2 ⟨tau, by group⟩)

/-! ### Class functions and the induction product -/

/-- A function on the symmetric group is a class function when it is constant on conjugacy
classes. -/
def IsClassFun {n : ℕ} (f : Perm (Fin n) → ℚ) : Prop :=
  ∀ sigma tau : Perm (Fin n), f (tau⁻¹ * sigma * tau) = f sigma

/-- The induction product of two class functions `f` on `S_m` and `g` on `S_n`: the class
function on `S_{m+n}` induced from the function `(u, v) ↦ f(u) · g(v)` on the image of
`Equiv.Perm.tinj`. -/
noncomputable def indProd {m n : ℕ} (f : Perm (Fin m) → ℚ) (g : Perm (Fin n) → ℚ) :
    Perm (Fin (m + n)) → ℚ := fun sigma =>
  ((Nat.factorial m : ℚ) * (Nat.factorial n : ℚ))⁻¹ * ∑ tau : Perm (Fin (m + n)),
    ∑ x : Perm (Fin m) × Perm (Fin n),
      if tinj m n x = tau⁻¹ * sigma * tau then f x.1 * g x.2 else 0

/-- The induction product is a class function. -/
theorem indProd_isClassFun {m n : ℕ} (f : Perm (Fin m) → ℚ) (g : Perm (Fin n) → ℚ) :
    IsClassFun (indProd f g) := by
  intro sigma pi
  simp only [indProd]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft pi) _ _ fun tau => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  have hc : (pi * tau)⁻¹ * sigma * (pi * tau) = tau⁻¹ * (pi⁻¹ * sigma * pi) * tau := by group
  simp only [Equiv.coe_mulLeft, hc]

/-! ### The Frobenius characteristic -/

/-- The Frobenius characteristic of a class function `f` on `S_n`, as a symmetric
polynomial in `m` variables: `ch(f) = (1 / n !) ∑_{σ} f(σ) · p_{cycleType σ}`. -/
noncomputable def frobChar (m : ℕ) {n : ℕ} (f : Perm (Fin n) → ℚ) :
    MvPolynomial (Fin m) ℚ :=
  ((Nat.factorial n : ℚ))⁻¹ • ∑ sigma : Perm (Fin n), f sigma • pProd m ℚ (cycleTypeList sigma)

/-- The Frobenius characteristic is additive. -/
lemma frobChar_add (m : ℕ) {n : ℕ} (f g : Perm (Fin n) → ℚ) :
    frobChar m (f + g) = frobChar m f + frobChar m g := by
  simp only [frobChar, Pi.add_apply, add_smul, Finset.sum_add_distrib, smul_add]

/-- The Frobenius characteristic commutes with multiplication by a rational scalar. -/
lemma frobChar_smul (m : ℕ) {n : ℕ} (c : ℚ) (f : Perm (Fin n) → ℚ) :
    frobChar m (c • f) = c • frobChar m f := by
  simp only [frobChar, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
  rw [smul_comm]


/-- The Frobenius characteristic of the indicator function of the conjugacy class of cycle
type `λ` is `p_λ / z_λ`. -/
theorem frobChar_classIndicator (m : ℕ) {n : ℕ} {lam : List ℕ} (hlam : IsPart lam)
    (hsum : lam.sum = n) :
    frobChar m (fun sigma : Perm (Fin n) => if cycleTypeList sigma = lam then 1 else 0)
      = ((zcard lam : ℚ))⁻¹ • pProd m ℚ lam := by
  classical
  have hz : (zcard lam : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (zcard_pos hlam).ne'
  have hcard := card_cycleTypeList_mul_zcard (n := n) hlam hsum
  have key : ∀ sigma : Perm (Fin n),
      (if cycleTypeList sigma = lam then (1 : ℚ) else 0) • pProd m ℚ (cycleTypeList sigma)
        = if cycleTypeList sigma = lam then pProd m ℚ lam else 0 := by
    intro sigma
    by_cases h : cycleTypeList sigma = lam <;> simp [h]
  rw [frobChar, Finset.sum_congr rfl fun sigma _ => key sigma, Finset.sum_ite,
    Finset.sum_const, Finset.sum_const_zero, add_zero, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  have hne : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [inv_mul_eq_div]
  field_simp
  exact_mod_cast hcard

/-- The Frobenius characteristic of the trivial character of `S_n` is the complete
homogeneous symmetric polynomial `h_n`. -/
theorem frobChar_one (m n : ℕ) :
    frobChar m (fun _ : Perm (Fin n) => (1 : ℚ)) = hsymm (Fin m) ℚ n := by
  have hne : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [frobChar]
  simp only [one_smul]
  rw [← factorial_nsmul_hsymm_eq_sum_perm m n ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    inv_mul_cancel₀ hne, one_smul]

/-- **The Frobenius characteristic is a morphism for the induction product**: the
characteristic of the induction product of two class functions is the product of their
characteristics (Coq: `Frobenius_char_ind_morph`). -/
theorem frobChar_indProd (k : ℕ) {m n : ℕ} (f : Perm (Fin m) → ℚ) (g : Perm (Fin n) → ℚ) :
    frobChar k (indProd f g) = frobChar k f * frobChar k g := by
  classical
  have hm : (Nat.factorial m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hn : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hmn : (Nat.factorial (m + n) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  -- the induced sum only depends on the pair of permutations
  have key : ∀ tau : Perm (Fin (m + n)),
      ∑ sigma : Perm (Fin (m + n)), ∑ x : Perm (Fin m) × Perm (Fin n),
          (if tinj m n x = tau⁻¹ * sigma * tau then f x.1 * g x.2 else 0)
            • pProd k ℚ (cycleTypeList sigma)
        = ∑ x : Perm (Fin m) × Perm (Fin n),
            (f x.1 * g x.2) • pProd k ℚ (cycleTypeList (tinj m n x)) := by
    intro tau
    have h1 : ∑ sigma : Perm (Fin (m + n)), ∑ x : Perm (Fin m) × Perm (Fin n),
          (if tinj m n x = tau⁻¹ * sigma * tau then f x.1 * g x.2 else 0)
            • pProd k ℚ (cycleTypeList sigma)
        = ∑ sigma : Perm (Fin (m + n)), ∑ x : Perm (Fin m) × Perm (Fin n),
          (if tinj m n x = sigma then f x.1 * g x.2 else 0)
            • pProd k ℚ (cycleTypeList sigma) := by
      refine Fintype.sum_equiv ((Equiv.mulLeft tau⁻¹).trans (Equiv.mulRight tau)) _ _
        fun sigma => ?_
      simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight,
        cycleTypeList_conj sigma tau]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_eq Finset.univ (tinj m n x)
      (fun sigma => (f x.1 * g x.2) • pProd k ℚ (cycleTypeList sigma)), if_pos (Finset.mem_univ _)]
  have hterm : ∀ sigma : Perm (Fin (m + n)),
      indProd f g sigma • pProd k ℚ (cycleTypeList sigma)
        = ((Nat.factorial m : ℚ) * (Nat.factorial n : ℚ))⁻¹ •
            ∑ tau : Perm (Fin (m + n)), ∑ x : Perm (Fin m) × Perm (Fin n),
              (if tinj m n x = tau⁻¹ * sigma * tau then f x.1 * g x.2 else 0)
                • pProd k ℚ (cycleTypeList sigma) := by
    intro sigma
    rw [indProd, mul_smul, Finset.sum_smul]
    exact congrArg _ (Finset.sum_congr rfl fun tau _ => Finset.sum_smul)
  have hcardperm : (Finset.univ : Finset (Perm (Fin (m + n)))).card = Nat.factorial (m + n) := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hsum : ∑ sigma : Perm (Fin (m + n)),
        indProd f g sigma • pProd k ℚ (cycleTypeList sigma)
      = ((Nat.factorial m : ℚ) * (Nat.factorial n : ℚ))⁻¹ •
          ((Nat.factorial (m + n) : ℚ) • ∑ x : Perm (Fin m) × Perm (Fin n),
            (f x.1 * g x.2) • pProd k ℚ (cycleTypeList (tinj m n x))) := by
    rw [Finset.sum_congr rfl fun sigma _ => hterm sigma, ← Finset.smul_sum, Finset.sum_comm]
    congr 1
    rw [Finset.sum_congr rfl fun tau _ => key tau, Finset.sum_const, hcardperm,
      ← Nat.cast_smul_eq_nsmul ℚ]
  have hprod : ∑ x : Perm (Fin m) × Perm (Fin n),
        (f x.1 * g x.2) • pProd k ℚ (cycleTypeList (tinj m n x))
      = (∑ u : Perm (Fin m), f u • pProd k ℚ (cycleTypeList u))
        * ∑ v : Perm (Fin n), g v • pProd k ℚ (cycleTypeList v) := by
    rw [Finset.sum_mul_sum]
    rw [← Finset.sum_product']
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [pProd_cycleTypeList_tinj, smul_mul_smul_comm, ← smul_eq_mul, smul_assoc]
  rw [frobChar, hsum, hprod, frobChar, frobChar, smul_mul_smul_comm, smul_smul, smul_smul]
  congr 1
  field_simp

/-! ### Characteristic of a function of the cycle type -/

/-- The Frobenius characteristic of a class function given by a function of the cycle type:
each conjugacy class contributes `p_λ / z_λ`. -/
theorem frobChar_comp_cycleTypeList (m : ℕ) {n : ℕ} (c : List ℕ → ℚ) :
    frobChar m (fun sigma : Perm (Fin n) => c (cycleTypeList sigma))
      = ∑ lam ∈ partFinset n, (c lam * ((zcard lam : ℚ))⁻¹) • pProd m ℚ lam := by
  classical
  have hne : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [frobChar, ← Finset.sum_fiberwise_of_maps_to
    (fun sigma _ => cycleTypeList_mem_partFinset sigma)
    (fun sigma : Perm (Fin n) => c (cycleTypeList sigma) • pProd m ℚ (cycleTypeList sigma)),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun lam hlam => ?_
  obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hlam
  have hz : (zcard lam : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (zcard_pos hpart).ne'
  have hcard := card_cycleTypeList_mul_zcard (n := n) hpart hsum
  rw [Finset.sum_congr rfl fun sigma hsigma => by rw [(Finset.mem_filter.1 hsigma).2],
    Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul]
  congr 1
  have hc : ((Finset.univ.filter fun sigma : Perm (Fin n) => cycleTypeList sigma = lam).card : ℚ)
      * (zcard lam : ℚ) = (Nat.factorial n : ℚ) := by exact_mod_cast hcard
  field_simp
  linear_combination c lam * hc

/-- The signature of a permutation in terms of the length of its cycle type. -/
lemma sign_eq_neg_one_pow_length_cycleTypeList {n : ℕ} (sigma : Perm (Fin n)) :
    ((Equiv.Perm.sign sigma : ℤ) : ℚ) = (-1) ^ (n + (cycleTypeList sigma).length) := by
  have hlen : (cycleTypeList sigma).length
      = Multiset.card sigma.cycleType + (n - sigma.support.card) := by
    have : ((cycleTypeList sigma : Multiset ℕ)) = sigma.partition.parts := coe_cycleTypeList sigma
    rw [← Multiset.coe_card, this]
    simp [Equiv.Perm.partition]
  have hsupp : sigma.cycleType.sum = sigma.support.card := Equiv.Perm.sum_cycleType sigma
  have hle : sigma.support.card ≤ n := by simpa using Finset.card_le_univ sigma.support
  have hsign : ((Equiv.Perm.sign sigma : ℤ) : ℚ)
      = (-1) ^ (sigma.cycleType.sum + Multiset.card sigma.cycleType) := by
    rw [Equiv.Perm.sign_of_cycleType]
    push_cast [Units.val_pow_eq_pow_val]
    norm_num
  have hpow2 : ((-1 : ℚ)) ^ (2 * (n - sigma.support.card)) = 1 := by
    rw [pow_mul]; norm_num
  rw [hsign, hlen, hsupp,
    show n + (Multiset.card sigma.cycleType + (n - sigma.support.card))
      = (sigma.support.card + Multiset.card sigma.cycleType) + 2 * (n - sigma.support.card) by
        omega]
  conv_rhs => rw [pow_add, hpow2, mul_one]

/-- The Frobenius characteristic of the signature character of `S_n` is the elementary
symmetric polynomial `e_n`. -/
theorem frobChar_sign (m n : ℕ) :
    frobChar m (fun sigma : Perm (Fin n) => ((Equiv.Perm.sign sigma : ℤ) : ℚ))
      = esymm (Fin m) ℚ n := by
  have hfun : (fun sigma : Perm (Fin n) => ((Equiv.Perm.sign sigma : ℤ) : ℚ))
      = fun sigma : Perm (Fin n) => (-1 : ℚ) ^ (n + (cycleTypeList sigma).length) :=
    funext fun sigma => sign_eq_neg_one_pow_length_cycleTypeList sigma
  rw [hfun, frobChar_comp_cycleTypeList m (fun lam => (-1 : ℚ) ^ (n + lam.length)),
    esymm_eq_signedCycleIndexSum, signedCycleIndexSum]

/-- The characteristic of the character of `S_{m+n}` induced from the trivial character of
`S_m × S_n` is the product `h_m · h_n`. -/
theorem frobChar_indProd_one (k m n : ℕ) :
    frobChar k (indProd (fun _ : Perm (Fin m) => (1 : ℚ)) fun _ : Perm (Fin n) => (1 : ℚ))
      = hsymm (Fin k) ℚ m * hsymm (Fin k) ℚ n := by
  rw [frobChar_indProd, frobChar_one, frobChar_one]

/-! ### Induction from a Young subgroup -/

/-- The character of the symmetric group `S_{l.sum}` induced from the trivial character of
the Young subgroup `S_{l_1} × ... × S_{l_r}`. -/
noncomputable def indTrivYoung : (l : List ℕ) → Perm (Fin l.sum) → ℚ
  | [] => fun _ => 1
  | _ :: t => indProd (fun _ => (1 : ℚ)) (indTrivYoung t)

/-- **The characteristic of the trivial character induced from a Young subgroup** is the
product `h_l = h_{l_1} ⋯ h_{l_r}` of complete homogeneous symmetric polynomials. -/
theorem frobChar_indTrivYoung (k : ℕ) (l : List ℕ) :
    frobChar k (indTrivYoung l) = hProd k ℚ l := by
  induction l with
  | nil => simpa using frobChar_one k 0
  | cons a t ih =>
    rw [indTrivYoung, frobChar_indProd, frobChar_one, ih, hProd, hProd, List.map_cons,
      List.prod_cons]

end Equiv.Perm
