/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Cauchy.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.CycleIndexGeneral

/-!
# The Cauchy kernel in terms of the power sums

Following `theories/MPoly/Cauchy.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we expand the Cauchy kernel in the
power sums: degree by degree,

`∑_{lam ⊢ n} s_lam(x) s_lam(y) = ∑_{lam ⊢ n} p_lam(x) p_lam(y) / z_lam`

over a commutative ring containing the rationals.

The proof compares the two sides with the cycle index sums of
`Mathlib/RingTheory/MvPolynomial/Symmetric/Basis/CycleIndexGeneral.lean` for the family `P_r
= p_r(x) p_r(y)`: the right-hand side is such a sum by definition, and the left-hand side, which is
the sum `∑_a h_{a_1}(x) ⋯ h_{a_k}(x) y^a` of
`Mathlib/RingTheory/MvPolynomial/Symmetric/Cauchy/Basic.lean`, satisfies the characterising
recursion `n · F n = ∑_{r=1}^n P_r · F (n-r)`, as one sees on the coefficient of each monomial `y^d`
using the recursion `n · h_n = ∑_{r=1}^n p_r · h_{n-r}`.

## Main results

* `MvPolynomial.coeff_cauchyRHS` : the coefficient of `y^d` in the Cauchy kernel.
* `MvPolynomial.nsmul_cauchyRHS` : the recursion satisfied by the Cauchy kernel.
* `MvPolynomial.power_sum_cauchy` : the Cauchy identity in terms of the power sums.
-/

namespace MvPolynomial

open List MvPolynomial

/-! ### The coefficients of the Cauchy kernel -/

/-- The coefficient of the monomial `y^d` in the Cauchy kernel of degree `n`. -/
lemma coeff_cauchyRHS (m k n : ℕ) (R : Type*) [CommRing R] (d : Fin k →₀ ℕ) :
    coeff d (cauchyRHS m k n R)
      = if ∑ j, d j = n then ∏ j : Fin k, hsymm (Fin m) R (d j) else 0 := by
  classical
  rw [cauchyRHS, coeff_sum]
  have hterm : ∀ a ∈ Finset.Nat.antidiagonalTuple k n,
      coeff d (C (∏ j : Fin k, hsymm (Fin m) R (a j))
          * ∏ j : Fin k, (X j : MvPolynomial (Fin k) (MvPolynomial (Fin m) R)) ^ a j)
        = if a = (d : Fin k → ℕ) then ∏ j : Fin k, hsymm (Fin m) R (d j) else 0 := by
    intro a _
    have hmon : (∏ j : Fin k, (X j : MvPolynomial (Fin k) (MvPolynomial (Fin m) R)) ^ a j)
        = monomial (Finsupp.equivFunOnFinite.symm a) 1 :=
      prod_X_pow_eq_monomial_finsupp (Finsupp.equivFunOnFinite.symm a)
    rw [hmon, C_mul_monomial, mul_one, coeff_monomial]
    by_cases h : a = (d : Fin k → ℕ)
    · subst h
      rw [if_pos rfl, if_pos (Finsupp.equivFunOnFinite_symm_coe d)]
    · rw [if_neg h, if_neg]
      intro hc
      exact h (by rw [← hc]; rfl)
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq' (Finset.Nat.antidiagonalTuple k n) (d : Fin k → ℕ)
      (fun _ => ∏ j : Fin k, hsymm (Fin m) R (d j))]
  simp only [Finset.Nat.mem_antidiagonalTuple]

/-! ### The recursion satisfied by the Cauchy kernel -/

/-- Removing `r` from the `j`-th exponent of a monomial. -/
lemma sum_sub_single {k : ℕ} (d : Fin k →₀ ℕ) (j : Fin k) {r : ℕ} (hr : r ≤ d j) :
    ∑ i, (d - Finsupp.single j r) i = (∑ i, d i) - r := by
  classical
  have hj : ∀ i, (d - Finsupp.single j r) i = if i = j then d j - r else d i := by
    intro i
    by_cases h : i = j <;> simp [h]
  rw [Finset.sum_congr rfl fun i _ => hj i]
  have hsplit : ∑ i, (if i = j then d j - r else d i)
      = (d j - r) + ∑ i ∈ Finset.univ.erase j, d i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), if_pos rfl]
    congr 1
    exact Finset.sum_congr rfl fun i hi => if_neg (Finset.mem_erase.1 hi).1
  have hsplit2 : ∑ i, d i = d j + ∑ i ∈ Finset.univ.erase j, d i :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  omega

/-- The product of the complete homogeneous symmetric polynomials of the exponents of a
monomial, after removing `r` from the `j`-th exponent. -/
lemma prod_hsymm_sub_single (m : ℕ) {k : ℕ} (R : Type*) [CommRing R] (d : Fin k →₀ ℕ)
    (j : Fin k) (r : ℕ) :
    (∏ i : Fin k, hsymm (Fin m) R ((d - Finsupp.single j r) i))
      = hsymm (Fin m) R (d j - r) * ∏ i ∈ Finset.univ.erase j, hsymm (Fin m) R (d i) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun i => hsymm (Fin m) R ((d - Finsupp.single j r) i))
    (Finset.mem_univ j)]
  congr 1
  · congr 1
    simp
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := (Finset.mem_erase.1 hi).1
    congr 1
    simp [hij]

/-- **The recursion satisfied by the Cauchy kernel**:
`n · F n = ∑_{r=1}^n p_r(x) p_r(y) · F (n-r)`. -/
lemma nsmul_cauchyRHS (m k n : ℕ) (R : Type*) [CommRing R] :
    (n : ℕ) • cauchyRHS m k n R
      = ∑ r ∈ Finset.Icc 1 n,
          (C (psum (Fin m) R r) * psum (Fin k) (MvPolynomial (Fin m) R) r)
            * cauchyRHS m k (n - r) R := by
  classical
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_smul, coeff_cauchyRHS, coeff_sum]
  have hterm : ∀ r : ℕ,
      coeff d ((C (psum (Fin m) R r) * psum (Fin k) (MvPolynomial (Fin m) R) r)
          * cauchyRHS m k (n - r) R)
        = ∑ j : Fin k, if r ≤ d j then
            psum (Fin m) R r * coeff (d - Finsupp.single j r) (cauchyRHS m k (n - r) R)
            else 0 := by
    intro r
    have hexp : (C (psum (Fin m) R r) * psum (Fin k) (MvPolynomial (Fin m) R) r)
        * cauchyRHS m k (n - r) R
        = ∑ j : Fin k, C (psum (Fin m) R r) *
            ((monomial (Finsupp.single j r) (1 : MvPolynomial (Fin m) R))
              * cauchyRHS m k (n - r) R) := by
      have hps : psum (Fin k) (MvPolynomial (Fin m) R) r
          = ∑ j : Fin k, (monomial (Finsupp.single j r) (1 : MvPolynomial (Fin m) R)) := by
        rw [psum]
        exact Finset.sum_congr rfl fun j _ => X_pow_eq_monomial
      rw [hps, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_assoc]
    rw [hexp, coeff_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_C_mul, coeff_monomial_mul', one_mul]
    by_cases hle : r ≤ d j
    · rw [if_pos (Finsupp.single_le_iff.2 hle), if_pos hle]
    · rw [if_neg (fun h => hle (Finsupp.single_le_iff.1 h)), if_neg hle, mul_zero]
  rw [Finset.sum_congr rfl fun r _ => hterm r]
  by_cases hd : ∑ j, d j = n
  · rw [if_pos hd]
    -- each `j` contributes `d j • ∏ h`, and the exponents sum to `n`
    rw [Finset.sum_comm]
    have hj : ∀ j : Fin k,
        (∑ r ∈ Finset.Icc 1 n, if r ≤ d j then
            psum (Fin m) R r * coeff (d - Finsupp.single j r) (cauchyRHS m k (n - r) R)
            else 0)
          = (d j : ℕ) • ∏ i : Fin k, hsymm (Fin m) R (d i) := by
      intro j
      have hdjn : d j ≤ n := by
        rw [← hd]
        exact Finset.single_le_sum (f := fun i => d i) (fun i _ => Nat.zero_le _)
          (Finset.mem_univ j)
      have hstep : ∀ r ∈ Finset.Icc 1 n,
          (if r ≤ d j then
            psum (Fin m) R r * coeff (d - Finsupp.single j r) (cauchyRHS m k (n - r) R)
            else 0)
            = if r ∈ Finset.Icc 1 (d j) then
                psum (Fin m) R r * hsymm (Fin m) R (d j - r)
                  * ∏ i ∈ Finset.univ.erase j, hsymm (Fin m) R (d i)
              else 0 := by
        intro r hr
        rw [Finset.mem_Icc] at hr
        by_cases hle : r ≤ d j
        · rw [if_pos hle, if_pos (Finset.mem_Icc.2 ⟨hr.1, hle⟩), coeff_cauchyRHS,
            if_pos (by rw [sum_sub_single d j hle, hd]),
            prod_hsymm_sub_single m R d j r, mul_assoc]
        · rw [if_neg hle, if_neg (fun h => hle (Finset.mem_Icc.1 h).2)]
      rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter,
        Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (by
          intro r hr
          rw [Finset.mem_Icc] at hr ⊢
          exact ⟨hr.1, le_trans hr.2 hdjn⟩), ← Finset.sum_mul,
        ← nsmul_hsymm_eq_sum_psum_mul_hsymm m (d j) R, smul_mul_assoc,
        Finset.mul_prod_erase Finset.univ (fun i => hsymm (Fin m) R (d i)) (Finset.mem_univ j)]
    rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.sum_smul, hd]
  · rw [if_neg hd, smul_zero]
    refine (Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun j _ => ?_).symm
    rw [Finset.mem_Icc] at hr
    dsimp only
    by_cases hle : r ≤ d j
    · rw [if_pos hle, coeff_cauchyRHS, if_neg, mul_zero]
      rw [sum_sub_single d j hle]
      have hdj : d j ≤ ∑ i, d i :=
        Finset.single_le_sum (f := fun i => d i) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    · rw [if_neg hle]

/-! ### The Cauchy identity in terms of the power sums -/

/-- The Cauchy kernel in degree `0` is `1`. -/
lemma cauchyRHS_zero (m k : ℕ) (R : Type*) [CommRing R] : cauchyRHS m k 0 R = 1 := by
  classical
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_cauchyRHS, coeff_one]
  by_cases hd : d = 0
  · subst hd
    simp
  · rw [if_neg (show ¬(0 = d) from fun h => hd h.symm), if_neg]
    intro hsum
    refine hd (Finsupp.ext fun i => ?_)
    exact (Finset.sum_eq_zero_iff.1 hsum) i (Finset.mem_univ i)

/-- The Cauchy kernel is the cycle index sum of the family `p_r(x) p_r(y)`. -/
theorem cauchyRHS_eq_genCycleIndexSum (m k n : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] :
    cauchyRHS m k n R
      = genCycleIndexSum
          (fun r => C (psum (Fin m) R r) * psum (Fin k) (MvPolynomial (Fin m) R) r) n := by
  refine eq_genCycleIndexSum_of_rec _ (fun n => cauchyRHS m k n R) (cauchyRHS_zero m k R)
    (fun n => ?_) n
  change (n : ℚ) • cauchyRHS m k n R
    = ∑ r ∈ Finset.Icc 1 n,
        (C (psum (Fin m) R r) * psum (Fin k) (MvPolynomial (Fin m) R) r) * cauchyRHS m k (n - r) R
  rw [Nat.cast_smul_eq_nsmul ℚ]
  exact nsmul_cauchyRHS m k n R

/-- The product of the family `p_r(x) p_r(y)` over a partition. -/
lemma genProd_psum_mul (m k : ℕ) (R : Type*) [CommRing R] (lam : List ℕ) :
    genProd (fun r => C (psum (Fin m) R r) * psum (Fin k) (MvPolynomial (Fin m) R) r) lam
      = C (pProd m R lam) * pProd k (MvPolynomial (Fin m) R) lam := by
  induction lam with
  | nil => simp [pProd]
  | cons a l ih =>
    rw [genProd_cons, ih, pProd_cons, pProd_cons, map_mul]
    ring

/-- **The Cauchy identity in terms of the power sums**. -/
theorem power_sum_cauchy (m k n : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] :
    (∑ lam ∈ partFinset n,
        C (schurPoly (Fin m) R lam) * schurPoly (Fin k) (MvPolynomial (Fin m) R) lam
      : MvPolynomial (Fin k) (MvPolynomial (Fin m) R))
      = ∑ lam ∈ partFinset n,
          ((zcard lam : ℚ))⁻¹ •
            (C (pProd m R lam) * pProd k (MvPolynomial (Fin m) R) lam) := by
  rw [show (∑ lam ∈ partFinset n,
      C (schurPoly (Fin m) R lam) * schurPoly (Fin k) (MvPolynomial (Fin m) R) lam
        : MvPolynomial (Fin k) (MvPolynomial (Fin m) R)) = cauchyRHS m k n R from cauchy m k n R,
    cauchyRHS_eq_genCycleIndexSum, genCycleIndexSum]
  exact Finset.sum_congr rfl fun lam _ => by rw [genProd_psum_mul]

end MvPolynomial
