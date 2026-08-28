/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric

/-!
# The branching rule for Schur polynomials

Following `theories/MPoly/Schur_mpoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove the branching rule: a Schur
polynomial in `m + 1` variables is the sum, over the shapes `nu` obtained from `lam` by
removing a horizontal strip, of the Schur polynomial of shape `nu` in the first `m`
variables times the appropriate power of the last variable.

This is the polynomial form of the recursion `List.kostkaNum_succ` on the largest letter
of a tableau.

## Main results

* `MvPolynomial.schurPoly_branching` : the branching rule.
-/

namespace MvPolynomial

open List MvPolynomial

variable {m : ℕ} {R : Type*} [CommSemiring R]

/-! ### Splitting off the last variable -/

/-- The exponent vector of the first `m` variables of a monomial in `m + 1` variables. -/
noncomputable def restrictLast (d : Fin (m + 1) →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i : Fin m => d i.castSucc) (fun _ _ => Finset.mem_univ _)

@[simp] lemma restrictLast_apply (d : Fin (m + 1) →₀ ℕ) (i : Fin m) :
    restrictLast d i = d i.castSucc := rfl

lemma mapDomain_castSucc_apply_castSucc (u : Fin m →₀ ℕ) (i : Fin m) :
    (Finsupp.mapDomain Fin.castSucc u) i.castSucc = u i :=
  Finsupp.mapDomain_apply (Fin.castSucc_injective m) u i

lemma mapDomain_castSucc_apply_last (u : Fin m →₀ ℕ) :
    (Finsupp.mapDomain Fin.castSucc u) (Fin.last m) = 0 := by
  refine Finsupp.mapDomain_notin_range u (Fin.last m) ?_
  rintro ⟨i, hi⟩
  exact (Fin.castSucc_lt_last i).ne hi

/-- A monomial in `m + 1` variables is determined by its exponent of the last variable and
the exponents of the others. -/
lemma eq_mapDomain_add_single_iff {d : Fin (m + 1) →₀ ℕ} {u : Fin m →₀ ℕ} {j : ℕ} :
    d = Finsupp.mapDomain Fin.castSucc u + Finsupp.single (Fin.last m) j ↔
      d (Fin.last m) = j ∧ restrictLast d = u := by
  constructor
  · rintro rfl
    refine ⟨by simp [mapDomain_castSucc_apply_last], ?_⟩
    ext i
    simp [mapDomain_castSucc_apply_castSucc, (Fin.castSucc_lt_last i).ne]
  · rintro ⟨hlast, rfl⟩
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · simp [mapDomain_castSucc_apply_castSucc, (Fin.castSucc_lt_last i').ne]
    · simp [mapDomain_castSucc_apply_last, hlast]

/-- The coefficients of a polynomial in the first `m` variables multiplied by a power of the
last one. -/
lemma coeff_rename_castSucc_mul_pow (P : MvPolynomial (Fin m) R) (j : ℕ)
    (d : Fin (m + 1) →₀ ℕ) :
    coeff d (rename Fin.castSucc P * X (Fin.last m) ^ j)
      = if d (Fin.last m) = j then coeff (restrictLast d) P else 0 := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [rename_monomial, X_pow_eq_monomial, monomial_mul, mul_one, coeff_monomial,
      coeff_monomial]
    by_cases hlast : d (Fin.last m) = j
    · rw [if_pos hlast]
      by_cases hu : u = restrictLast d
      · rw [if_pos hu, if_pos (eq_mapDomain_add_single_iff.2 ⟨hlast, hu.symm⟩).symm]
      · rw [if_neg hu, if_neg fun h => hu (eq_mapDomain_add_single_iff.1 h.symm).2.symm]
    · rw [if_neg hlast, if_neg fun h => hlast (eq_mapDomain_add_single_iff.1 h.symm).1]
  | add P Q hP hQ =>
    rw [map_add, add_mul, coeff_add, hP, hQ, coeff_add]
    split_ifs
    · rfl
    · rw [add_zero]

/-! ### Restricting the content to the first letters -/

lemma finContent_castSucc (d : Fin (m + 1) →₀ ℕ) (i : ℕ) (hi : i < m) :
    finContent (m + 1) d i = finContent m (restrictLast d) i := by
  rw [finContent, finContent, dif_pos (by omega), dif_pos hi]
  rfl

lemma finContent_last (d : Fin (m + 1) →₀ ℕ) :
    finContent (m + 1) d m = d (Fin.last m) := by
  rw [finContent, dif_pos (Nat.lt_succ_self m)]
  rfl

/-! ### The branching rule -/

open Classical in
/-- **The branching rule**: a Schur polynomial in `m + 1` variables is the sum, over the
shapes `nu` such that `lam / nu` is a horizontal strip, of the Schur polynomial of shape
`nu` in the first `m` variables times the power of the last variable filling up the
strip. -/
theorem schurPoly_branching (lam : List ℕ) (hlam : IsPart lam) :
    schurPoly (Fin (m + 1)) R lam
      = ∑ k ∈ Finset.range (lam.sum + 1),
          ∑ nu : {p : List ℕ // IsPart p ∧ p.sum = k},
            if HorizStrip lam nu.1 then
              rename Fin.castSucc (schurPoly (Fin m) R nu.1) * X (Fin.last m) ^ (lam.sum - k)
            else 0 := by
  classical
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_schurPoly_eq_kostkaNum, coeff_sum]
  have hterm : ∀ k ∈ Finset.range (lam.sum + 1),
      coeff d (∑ nu : {p : List ℕ // IsPart p ∧ p.sum = k},
        if HorizStrip lam nu.1 then
          rename Fin.castSucc (schurPoly (Fin m) R nu.1) * X (Fin.last m) ^ (lam.sum - k)
        else 0)
      = if d (Fin.last m) = lam.sum - k then
          ((∑ nu : {p : List ℕ // IsPart p ∧ p.sum = k},
            if HorizStrip lam nu.1 then
              kostkaNum m nu.1 (finContent (m + 1) d) else 0 : ℕ) : R)
        else 0 := by
    intro k _
    rw [coeff_sum]
    by_cases hlast : d (Fin.last m) = lam.sum - k
    · rw [if_pos hlast, Nat.cast_sum]
      refine Finset.sum_congr rfl fun nu _ => ?_
      by_cases hstrip : HorizStrip lam nu.1
      · rw [if_pos hstrip, if_pos hstrip, coeff_rename_castSucc_mul_pow, if_pos hlast,
          coeff_schurPoly_eq_kostkaNum]
        exact congrArg _ (kostkaNum_congr m nu.1
          fun i hi => (finContent_castSucc d i hi).symm)
      · rw [if_neg hstrip, if_neg hstrip, coeff_zero, Nat.cast_zero]
    · rw [if_neg hlast, Finset.sum_eq_zero fun nu _ => ?_]
      by_cases hstrip : HorizStrip lam nu.1
      · rw [if_pos hstrip, coeff_rename_castSucc_mul_pow, if_neg hlast]
      · rw [if_neg hstrip, coeff_zero]
  rw [Finset.sum_congr rfl hterm]
  by_cases hle : d (Fin.last m) ≤ lam.sum
  · have hk : lam.sum - d (Fin.last m) ∈ Finset.range (lam.sum + 1) :=
      Finset.mem_range.2 (by omega)
    rw [Finset.sum_eq_single (lam.sum - d (Fin.last m)) ?_ (fun h => absurd hk h)]
    · rw [if_pos (by omega)]
      refine congrArg _ (kostkaNum_succ hlam ?_)
      rw [finContent_last]
      omega
    · intro k hk hne
      have hkk := Finset.mem_range.1 hk
      exact if_neg (by omega)
  · have hzero : kostkaNum (m + 1) lam (finContent (m + 1) d) = 0 := by
      refine kostkaNum_eq_zero_of_sum_ne _ _ _ fun hsum => hle ?_
      have hle' : finContent (m + 1) d m ≤ ∑ i ∈ Finset.range (m + 1), finContent (m + 1) d i :=
        Finset.single_le_sum (f := finContent (m + 1) d) (fun i _ => Nat.zero_le _)
          (Finset.mem_range.2 (Nat.lt_succ_self m))
      rw [finContent_last] at hle'
      omega
    rw [hzero, Nat.cast_zero, Finset.sum_eq_zero]
    intro k hk
    exact if_neg (by
      have := Finset.mem_range.1 hk
      omega)

end MvPolynomial
