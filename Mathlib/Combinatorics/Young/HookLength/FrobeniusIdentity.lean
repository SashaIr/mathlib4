/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.HookLength.Formula

/-!
# The Frobenius identity

A Lean 4 port of `theories/HookFormula/Frobenius_ident.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

Combining the Robinson–Schensted enumeration `∑_λ (f^λ)² = n !` of
`Mathlib/Combinatorics/Young/RobinsonSchensted/Counting.lean` with the hook length formula
`f^λ · ∏ h(i, j) = n !` of `Mathlib/Combinatorics/Young/HookLength/Formula.lean` gives the
*Frobenius identity*

`n ! = ∑_{λ ⊢ n} (n ! / ∏_{(i, j) ∈ λ} h(i, j))²`,

or, dividing by `(n !)²` in the rationals,

`1 / n ! = ∑_{λ ⊢ n} 1 / (∏_{(i, j) ∈ λ} h(i, j))²`.

## Main results

* `Young.factorial_eq_sum_sq_factorial_div_hookProd` : the Frobenius identity
  (Coq `Frobenius_ident`).
* `Young.inv_factorial_eq_sum_inv_sq_hookProd` : its rational form
  (Coq `Frobenius_ident_rat`).
-/

@[expose] public section

namespace Young

open List

open Finset

/-- The number of standard Young tableaux of shape a partition of `n`, as a rational
number: it is `n !` divided by the product of the hook lengths. -/
lemma cast_numStdTab_partsList (n : ℕ) (η : Nat.Partition n) :
    (numStdTab η.partsList : ℚ) = (Nat.factorial n : ℚ) / (hookProd η.partsList : ℚ) := by
  have hpart : IsPart η.partsList := Nat.Partition.isPart_partsList η
  have hpos : (0 : ℚ) < (hookProd η.partsList : ℚ) := by
    exact_mod_cast hookProd_pos hpart
  rw [eq_div_iff hpos.ne', ← Nat.cast_mul, numStdTab_mul_hookProd hpart,
    Nat.Partition.sum_partsList]

/-- **The Frobenius identity** (Coq `Frobenius_ident`): `n !` is the sum over the
partitions `λ` of `n` of the squares of `n !` divided by the product of the hook lengths
of `λ`. -/
theorem factorial_eq_sum_sq_factorial_div_hookProd (n : ℕ) :
    Nat.factorial n =
      ∑ η : Nat.Partition n, (Nat.factorial n / hookProd η.partsList) ^ 2 := by
  have h : ∀ η : Nat.Partition n,
      numStdTab η.partsList = Nat.factorial n / hookProd η.partsList := fun η ↦ by
    rw [numStdTab_eq_factorial_div_hookProd (Nat.Partition.isPart_partsList η),
      Nat.Partition.sum_partsList]
  calc Nat.factorial n = ∑ η : Nat.Partition n, (numStdTab η.partsList) ^ 2 :=
        (sum_sq_numStdTab n).symm
    _ = _ := Finset.sum_congr rfl fun η _ ↦ by rw [h η]

/-- **The Frobenius identity** in its rational form (Coq `Frobenius_ident_rat`): the sum
over the partitions `λ` of `n` of the inverses of the squares of the products of the hook
lengths of `λ` is `1 / n !`. -/
theorem inv_factorial_eq_sum_inv_sq_hookProd (n : ℕ) :
    (1 : ℚ) / (Nat.factorial n : ℚ) =
      ∑ η : Nat.Partition n, 1 / (hookProd η.partsList : ℚ) ^ 2 := by
  have hfac : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have h : ∑ η : Nat.Partition n, (numStdTab η.partsList : ℚ) ^ 2
      = (Nat.factorial n : ℚ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℚ)) (sum_sq_numStdTab n)
  have h2 : (∑ η : Nat.Partition n, 1 / (hookProd η.partsList : ℚ) ^ 2)
      * (Nat.factorial n : ℚ) ^ 2 = (Nat.factorial n : ℚ) := by
    rw [Finset.sum_mul]
    calc ∑ η : Nat.Partition n,
          1 / (hookProd η.partsList : ℚ) ^ 2 * (Nat.factorial n : ℚ) ^ 2
        = ∑ η : Nat.Partition n, (numStdTab η.partsList : ℚ) ^ 2 :=
          Finset.sum_congr rfl fun η _ ↦ by
            rw [cast_numStdTab_partsList n η, div_pow]
            ring
      _ = (Nat.factorial n : ℚ) := h
  rw [eq_div_of_mul_eq (pow_ne_zero 2 hfac) h2, sq]
  field_simp

end Young
