/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RepresentationTheory.SymmetricGroup.SchurCharacterIrreducible
public import Mathlib.RepresentationTheory.SymmetricGroup.SchurCharacterMN
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.LRSymmetry

/-!
# The Littlewood–Richardson rule for the characters of the symmetric group

Continuing the port of Coq-Combi's `SymGroup/Frobenius_char.v`, we transport the
Littlewood–Richardson rule for Schur polynomials along the Frobenius characteristic: the
induction product of the Schur class functions `χ^λ` of `S_m` and `χ^μ` of `S_n` is the
sum, over the partitions `ν` of `m + n`, of `c^ν_{λμ}` copies of `χ^ν` (Coq:
`LR_rule_irrSG`).

## Main results

* `Equiv.Perm.frobChar_schurChar_of_le` : the Frobenius characteristic of `schurChar lam` is the
  Schur polynomial `s_lam`, in any number `k ≥ n` of variables.
* `Equiv.Perm.indProd_schurChar` : **the Littlewood–Richardson rule for characters**,
  `χ^λ ⊙ χ^μ = ∑_ν c^ν_{λμ} χ^ν`.
-/

@[expose] public section

open Equiv MvPolynomial List

namespace Equiv.Perm


variable {n m k M : ℕ}

/-! ### The Frobenius characteristic in more variables -/

/-- Truncation of the variables commutes with the Frobenius characteristic. -/
lemma truncVars_frobChar (h : m ≤ M) (f : Perm (Fin n) → ℚ) :
    truncVars m M ℚ (frobChar M f) = frobChar m f := by
  rw [frobChar, frobChar, map_smul, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun sigma _ => ?_)
  rw [map_smul, truncVars_pProd h (isPart_cycleTypeList sigma)]

/-- The Frobenius characteristic of the Schur class function `schurChar lam` is the Schur
polynomial `s_lam`, in any number `k ≥ n` of variables. -/
theorem frobChar_schurChar_of_le (hnk : n ≤ k) (lam : PartIdx n n) :
    frobChar k (schurChar lam) = schurPoly (Fin k) ℚ lam.1 := by
  refine eq_of_truncVars_eq (le_refl n) hnk (frobChar_mem_symHomogeneousSubmodule hnk _)
    (schurPoly_mem_symHomogeneousSubmodule
      (⟨lam.1, lam.2.1, lam.2.2.1, lam.2.2.2.trans hnk⟩ : PartIdx n k)) ?_
  rw [truncVars_frobChar hnk, frobChar_schurChar,
    truncVars_schurPoly hnk lam.2.1 (le_of_eq lam.2.2.1)]

/-! ### The Littlewood–Richardson rule for characters -/

/-- A scalar multiple of a class function is a class function. -/
lemma IsClassFun.smul {f : Perm (Fin n) → ℚ} (hf : IsClassFun f) (c : ℚ) :
    IsClassFun (c • f) := fun sigma tau => by
  simp only [Pi.smul_apply, hf sigma tau]

/-- **The Littlewood–Richardson rule for the characters of the symmetric group**: the
induction product of the Schur class functions of `S_m` and `S_n` attached to the shapes
`lam` and `mu` is the sum, over the shapes `nu` of size `m + n`, of `c^nu_{lam mu}` copies
of the Schur class function of `S_{m+n}` attached to `nu` (Coq: `LR_rule_irrSG`). -/
theorem indProd_schurChar (lam : PartIdx m m) (mu : PartIdx n n) :
    indProd (schurChar lam) (schurChar mu)
      = ∑ nu : PartIdx (m + n) (m + n),
          (lrCoeff lam.1 mu.1 nu.1 : ℚ) • schurChar nu := by
  classical
  refine eq_of_frobChar_eq (indProd_isClassFun _ _)
    (isClassFun_sum Finset.univ _ fun nu _ => (isClassFun_schurChar nu).smul _) ?_
  rw [frobChar_indProd, frobChar_schurChar_of_le (Nat.le_add_right m n),
    frobChar_schurChar_of_le (Nat.le_add_left n m), frobChar_sum]
  rw [schurPoly_mul_eq_sum_partIdx (by rw [lam.2.2.1, mu.2.2.1]) (le_refl (m + n))]
  refine Finset.sum_congr rfl fun nu _ => ?_
  rw [frobChar_smul, frobChar_schurChar_of_le (le_refl (m + n)),
    ← Nat.cast_smul_eq_nsmul ℚ]

end Equiv.Perm
