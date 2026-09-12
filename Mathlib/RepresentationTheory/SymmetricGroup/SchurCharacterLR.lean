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
induction product of the Schur class functions `χ^μ` of `S_m` and `χ^ν` of `S_n` is the
sum, over the partitions `ρ` of `m + n`, of `c^ρ_{μν}` copies of `χ^ρ` (Coq:
`LR_rule_irrSG`).

## Main results

* `Equiv.Perm.frobChar_schurChar_of_le` : the Frobenius characteristic of `schurChar μ` is the
  Schur polynomial `s_μ`, in any number `k ≥ n` of variables.
* `Equiv.Perm.indProd_schurChar` : **the Littlewood–Richardson rule for characters**,
  `χ^μ ⊙ χ^ν = ∑_ρ c^ρ_{μν} χ^ρ`.
-/

@[expose] public section

open Young

open Equiv MvPolynomial List

namespace Equiv.Perm


variable {n m k M : ℕ}

/-! ### The Frobenius characteristic in more variables -/

/-- Truncation of the variables commutes with the Frobenius characteristic. -/
lemma truncVars_frobChar (h : m ≤ M) (f : Perm (Fin n) → ℚ) :
    truncVars m M ℚ (frobChar M f) = frobChar m f := by
  rw [frobChar, frobChar, map_smul, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun σ _ => ?_)
  rw [map_smul, truncVars_pProd h (isPart_cycleTypeList σ)]

/-- The Frobenius characteristic of the Schur class function `schurChar μ` is the Schur
polynomial `s_μ`, in any number `k ≥ n` of variables. -/
theorem frobChar_schurChar_of_le (hnk : n ≤ k) (μ : Nat.Partition n) :
    frobChar k (schurChar μ) = schurPoly (Fin k) ℚ μ.partsList := by
  refine eq_of_truncVars_eq (le_refl n) hnk (frobChar_mem_symHomogeneousSubmodule hnk _)
    (schurPoly_mem_symHomogeneousSubmodule (natPartitionEquivPartLengthLe hnk μ)) ?_
  rw [truncVars_frobChar hnk, frobChar_schurChar,
    truncVars_schurPoly hnk (Nat.Partition.isPart_partsList μ)
      (le_of_eq (Nat.Partition.sum_partsList μ))]

/-! ### The Littlewood–Richardson rule for characters -/

/-- A scalar multiple of a class function is a class function. -/
lemma IsClassFun.smul {f : Perm (Fin n) → ℚ} (hf : IsClassFun f) (c : ℚ) :
    IsClassFun (c • f) := fun σ τ => by
  simp only [Pi.smul_apply, hf σ τ]

/-- **The Littlewood–Richardson rule for the characters of the symmetric group**: the
induction product of the Schur class functions of `S_m` and `S_n` attached to the shapes
`μ` and `ν` is the sum, over the shapes `ρ` of size `m + n`, of `c^ρ_{μ ν}` copies
of the Schur class function of `S_{m+n}` attached to `ρ` (Coq: `LR_rule_irrSG`). -/
theorem indProd_schurChar (μ : Nat.Partition m) (ν : Nat.Partition n) :
    indProd (schurChar μ) (schurChar ν)
      = ∑ ρ : Nat.Partition (m + n),
          (lrCoeff μ.partsList ν.partsList ρ.partsList : ℚ) • schurChar ρ := by
  classical
  refine eq_of_frobChar_eq (indProd_isClassFun _ _)
    (isClassFun_sum Finset.univ _ fun ρ _ => (isClassFun_schurChar ρ).smul _) ?_
  rw [frobChar_indProd, frobChar_schurChar_of_le (Nat.le_add_right m n),
    frobChar_schurChar_of_le (Nat.le_add_left n m), frobChar_sum]
  rw [schurPoly_mul_eq_sum_partLengthLe
      (by rw [Nat.Partition.sum_partsList, Nat.Partition.sum_partsList]) (le_refl (m + n)),
    ← sum_natPartition_eq_sum_partLengthLe (le_refl (m + n))
      (fun l => lrCoeff μ.partsList ν.partsList l • schurPoly (Fin (m + n)) ℚ l)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [frobChar_smul, frobChar_schurChar_of_le (le_refl (m + n)),
    ← Nat.cast_smul_eq_nsmul ℚ]

end Equiv.Perm
