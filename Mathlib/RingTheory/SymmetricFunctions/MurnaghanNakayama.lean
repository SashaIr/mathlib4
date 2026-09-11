/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Ribbon
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.MurnaghanNakayamaRibbon
public import Mathlib.RingTheory.SymmetricFunctions.Basic

/-!
# The Murnaghan–Nakayama rule for symmetric functions

`MvPolynomial.psum_mul_schurPoly_sum_ribbon` of
`Mathlib/RingTheory/MvPolynomial/Symmetric/Schur/MurnaghanNakayamaRibbon.lean` multiplies a
Schur polynomial by a power sum, in finitely many variables and with the shapes given as
weakly decreasing lists.  This file restates it for symmetric functions and for partitions of
an integer: the product `p_r · s_μ` is a signed sum of the Schur functions `s_ν` over the
partitions `ν` of `|μ| + r` such that the skew shape `ν / μ` is a ribbon, with the sign
`(-1)` to the number of rows of the ribbon minus one.

## Main results

* `SymFunc.poly_psymFunc_indiscrete` : the components of `p_r`, seen as the power sum
  symmetric function of the partition with the single part `r`, are the power sums.
* `SymFunc.psymFunc_mul_schurFunc` : **the Murnaghan–Nakayama rule for symmetric
  functions**.

## References

* [I. G. Macdonald, *Symmetric functions and Hall polynomials*][macdonald1995]
* [F. Hivert et al., *Coq-Combi*][hivert-coqcombi]
-/

@[expose] public section

open List MvPolynomial Young

namespace SymFunc

variable {R : Type*} [CommRing R]

/-- The `m`-variable component of the power sum symmetric function of the partition with the
single part `r` is the power sum `p_r`. -/
theorem poly_psymFunc_indiscrete {r m : ℕ} (hr : 0 < r) (hrm : r ≤ m) :
    (psymFunc r R (Nat.Partition.indiscrete r)).1.poly m = psum (Fin m) R r := by
  rw [poly_psymFunc hrm, Nat.Partition.partsList_indiscrete hr.ne']
  simp [pProd]

open scoped Classical in
/-- **The Murnaghan–Nakayama rule for symmetric functions**: the product of the power sum
`p_r` by the Schur function `s_μ` is the sum, over the partitions `ν` of `|μ| + r` such that
the skew shape `ν / μ` is a ribbon, of `(-1)` to the number of rows of the ribbon minus one,
times `s_ν`. -/
theorem psymFunc_mul_schurFunc {a r : ℕ} (hr : 0 < r) (μ : Nat.Partition a) :
    (psymFunc r R (Nat.Partition.indiscrete r)).1 * (schurFunc a R μ).1
      = ∑ ν : Nat.Partition (a + r),
          if μ.IsRibbonOf ν then
            ((-1 : ℤ) ^ (μ.ribbonHeight ν - 1)) • (schurFunc (a + r) R ν).1
          else 0 := by
  classical
  have ha : a ≤ a + r := Nat.le_add_right _ _
  have hrn : r ≤ a + r := Nat.le_add_left _ _
  have hlen : μ.partsList.length ≤ a + r := (Nat.Partition.length_partsList_le μ).trans ha
  have hL : ((psymFunc r R (Nat.Partition.indiscrete r)).1 * (schurFunc a R μ).1).IsHomogeneous
      (a + r) := by
    have h := (psymFunc r R (Nat.Partition.indiscrete r)).2.mul (schurFunc a R μ).2
    rwa [Nat.add_comm r a] at h
  have hR : (∑ ν : Nat.Partition (a + r),
      if μ.IsRibbonOf ν then
        ((-1 : ℤ) ^ (μ.ribbonHeight ν - 1)) • (schurFunc (a + r) R ν).1
      else 0).IsHomogeneous (a + r) := by
    rw [← mem_symFuncHomogeneous]
    refine Submodule.sum_mem _ fun ν _ => ?_
    by_cases hcond : μ.IsRibbonOf ν
    · rw [ite_eq_left hcond]
      exact zsmul_mem (schurFunc (a + r) R ν).2 _
    · rw [ite_eq_right hcond]
      exact zero_mem _
  refine ext_of_poly_eq (le_refl (a + r)) hL hR ?_
  have hsum : (∑ ν : Nat.Partition (a + r),
        if μ.IsRibbonOf ν then
          ((-1 : ℤ) ^ (μ.ribbonHeight ν - 1)) • (schurFunc (a + r) R ν).1
        else 0).poly (a + r)
      = ∑ ν : Nat.Partition (a + r),
          if μ.IsRibbonOf ν then
            ((-1 : ℤ) ^ (μ.ribbonHeight ν - 1)) • schurPoly (Fin (a + r)) R ν.partsList
          else 0 := by
    rw [← polyAlgHom_apply, map_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    by_cases hcond : μ.IsRibbonOf ν
    · rw [ite_eq_left hcond, ite_eq_left hcond, map_zsmul, polyAlgHom_apply,
        poly_schurFunc (le_refl (a + r))]
    · rw [ite_eq_right hcond, ite_eq_right hcond, map_zero]
  rw [poly_mul, hsum, poly_psymFunc_indiscrete hr hrn, poly_schurFunc ha]
  have key := psum_mul_schurPoly_sum_ribbon (R := R) (m := a + r) (r := r)
    (Nat.Partition.isPart_partsList μ) hlen hr
  rw [Nat.Partition.sum_partsList μ] at key
  rw [key, ← sum_natPartition_eq_sum_partIdx (le_refl (a + r))
    (fun l => if ∃ s k, RibbonOn s k μ.partsList l then
      ((-1 : ℤ) ^ (Young.ribbonHeight μ.partsList l - 1)) • schurPoly (Fin (a + r)) R l else 0)]
  exact Finset.sum_congr rfl fun ν _ => (if_congr Iff.rfl rfl rfl).symm

end SymFunc
