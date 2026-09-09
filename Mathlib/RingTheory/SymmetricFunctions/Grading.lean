/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.RingTheory.SymmetricFunctions.Basic

/-!
# The ring of symmetric functions is a graded algebra

Following `theories/MPoly/homogsym.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we show that the ring of symmetric
functions `SymFunc R` is graded by the submodules `symFuncHomogeneous n R` of homogeneous
symmetric functions of degree `n`: the product of two homogeneous symmetric functions of
degrees `a` and `b` is homogeneous of degree `a + b`, and every symmetric function is
uniquely a finite sum of homogeneous ones.

## Main results

* `SymFunc.symFuncHomogeneous_gradedMonoid` : the homogeneous parts form a graded monoid.
* `SymFunc.iSupIndep_symFuncHomogeneous` and `SymFunc.iSup_symFuncHomogeneous_eq_top` : the
  homogeneous parts are independent and span the ring of symmetric functions.
* `SymFunc.symFuncHomogeneous_isInternal` : **the ring of symmetric functions is the internal
  direct sum of its homogeneous parts**.
* `SymFunc.symFuncGradedAlgebra` : **the ring of symmetric functions is a graded algebra**.
-/

namespace SymFunc

open MvPolynomial

variable {n : ℕ} {R : Type*} [CommRing R]

/-! ### The homogeneous component as a projection -/

/-- The homogeneous component of degree `d` of a homogeneous symmetric function of degree
`n` is the function itself if `d = n`, and zero otherwise. -/
lemma homogeneousComponent_of_isHomogeneous {f : SymFunc R} (hf : f.IsHomogeneous n)
    (d : ℕ) : SymFunc.homogeneousComponent d f = if d = n then f else 0 := by
  refine SymFunc.ext fun k => ?_
  rw [poly_homogeneousComponent, MvPolynomial.homogeneousComponent_of_mem (hf k)]
  split_ifs with h
  · rfl
  · rw [SymFunc.poly_zero]

/-- Taking the homogeneous component of degree `d`, as a linear map. -/
noncomputable def homogeneousComponentLM (d : ℕ) (R : Type*) [CommRing R] :
    SymFunc R →ₗ[R] SymFunc R where
  toFun f := SymFunc.homogeneousComponent d f
  map_add' f g := by
    refine SymFunc.ext fun k => ?_
    rw [SymFunc.poly_add, poly_homogeneousComponent, poly_homogeneousComponent,
      poly_homogeneousComponent, SymFunc.poly_add, map_add]
  map_smul' r f := by
    refine SymFunc.ext fun k => ?_
    rw [RingHom.id_apply, SymFunc.poly_smul, poly_homogeneousComponent,
      poly_homogeneousComponent, SymFunc.poly_smul, map_smul]

@[simp] lemma homogeneousComponentLM_apply (d : ℕ) (f : SymFunc R) :
    SymFunc.homogeneousComponentLM d R f = SymFunc.homogeneousComponent d f := rfl

/-! ### The grading -/

/-- The homogeneous parts of the ring of symmetric functions form a graded monoid. -/
lemma symFuncHomogeneous_gradedMonoid (R : Type*) [CommRing R] :
    SetLike.GradedMonoid (fun n => symFuncHomogeneous n R) where
  one_mem := (SymFunc.isHomogeneous_one : (1 : SymFunc R).IsHomogeneous 0)
  mul_mem _ _ _ _ hf hg := SymFunc.IsHomogeneous.mul hf hg

/-- **The homogeneous parts of the ring of symmetric functions are independent.** -/
theorem iSupIndep_symFuncHomogeneous (R : Type*) [CommRing R] :
    iSupIndep fun n => symFuncHomogeneous n R := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hzero : ∀ y ∈ (⨆ (j) (_ : j ≠ i), symFuncHomogeneous j R),
      SymFunc.homogeneousComponentLM i R y = 0 := by
    intro y hy
    refine Submodule.iSup_induction (motive := fun z => SymFunc.homogeneousComponentLM i R z = 0)
      (fun j => ⨆ _ : j ≠ i, symFuncHomogeneous j R) hy (fun j z hz => ?_) (map_zero _)
      (fun a b ha hb => by
        change SymFunc.homogeneousComponentLM i R (a + b) = 0
        rw [map_add, ha, hb, add_zero])
    have hz' : z ∈ ⨆ _ : j ≠ i, symFuncHomogeneous j R := hz
    change SymFunc.homogeneousComponentLM i R z = 0
    by_cases hj : j ≠ i
    · rw [iSup_pos hj] at hz'
      rw [SymFunc.homogeneousComponentLM_apply,
        SymFunc.homogeneousComponent_of_isHomogeneous hz', ite_eq_right fun h => hj h.symm]
    · rw [iSup_neg hj, Submodule.mem_bot] at hz'
      rw [hz', map_zero]
  have hxi : SymFunc.homogeneousComponentLM i R x = x := by
    rw [SymFunc.homogeneousComponentLM_apply, SymFunc.homogeneousComponent_of_isHomogeneous hx,
      ite_eq_left rfl]
  rw [← hxi, hzero x hx']

/-- **The homogeneous parts span the ring of symmetric functions.** -/
theorem iSup_symFuncHomogeneous_eq_top (R : Type*) [CommRing R] :
    ⨆ n, symFuncHomogeneous n R = ⊤ := by
  refine top_le_iff.1 fun f _ => ?_
  obtain ⟨N, hN⟩ := f.exists_sum_homogeneousComponent
  rw [← hN]
  refine Submodule.sum_mem _ fun d _ => ?_
  exact Submodule.mem_iSup_of_mem d (SymFunc.homogeneousComponent_mem d f)

/-- **The ring of symmetric functions is the internal direct sum of its homogeneous
parts.** -/
theorem symFuncHomogeneous_isInternal (R : Type*) [CommRing R] :
    DirectSum.IsInternal fun n => symFuncHomogeneous n R :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_symFuncHomogeneous R, iSup_symFuncHomogeneous_eq_top R⟩

/-- **The ring of symmetric functions is a graded algebra**, graded by the homogeneous
symmetric functions of each degree. -/
@[instance_reducible]
noncomputable def symFuncGradedAlgebra (R : Type*) [CommRing R] :
    GradedAlgebra fun n => symFuncHomogeneous n R :=
  { symFuncHomogeneous_gradedMonoid R,
    (symFuncHomogeneous_isInternal R).chooseDecomposition with }

end SymFunc
