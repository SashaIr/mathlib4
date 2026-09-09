/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.SymmetricFunctions.Grading

/-!
# The involution `omega` as an automorphism of the ring of symmetric functions

Following `theories/MPoly/sympoly.v` and `theories/MPoly/homogsym.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we extend the involution `omega` from
the homogeneous parts to the whole ring of symmetric functions, using the decomposition of
`SymFunc R` as the direct sum of its homogeneous parts, and we prove that the result is an
algebra automorphism of order two.

## Main definitions

* `SymFunc.omegaSymFunc R` : the involution `omega` on the ring of symmetric functions.
* `SymFunc.omegaSymFuncAlgEquiv R` : the same, as an algebra automorphism.

## Main results

* `SymFunc.truncSub_omegaSym` : `omega` commutes with truncation of the variables.
* `SymFunc.poly_omegaFunc` : the component in `m ≥ n` variables of `omega f` is the image of
  the component of `f` under `omega` in `m` variables.
* `SymFunc.omegaSymFunc_mul` and `SymFunc.omegaSymFunc_one` : **`omega` is a ring
  automorphism** of the symmetric functions, and `SymFunc.omegaSymFunc_omegaSymFunc` : it is
  an involution.
* `SymFunc.omegaSymFunc_schurFunc`, `SymFunc.omegaSymFunc_hsymFunc`,
  `SymFunc.omegaSymFunc_psymFunc` : its values on the classical symmetric functions.
-/

@[expose] public section

namespace SymFunc

open MvPolynomial

variable {m M n : ℕ} {R : Type*} [CommRing R]

/-! ### `omega` and truncation -/

/-- **The involution `omega` commutes with truncation** of the variables. -/
theorem truncSub_omegaSym (hn : n ≤ m) (h : m ≤ M) (f : symHomogeneousSubmodule M n R) :
    truncSub h n R (omegaSym M n R (hn.trans h) f)
      = omegaSym m n R hn (truncSub h n R f) := by
  refine LinearMap.congr_fun (f := (truncSub h n R).comp
    (omegaSym M n R (hn.trans h)).toLinearMap)
    (g := (omegaSym m n R hn).toLinearMap.comp (truncSub h n R)) ?_ f
  refine (schurBasis M n R).ext fun nu => ?_
  simp only [LinearMap.comp_apply, schurBasis_apply, LinearEquiv.coe_coe]
  set mu := (partIdxEquiv hn (hn.trans h)).symm nu with hmudef
  have hnu : nu = partIdxEquiv hn (hn.trans h) mu :=
    ((partIdxEquiv hn (hn.trans h)).apply_symm_apply nu).symm
  have hconj : conjIdx (hn.trans h) (partIdxEquiv hn (hn.trans h) mu)
      = partIdxEquiv hn (hn.trans h) (conjIdx hn mu) := Subtype.ext rfl
  rw [hnu, omegaSym_schurSub, hconj, truncSub_schurSub, truncSub_schurSub, omegaSym_schurSub]

/-- The component in `m ≥ n` variables of `omega f` is the image under `omega` of the
component of `f` in `m` variables. -/
theorem poly_omegaFunc (hn : n ≤ m) (f : symFuncHomogeneous n R) :
    (omegaFunc n R f).1.poly m
      = (omegaSym m n R hn (symFuncHomogeneousEquiv hn R f) : MvPolynomial (Fin m) R) := by
  have h2 : symFuncHomogeneousEquiv (le_refl n) R (omegaFunc n R f)
      = omegaSym n n R (le_refl n) (symFuncHomogeneousEquiv (le_refl n) R f) := by
    simp only [omegaFunc, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  refine SymFunc.poly_eq_of_truncVars_eq (omegaFunc n R f).2 (le_refl n) hn
    (omegaSym m n R hn (symFuncHomogeneousEquiv hn R f)).2 ?_
  rw [← coe_truncSub, truncSub_omegaSym (le_refl n) hn, truncSub_symFuncHomogeneousEquiv,
    ← symFuncHomogeneousEquiv_apply (le_refl n) (omegaFunc n R f), h2]
  exact hn

/-- **`omega` is multiplicative** on homogeneous symmetric functions. -/
theorem omegaFunc_mul {a b : ℕ} (hab : a + b = n) (f : symFuncHomogeneous a R)
    (g : symFuncHomogeneous b R) (hfg : (f.1 * g.1).IsHomogeneous n) :
    (omegaFunc n R ⟨f.1 * g.1, hfg⟩).1 = (omegaFunc a R f).1 * (omegaFunc b R g).1 := by
  have ha : a ≤ n := by omega
  have hb : b ≤ n := by omega
  have hRHS : ((omegaFunc a R f).1 * (omegaFunc b R g).1).IsHomogeneous n := by
    rw [← hab]
    exact (omegaFunc a R f).2.mul (omegaFunc b R g).2
  refine SymFunc.ext_of_poly_eq (le_refl n) (omegaFunc n R ⟨f.1 * g.1, hfg⟩).2 hRHS ?_
  have hmul : symFuncHomogeneousEquiv (le_refl n) R ⟨f.1 * g.1, hfg⟩
      = mulSub n R hab (symFuncHomogeneousEquiv ha R f) (symFuncHomogeneousEquiv hb R g) := by
    refine Subtype.ext ?_
    rw [coe_mulSub, symFuncHomogeneousEquiv_apply, symFuncHomogeneousEquiv_apply,
      symFuncHomogeneousEquiv_apply, SymFunc.poly_mul]
  rw [poly_omegaFunc (le_refl n), hmul, SymFunc.poly_mul, poly_omegaFunc ha, poly_omegaFunc hb,
    omegaSym_mul hab (le_refl n)]

/-- On symmetric functions of degree `0`, `omega` is the identity. -/
theorem omegaFunc_zero_eq (f : symFuncHomogeneous 0 R) : omegaFunc 0 R f = f := by
  have hid : omegaSym 0 0 R (le_refl 0) = LinearEquiv.refl R (symHomogeneousSubmodule 0 0 R) := by
    refine LinearEquiv.toLinearMap_injective ((schurBasis 0 0 R).ext fun nu => ?_)
    have hnil : nu.1 = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 nu.2.2.2)
    have hconj : conjIdx (le_refl 0) nu = nu := Subtype.ext (by rw [conjIdx_val, hnil]; rfl)
    simp only [LinearEquiv.coe_coe, schurBasis_apply, omegaSym_schurSub, hconj,
      LinearEquiv.refl_apply]
  refine (symFuncHomogeneousEquiv (le_refl 0) R).injective ?_
  simp only [omegaFunc, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hid,
    LinearEquiv.refl_apply]

/-! ### `omega` on the whole ring -/

/-- The decomposition of the ring of symmetric functions into its homogeneous parts. -/
noncomputable instance symFuncDecomposition (R : Type*) [CommRing R] :
    DirectSum.Decomposition fun n => symFuncHomogeneous n R :=
  (symFuncHomogeneous_isInternal R).chooseDecomposition

/-- **The involution `omega`** on the whole ring of symmetric functions: the linear map
acting on the homogeneous part of degree `n` as the involution `omegaFunc n`. -/
noncomputable def omegaSymFunc (R : Type*) [CommRing R] : SymFunc R →ₗ[R] SymFunc R :=
  (DirectSum.toModule R ℕ (SymFunc R)
      fun d => (symFuncHomogeneous d R).subtype ∘ₗ (omegaFunc d R).toLinearMap).comp
    (DirectSum.decomposeLinearEquiv fun n => symFuncHomogeneous n R).toLinearMap

theorem omegaSymFunc_of_mem {f : SymFunc R} (hf : f ∈ symFuncHomogeneous n R) :
    omegaSymFunc R f = (omegaFunc n R ⟨f, hf⟩).1 := by
  rw [omegaSymFunc, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem _ hf,
    ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]
  rfl

/-- **`omega` is multiplicative** on the ring of symmetric functions. -/
theorem omegaSymFunc_mul (f g : SymFunc R) :
    omegaSymFunc R (f * g) = omegaSymFunc R f * omegaSymFunc R g := by
  refine DirectSum.Decomposition.inductionOn (fun n => symFuncHomogeneous n R)
    (motive := fun f => ∀ g, omegaSymFunc R (f * g) = omegaSymFunc R f * omegaSymFunc R g)
    (fun g => by rw [zero_mul, map_zero, zero_mul])
    (fun {a} fa => ?_)
    (fun f1 f2 h1 h2 g => by rw [add_mul, map_add, map_add, h1, h2, add_mul]) f g
  refine DirectSum.Decomposition.inductionOn (fun n => symFuncHomogeneous n R)
    (motive := fun g => omegaSymFunc R (fa.1 * g) = omegaSymFunc R fa.1 * omegaSymFunc R g)
    (by rw [mul_zero, map_zero, mul_zero])
    (fun {b} gb => ?_)
    (fun g1 g2 h1 h2 => by rw [mul_add, map_add, map_add, h1, h2, mul_add])
  rw [omegaSymFunc_of_mem (SymFunc.IsHomogeneous.mul fa.2 gb.2), omegaSymFunc_of_mem fa.2,
    omegaSymFunc_of_mem gb.2, omegaFunc_mul rfl fa gb]

/-- `omega` fixes the unit. -/
@[simp] theorem omegaSymFunc_one (R : Type*) [CommRing R] :
    omegaSymFunc R (1 : SymFunc R) = 1 := by
  rw [omegaSymFunc_of_mem (SymFunc.isHomogeneous_one : (1 : SymFunc R).IsHomogeneous 0),
    omegaFunc_zero_eq]

/-- **`omega` is an involution** of the ring of symmetric functions. -/
theorem omegaSymFunc_omegaSymFunc (f : SymFunc R) :
    omegaSymFunc R (omegaSymFunc R f) = f := by
  refine DirectSum.Decomposition.inductionOn (fun n => symFuncHomogeneous n R)
    (motive := fun f => omegaSymFunc R (omegaSymFunc R f) = f)
    (by rw [map_zero, map_zero])
    (fun {a} fa => ?_)
    (fun f1 f2 h1 h2 => by rw [map_add, map_add, h1, h2]) f
  rw [omegaSymFunc_of_mem fa.2, omegaSymFunc_of_mem (omegaFunc a R fa).2]
  exact congrArg Subtype.val (omegaFunc_omegaFunc fa)

/-- **The involution `omega` as an algebra endomorphism** of the ring of symmetric
functions. -/
noncomputable def omegaSymFuncAlgHom (R : Type*) [CommRing R] : SymFunc R →ₐ[R] SymFunc R where
  toFun := omegaSymFunc R
  map_one' := omegaSymFunc_one R
  map_mul' := omegaSymFunc_mul
  map_zero' := map_zero _
  map_add' f g := map_add _ f g
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    change omegaSymFunc R (r • (1 : SymFunc R)) = r • (1 : SymFunc R)
    rw [map_smul, omegaSymFunc_one]

@[simp] lemma omegaSymFuncAlgHom_apply (f : SymFunc R) :
    omegaSymFuncAlgHom R f = omegaSymFunc R f := rfl

/-- **The involution `omega` as an algebra automorphism** of the ring of symmetric
functions. -/
noncomputable def omegaSymFuncAlgEquiv (R : Type*) [CommRing R] : SymFunc R ≃ₐ[R] SymFunc R :=
  AlgEquiv.ofAlgHom (omegaSymFuncAlgHom R) (omegaSymFuncAlgHom R)
    (AlgHom.ext fun f => omegaSymFunc_omegaSymFunc f)
    (AlgHom.ext fun f => omegaSymFunc_omegaSymFunc f)

@[simp] lemma omegaSymFuncAlgEquiv_apply (f : SymFunc R) :
    omegaSymFuncAlgEquiv R f = omegaSymFunc R f := rfl

/-! ### `omega` on the classical symmetric functions -/

/-- `omega` exchanges the Schur functions of two conjugate shapes. -/
@[simp] theorem omegaSymFunc_schurFunc (lam : PartIdx n n) :
    omegaSymFunc R (schurFunc n R lam).1 = (schurFunc n R (conjIdx (le_refl n) lam)).1 := by
  rw [omegaSymFunc_of_mem (schurFunc n R lam).2]
  exact congrArg Subtype.val (omegaFunc_schurFunc lam)

/-- `omega` exchanges the complete homogeneous and the elementary symmetric functions. -/
@[simp] theorem omegaSymFunc_hsymFunc (lam : PartIdx n n) :
    omegaSymFunc R (hsymFunc n R lam).1 = (esymFunc n R (conjIdx (le_refl n) lam)).1 := by
  rw [omegaSymFunc_of_mem (hsymFunc n R lam).2]
  exact congrArg Subtype.val (omegaFunc_hsymFunc lam)

/-- `omega` acts on the power sum symmetric functions by the sign `(-1)^(n - length lam)`. -/
@[simp] theorem omegaSymFunc_psymFunc (lam : PartIdx n n) :
    omegaSymFunc R (psymFunc n R lam).1
      = ((-1) ^ (n - lam.1.length) : R) • (psymFunc n R lam).1 := by
  rw [omegaSymFunc_of_mem (psymFunc n R lam).2]
  exact congrArg Subtype.val (omegaFunc_psymFunc lam)

end SymFunc
