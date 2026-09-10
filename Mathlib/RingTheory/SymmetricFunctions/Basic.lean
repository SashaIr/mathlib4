/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.Truncate
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.LRSymmetry

/-!
# The ring of symmetric functions

Following `theories/MPoly/homogsym.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we build the ring of symmetric
functions `SymFunc R` in countably many variables: a symmetric function is a family
`f m : MvPolynomial (Fin m) R` of symmetric polynomials, one for each number `m` of
variables, of bounded total degree and compatible with setting the last variable to zero.

## Main definitions

* `SymFunc.symFuncSubalgebra R` : the ring of symmetric functions, as a subalgebra of the
  product of the polynomial algebras.
* `SymFunc R` : the same, as a type.
* `SymFunc.poly f m` : the underlying polynomial in `m` variables.
* `SymFunc.IsHomogeneous f n` and `SymFunc.symFuncHomogeneous n R` : the homogeneous
  symmetric functions of degree `n`.
* `SymFunc.homogeneousComponent d f` : the homogeneous component of degree `d`.
* `SymFunc.msymFunc n R η`, `SymFunc.schurFunc n R η`, `SymFunc.hsymFunc n R η`,
  `SymFunc.esymFunc n R η`, `SymFunc.psymFunc n R η` : the monomial, Schur, complete
  homogeneous, elementary and power sum symmetric functions of a partition of `n`.
* `SymFunc.hallInnerFunc n R` : the Hall scalar product on the homogeneous symmetric
  functions of degree `n`.
* `SymFunc.omegaFunc n R` : the involution `omega` on the homogeneous symmetric functions of
  degree `n`.

## Main results

* `SymFunc.truncVars_poly_of_le` : the components of a symmetric function are
  obtained from one another by truncation.
* `SymFunc.ext_of_poly_eq` : a homogeneous symmetric function of degree `n` is
  determined by its component in `m ≥ n` variables.
* `SymFunc.exists_symFunc_poly_eq` : every symmetric homogeneous polynomial of degree `n` in
  `m ≥ n` variables comes from a homogeneous symmetric function.
* `SymFunc.symFuncHomogeneousEquiv` : **the homogeneous symmetric functions of degree `n`
  are the symmetric homogeneous polynomials of degree `n` in `m ≥ n` variables**.
* `SymFunc.sum_homogeneousComponent` : a symmetric function is the sum of its
  homogeneous components, and `SymFunc.IsHomogeneous.mul` : the product of two
  homogeneous symmetric functions is homogeneous, so that `SymFunc R` is a graded ring.
* `SymFunc.poly_msymFunc`, `SymFunc.poly_schurFunc` : the components of `m_η` and `s_η`
  are the monomial symmetric polynomials and the Schur polynomials.
* `SymFunc.msymFuncBasis`, `SymFunc.schurFuncBasis`, `SymFunc.hsymFuncBasis`,
  `SymFunc.esymFuncBasis`, `SymFunc.psymFuncBasis` : **the monomial, Schur, complete
  homogeneous, elementary and power sum symmetric functions of the partitions of `n` are
  bases of the homogeneous symmetric functions of degree `n`** (the last one over a ring
  containing the rationals).
* `SymFunc.hallInnerFunc_schurFunc` : **the Schur functions are orthonormal** for the Hall
  scalar product, and `SymFunc.hallInnerFunc_hsymFunc_msymFunc` : the bases `h` and `m` are
  dual.
* `SymFunc.omegaFunc_schurFunc`, `SymFunc.omegaFunc_omegaFunc`, `SymFunc.hallInnerFunc_omegaFunc`,
  `SymFunc.omegaFunc_hsymFunc`, `SymFunc.omegaFunc_psymFunc` : `omega` exchanges the Schur
  functions of two conjugate shapes, is an involution and an isometry, exchanges `h` and
  `e`, and acts on `p_η` by the sign `(-1)^(n - length η)`.
* `SymFunc.schurFunc_mul_schurFunc` : **the Littlewood–Richardson rule** for symmetric
  functions, `s_η · s_μ = ∑_nu c^ν_{η μ} · s_ν`.

## References

* [I. G. Macdonald, *Symmetric functions and Hall polynomials*][macdonald1995]
* [F. Hivert et al., *Coq-Combi*][hivert-coqcombi]
-/

@[expose] public section

open Young

open List

namespace SymFunc

open MvPolynomial

variable {m M n : ℕ}

/-! ### The ring of symmetric functions -/

/-- The ring of symmetric functions: the families of symmetric polynomials of bounded
degree, one in `m` variables for each `m`, compatible with the truncation maps. -/
def symFuncSubalgebra (R : Type*) [CommRing R] :
    Subalgebra R (∀ m : ℕ, MvPolynomial (Fin m) R) where
  carrier := {f | (∀ m, f m ∈ symmetricSubalgebra (Fin m) R) ∧
    (∀ m, truncVars m (m + 1) R (f (m + 1)) = f m) ∧ ∃ N, ∀ m, (f m).totalDegree ≤ N}
  mul_mem' := by
    rintro f g ⟨hfs, hft, N, hfN⟩ ⟨hgs, hgt, K, hgK⟩
    refine ⟨fun m => mul_mem (hfs m) (hgs m), fun m => ?_, N + K, fun m => ?_⟩
    · rw [Pi.mul_apply, Pi.mul_apply, map_mul, hft, hgt]
    · exact (totalDegree_mul _ _).trans (Nat.add_le_add (hfN m) (hgK m))
  add_mem' := by
    rintro f g ⟨hfs, hft, N, hfN⟩ ⟨hgs, hgt, K, hgK⟩
    refine ⟨fun m => add_mem (hfs m) (hgs m), fun m => ?_, max N K, fun m => ?_⟩
    · rw [Pi.add_apply, Pi.add_apply, map_add, hft, hgt]
    · exact (totalDegree_add _ _).trans
        (max_le_max (hfN m) (hgK m))
  algebraMap_mem' := by
    intro r
    refine ⟨fun m => Subalgebra.algebraMap_mem _ _, fun m => ?_, 0, fun m => ?_⟩
    · rw [Pi.algebraMap_apply, Pi.algebraMap_apply, AlgHom.commutes]
    · rw [Pi.algebraMap_apply, algebraMap_eq, totalDegree_C]

/-- The ring of symmetric functions over `R`. -/
abbrev _root_.SymFunc (R : Type*) [CommRing R] : Type _ := ↥(symFuncSubalgebra R)


variable {R : Type*} [CommRing R]

/-- The polynomial in `m` variables underlying a symmetric function. -/
def poly (f : SymFunc R) (m : ℕ) : MvPolynomial (Fin m) R := (f : ∀ m, MvPolynomial (Fin m) R) m

lemma isSymmetric_poly (f : SymFunc R) (m : ℕ) : (f.poly m).IsSymmetric := f.2.1 m

@[simp] lemma truncVars_poly (f : SymFunc R) (m : ℕ) :
    truncVars m (m + 1) R (f.poly (m + 1)) = f.poly m := f.2.2.1 m

lemma exists_totalDegree_poly_le (f : SymFunc R) : ∃ N, ∀ m, (f.poly m).totalDegree ≤ N := f.2.2.2

/-- The components of a symmetric function are obtained from one another by truncation. -/
lemma truncVars_poly_of_le (f : SymFunc R) (h : m ≤ M) :
    truncVars m M R (f.poly M) = f.poly m := by
  induction M, h using Nat.le_induction with
  | base => exact truncVars_self _
  | succ M hM ih => rw [← truncVars_truncVars hM (Nat.le_succ M), truncVars_poly, ih]

@[ext] lemma ext {f g : SymFunc R} (h : ∀ m, f.poly m = g.poly m) : f = g :=
  Subtype.ext (funext h)

@[simp] lemma poly_add (f g : SymFunc R) (m : ℕ) : (f + g).poly m = f.poly m + g.poly m := rfl

@[simp] lemma poly_mul (f g : SymFunc R) (m : ℕ) : (f * g).poly m = f.poly m * g.poly m := rfl

@[simp] lemma poly_zero (m : ℕ) : (0 : SymFunc R).poly m = 0 := rfl

@[simp] lemma poly_one (m : ℕ) : (1 : SymFunc R).poly m = 1 := rfl

@[simp] lemma poly_smul (r : R) (f : SymFunc R) (m : ℕ) : (r • f).poly m = r • f.poly m := rfl

/-- Evaluating a symmetric function in `m` variables, as an algebra map. -/
def polyAlgHom (R : Type*) [CommRing R] (m : ℕ) : SymFunc R →ₐ[R] MvPolynomial (Fin m) R where
  toFun f := f.poly m
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] lemma polyAlgHom_apply (f : SymFunc R) (m : ℕ) : polyAlgHom R m f = f.poly m := rfl

/-! ### Homogeneous symmetric functions -/

/-- A symmetric function is homogeneous of degree `n` when all its components are. -/
def IsHomogeneous (f : SymFunc R) (n : ℕ) : Prop := ∀ m, (f.poly m).IsHomogeneous n

/-- The product of two homogeneous symmetric functions is homogeneous. -/
lemma IsHomogeneous.mul {f g : SymFunc R} {a b : ℕ} (hf : f.IsHomogeneous a)
    (hg : g.IsHomogeneous b) : (f * g).IsHomogeneous (a + b) := fun k => (hf k).mul (hg k)

/-- The unit is homogeneous of degree `0`. -/
lemma isHomogeneous_one : (1 : SymFunc R).IsHomogeneous 0 :=
  fun _ => MvPolynomial.isHomogeneous_one _ _


/-- The submodule of the homogeneous symmetric functions of degree `n`. -/
def symFuncHomogeneous (n : ℕ) (R : Type*) [CommRing R] : Submodule R (SymFunc R) where
  carrier := {f | f.IsHomogeneous n}
  add_mem' hf hg m := (hf m).add (hg m)
  zero_mem' m := isHomogeneous_zero _ _ _
  smul_mem' r f hf m := by
    rw [SymFunc.poly_smul, smul_eq_C_mul]
    exact (hf m).C_mul r

variable {R : Type*} [CommRing R]

lemma mem_symFuncHomogeneous {f : SymFunc R} :
    f ∈ symFuncHomogeneous n R ↔ f.IsHomogeneous n := Iff.rfl

/-- The component in `m` variables of a homogeneous symmetric function of degree `n` is a
symmetric homogeneous polynomial of degree `n`. -/
lemma poly_mem_symHomogeneousSubmodule {f : SymFunc R} (hf : f.IsHomogeneous n) (m : ℕ) :
    f.poly m ∈ symHomogeneousSubmodule m n R := ⟨hf m, f.isSymmetric_poly m⟩

/-- A homogeneous symmetric function of degree `n` is determined by its component in
`m ≥ n` variables. -/
theorem ext_of_poly_eq (hn : n ≤ m) {f g : SymFunc R} (hf : f.IsHomogeneous n)
    (hg : g.IsHomogeneous n) (h : f.poly m = g.poly m) : f = g := by
  refine SymFunc.ext fun k => ?_
  rcases le_total k m with hk | hk
  · rw [← f.truncVars_poly_of_le hk, ← g.truncVars_poly_of_le hk, h]
  · have hinj : Function.Injective (truncSub hk n R : symHomogeneousSubmodule k n R →ₗ[R]
        symHomogeneousSubmodule m n R) := fun a b hab => (truncEquiv hn hk R).injective hab
    have := hinj (a₁ := ⟨f.poly k, poly_mem_symHomogeneousSubmodule hf k⟩)
      (a₂ := ⟨g.poly k, poly_mem_symHomogeneousSubmodule hg k⟩) ?_
    · exact congrArg Subtype.val this
    · apply Subtype.ext
      rw [coe_truncSub, coe_truncSub]
      simpa [f.truncVars_poly_of_le hk, g.truncVars_poly_of_le hk] using h

/-! ### Lifting a symmetric homogeneous polynomial to a symmetric function -/

/-- The symmetric homogeneous polynomial of degree `n` in `M ≥ m` variables whose
truncation to `m` variables is `g`. -/
noncomputable def liftSub (hn : n ≤ m) (hM : m ≤ M) (g : symHomogeneousSubmodule m n R) :
    symHomogeneousSubmodule M n R := (truncEquiv hn hM R).symm g

@[simp] lemma truncSub_liftSub (hn : n ≤ m) (hM : m ≤ M) (g : symHomogeneousSubmodule m n R) :
    truncSub hM n R (liftSub hn hM g) = g := (truncEquiv hn hM R).apply_symm_apply g

/-- The lifts of `g` to more and more variables are compatible with truncation. -/
lemma truncSub_liftSub_liftSub {K : ℕ} (hn : n ≤ m) (hM : m ≤ M) (hK : M ≤ K)
    (g : symHomogeneousSubmodule m n R) :
    truncSub hK n R (liftSub hn (hM.trans hK) g) = liftSub hn hM g := by
  refine (truncEquiv hn hM R).injective ?_
  rw [truncEquiv_apply, truncEquiv_apply, truncSub_truncSub, truncSub_liftSub,
    truncSub_liftSub]

/-- The family of polynomials attached to a symmetric homogeneous polynomial of degree `n`
in `m ≥ n` variables. -/
noncomputable def liftPoly (hn : n ≤ m) (g : symHomogeneousSubmodule m n R) (k : ℕ) :
    MvPolynomial (Fin k) R :=
  truncVars k (m + k) R (liftSub hn (Nat.le_add_right m k) g)

lemma isHomogeneous_liftPoly (hn : n ≤ m) (g : symHomogeneousSubmodule m n R) (k : ℕ) :
    (liftPoly hn g k).IsHomogeneous n :=
  isHomogeneous_truncVars (liftSub hn (Nat.le_add_right m k) g).2.1

lemma isSymmetric_liftPoly (hn : n ≤ m) (g : symHomogeneousSubmodule m n R) (k : ℕ) :
    (liftPoly hn g k).IsSymmetric :=
  isSymmetric_truncVars (Nat.le_add_left k m) (liftSub hn (Nat.le_add_right m k) g).2.2

lemma truncVars_liftPoly (hn : n ≤ m) (g : symHomogeneousSubmodule m n R) (k : ℕ) :
    truncVars k (k + 1) R (liftPoly hn g (k + 1)) = liftPoly hn g k := by
  rw [liftPoly, liftPoly, truncVars_truncVars (Nat.le_succ k) (by omega : k + 1 ≤ m + (k + 1)),
    ← truncVars_truncVars (Nat.le_add_left k m) (by omega : m + k ≤ m + (k + 1))]
  congr 1
  exact congrArg Subtype.val
    (truncSub_liftSub_liftSub hn (Nat.le_add_right m k) (by omega : m + k ≤ m + (k + 1)) g)

/-- Every symmetric homogeneous polynomial of degree `n` in `m ≥ n` variables is the
component of a homogeneous symmetric function. -/
theorem exists_symFunc_poly_eq (hn : n ≤ m) (g : symHomogeneousSubmodule m n R) :
    ∃ f : SymFunc R, f.IsHomogeneous n ∧ f.poly m = g := by
  refine ⟨⟨fun k => liftPoly hn g k, fun k => isSymmetric_liftPoly hn g k,
    fun k => truncVars_liftPoly hn g k, n, fun k => (isHomogeneous_liftPoly hn g k).totalDegree_le⟩,
    fun k => isHomogeneous_liftPoly hn g k, ?_⟩
  change liftPoly hn g m = (g : MvPolynomial (Fin m) R)
  rw [liftPoly]
  exact congrArg Subtype.val (truncSub_liftSub hn (Nat.le_add_right m m) g)

/-! ### The homogeneous components of degree `n` -/

/-- Taking the component in `m` variables of a homogeneous symmetric function of degree
`n`, as a linear map. -/
noncomputable def polyHomogeneous (n m : ℕ) (R : Type*) [CommRing R] :
    symFuncHomogeneous n R →ₗ[R] symHomogeneousSubmodule m n R where
  toFun f := ⟨f.1.poly m, poly_mem_symHomogeneousSubmodule f.2 m⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma coe_polyHomogeneous (f : symFuncHomogeneous n R) (m : ℕ) :
    (polyHomogeneous n m R f : MvPolynomial (Fin m) R) = f.1.poly m := rfl

/-- **A homogeneous symmetric function of degree `n` is the same thing as a symmetric
homogeneous polynomial of degree `n` in `m ≥ n` variables.** -/
noncomputable def symFuncHomogeneousEquiv (hn : n ≤ m) (R : Type*) [CommRing R] :
    symFuncHomogeneous n R ≃ₗ[R] symHomogeneousSubmodule m n R :=
  LinearEquiv.ofBijective (polyHomogeneous n m R) (by
    constructor
    · intro f g h
      exact Subtype.ext (SymFunc.ext_of_poly_eq hn f.2 g.2 (congrArg Subtype.val h))
    · intro g
      obtain ⟨f, hf, hfg⟩ := exists_symFunc_poly_eq hn g
      exact ⟨⟨f, hf⟩, Subtype.ext hfg⟩)

@[simp] lemma symFuncHomogeneousEquiv_apply (hn : n ≤ m) (f : symFuncHomogeneous n R) :
    (symFuncHomogeneousEquiv hn R f : MvPolynomial (Fin m) R) = f.1.poly m := rfl

/-- A homogeneous symmetric function of degree `n` is recognised by one of its components
in at least `n` variables. -/
lemma poly_eq_of_truncVars_eq {k : ℕ} {f : SymFunc R} (hf : f.IsHomogeneous n)
    (hn : n ≤ m) (hmk : m ≤ k) {q : MvPolynomial (Fin k) R}
    (hq : q ∈ symHomogeneousSubmodule k n R) (hqf : truncVars m k R q = f.poly m) :
    f.poly k = q := by
  have hinj : Function.Injective (truncSub hmk n R : symHomogeneousSubmodule k n R →ₗ[R]
      symHomogeneousSubmodule m n R) := fun a b hab => (truncEquiv hn hmk R).injective hab
  refine congrArg Subtype.val (hinj (a₁ := ⟨f.poly k, poly_mem_symHomogeneousSubmodule hf k⟩)
    (a₂ := ⟨q, hq⟩) (Subtype.ext ?_))
  rw [coe_truncSub, coe_truncSub, hqf, f.truncVars_poly_of_le hmk]

/-! ### Homogeneous components -/


/-- The homogeneous component of degree `d` of a symmetric function. -/
noncomputable def homogeneousComponent (d : ℕ) (f : SymFunc R) : SymFunc R :=
  ⟨fun k => MvPolynomial.homogeneousComponent d (f.poly k),
    fun k => isSymmetric_homogeneousComponent (f.isSymmetric_poly k) d,
    fun k => by
      rw [truncVars_homogeneousComponent (Nat.le_succ k)]
      exact congrArg _ (f.truncVars_poly k),
    ⟨d, fun k => (MvPolynomial.homogeneousComponent_isHomogeneous d _).totalDegree_le⟩⟩

@[simp] lemma poly_homogeneousComponent (d : ℕ) (f : SymFunc R) (k : ℕ) :
    (homogeneousComponent d f).poly k = MvPolynomial.homogeneousComponent d (f.poly k) := rfl

lemma isHomogeneous_homogeneousComponent (d : ℕ) (f : SymFunc R) :
    (homogeneousComponent d f).IsHomogeneous d :=
  fun _ => MvPolynomial.homogeneousComponent_isHomogeneous d _

lemma homogeneousComponent_mem (d : ℕ) (f : SymFunc R) :
    homogeneousComponent d f ∈ symFuncHomogeneous d R :=
  isHomogeneous_homogeneousComponent d f

/-- **A symmetric function is the sum of its homogeneous components.** -/
theorem sum_homogeneousComponent {f : SymFunc R} {N : ℕ} (hN : ∀ k, (f.poly k).totalDegree ≤ N) :
    ∑ d ∈ Finset.range (N + 1), homogeneousComponent d f = f := by
  refine SymFunc.ext fun k => ?_
  have hsum : (∑ d ∈ Finset.range (N + 1), homogeneousComponent d f).poly k
      = ∑ d ∈ Finset.range (N + 1), MvPolynomial.homogeneousComponent d (f.poly k) := by
    induction (Finset.range (N + 1)) using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, poly_add, ih, poly_homogeneousComponent]
  have hk := hN k
  rw [hsum]
  calc ∑ d ∈ Finset.range (N + 1), MvPolynomial.homogeneousComponent d (f.poly k)
      = ∑ d ∈ Finset.range ((f.poly k).totalDegree + 1),
          MvPolynomial.homogeneousComponent d (f.poly k) := by
        refine (Finset.sum_subset (fun d hd => ?_) fun d _ hd => ?_).symm
        · rw [Finset.mem_range] at hd ⊢
          omega
        · rw [Finset.mem_range, not_lt] at hd
          exact MvPolynomial.homogeneousComponent_eq_zero d (f.poly k) (by omega)
    _ = f.poly k := MvPolynomial.sum_homogeneousComponent (f.poly k)

/-- Every symmetric function is a finite sum of homogeneous ones. -/
theorem exists_sum_homogeneousComponent (f : SymFunc R) :
    ∃ N, ∑ d ∈ Finset.range (N + 1), homogeneousComponent d f = f := by
  obtain ⟨N, hN⟩ := f.exists_totalDegree_poly_le
  exact ⟨N, sum_homogeneousComponent hN⟩


/-! ### Symmetric functions out of symmetric polynomials -/

/-- The homogeneous symmetric function of degree `n` whose component in `n` variables is a
given symmetric homogeneous polynomial of degree `n` in `n` variables. -/
noncomputable def symFuncOfPoly (n : ℕ) (R : Type*) [CommRing R]
    (g : symHomogeneousSubmodule n n R) : symFuncHomogeneous n R :=
  (symFuncHomogeneousEquiv (le_refl n) R).symm g

@[simp] lemma poly_symFuncOfPoly_self (g : symHomogeneousSubmodule n n R) :
    (symFuncOfPoly n R g).1.poly n = g :=
  congrArg Subtype.val ((symFuncHomogeneousEquiv (le_refl n) R).apply_symm_apply g)

/-- To identify the component in `m ≥ n` variables of `symFuncOfPoly n R g`, it is enough
to truncate it to `n` variables. -/
lemma poly_symFuncOfPoly (hn : n ≤ m) (g : symHomogeneousSubmodule n n R)
    {q : MvPolynomial (Fin m) R} (hq : q ∈ symHomogeneousSubmodule m n R)
    (hqg : truncVars n m R q = g) : (symFuncOfPoly n R g).1.poly m = q :=
  SymFunc.poly_eq_of_truncVars_eq (symFuncOfPoly n R g).2 (le_refl n) hn hq
    (by rw [hqg, poly_symFuncOfPoly_self])

/-! ### The classical symmetric functions and the bases of the homogeneous part -/

/-- The monomial symmetric function `m_η`, as a homogeneous symmetric function of degree
`n = |η|`. -/
noncomputable def msymFunc (n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n n) :
    symFuncHomogeneous n R := symFuncOfPoly n R (mSub n n R η)

/-- The Schur symmetric function `s_η`, as a homogeneous symmetric function of degree
`n = |η|`. -/
noncomputable def schurFunc (n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n n) :
    symFuncHomogeneous n R := symFuncOfPoly n R (schurSub n n R η)

/-- The complete homogeneous symmetric function `h_η`, as a homogeneous symmetric
function of degree `n = |η|`. -/
noncomputable def hsymFunc (n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n n) :
    symFuncHomogeneous n R := symFuncOfPoly n R (hSub n n R η)

/-- The elementary symmetric function `e_{η'}`, as a homogeneous symmetric function of
degree `n = |η|`. -/
noncomputable def esymFunc (n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n n) :
    symFuncHomogeneous n R := symFuncOfPoly n R (eSub n n R η)

/-- The power sum symmetric function `p_η`, as a homogeneous symmetric function of
degree `n = |η|`. -/
noncomputable def psymFunc (n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n n) :
    symFuncHomogeneous n R := symFuncOfPoly n R (pSub n n R η)

/-- The components of the monomial symmetric function are the monomial symmetric
polynomials. -/
@[simp] theorem poly_msymFunc (hn : n ≤ m) (η : PartIdx n n) :
    (msymFunc n R η).1.poly m = monomialSym m R η.1 := by
  refine poly_symFuncOfPoly hn _ (monomialSym_mem_symHomogeneousSubmodule
    ⟨η.1, η.2.1, η.2.2.1, η.2.1.length_le_sum.trans (η.2.2.1.symm ▸ hn)⟩) ?_
  rw [truncVars_monomialSym hn η.2.1 (le_of_eq η.2.2.1), coe_mSub]

/-- The components of the Schur symmetric function are the Schur polynomials. -/
@[simp] theorem poly_schurFunc (hn : n ≤ m) (η : PartIdx n n) :
    (schurFunc n R η).1.poly m = schurPoly (Fin m) R η.1 := by
  refine poly_symFuncOfPoly hn _ (schurPoly_mem_symHomogeneousSubmodule
    ⟨η.1, η.2.1, η.2.2.1, η.2.1.length_le_sum.trans (η.2.2.1.symm ▸ hn)⟩) ?_
  rw [truncVars_schurPoly hn η.2.1 (le_of_eq η.2.2.1), coe_schurSub]

/-- The components of `h_η` are the products of complete homogeneous symmetric
polynomials. -/
@[simp] theorem poly_hsymFunc (hn : n ≤ m) (η : PartIdx n n) :
    (hsymFunc n R η).1.poly m = hProd m R η.1 := by
  refine poly_symFuncOfPoly hn _ (hProd_mem_symHomogeneousSubmodule
    (partIdxEquiv (le_refl n) hn η)) ?_
  have hh := congrArg Subtype.val (truncSub_hSub (R := R) (le_refl n) hn η)
  rw [coe_truncSub, coe_hSub, coe_hSub] at hh
  rw [coe_hSub]
  exact hh

/-- The components of `e_{η'}` are the products of elementary symmetric polynomials. -/
@[simp] theorem poly_esymFunc (hn : n ≤ m) (η : PartIdx n n) :
    (esymFunc n R η).1.poly m = eProd m R (conjPart η.1) := by
  refine poly_symFuncOfPoly hn _ (eProd_conj_mem_symHomogeneousSubmodule
    (partIdxEquiv (le_refl n) hn η)) ?_
  have he := congrArg Subtype.val (truncSub_eSub (R := R) (le_refl n) hn η)
  rw [coe_truncSub, coe_eSub, coe_eSub] at he
  rw [coe_eSub]
  exact he

/-- The components of `p_η` are the products of power sums. -/
@[simp] theorem poly_psymFunc (hn : n ≤ m) (η : PartIdx n n) :
    (psymFunc n R η).1.poly m = pProd m R η.1 := by
  refine poly_symFuncOfPoly hn _ (pProd_mem_symHomogeneousSubmodule
    (partIdxEquiv (le_refl n) hn η)) ?_
  rw [truncVars_pProd hn η.2.1, coe_pSub]

/-- **The monomial symmetric functions of the partitions of `n` form a basis** of the
homogeneous symmetric functions of degree `n`. -/
noncomputable def msymFuncBasis (n : ℕ) (R : Type*) [CommRing R] :
    Module.Basis (PartIdx n n) R (symFuncHomogeneous n R) :=
  (mBasis n n R).map (symFuncHomogeneousEquiv (le_refl n) R).symm

@[simp] lemma msymFuncBasis_apply (η : PartIdx n n) :
    msymFuncBasis n R η = msymFunc n R η := by
  rw [msymFuncBasis, Module.Basis.map_apply, mBasis_apply, msymFunc, symFuncOfPoly]

/-- **The Schur symmetric functions of the partitions of `n` form a basis** of the
homogeneous symmetric functions of degree `n`. -/
noncomputable def schurFuncBasis (n : ℕ) (R : Type*) [CommRing R] :
    Module.Basis (PartIdx n n) R (symFuncHomogeneous n R) :=
  (schurBasis n n R).map (symFuncHomogeneousEquiv (le_refl n) R).symm

@[simp] lemma schurFuncBasis_apply (η : PartIdx n n) :
    schurFuncBasis n R η = schurFunc n R η := by
  rw [schurFuncBasis, Module.Basis.map_apply, schurBasis_apply, schurFunc, symFuncOfPoly]

/-- **The complete homogeneous symmetric functions `h_η` form a basis** of the
homogeneous symmetric functions of degree `n`. -/
noncomputable def hsymFuncBasis (n : ℕ) (R : Type*) [CommRing R] :
    Module.Basis (PartIdx n n) R (symFuncHomogeneous n R) :=
  (hBasis n n R).map (symFuncHomogeneousEquiv (le_refl n) R).symm

@[simp] lemma hsymFuncBasis_apply (η : PartIdx n n) :
    hsymFuncBasis n R η = hsymFunc n R η := by
  rw [hsymFuncBasis, Module.Basis.map_apply, hBasis, Module.Basis.mk_apply, hsymFunc,
    symFuncOfPoly]

/-- **The elementary symmetric functions `e_{η'}` form a basis** of the homogeneous
symmetric functions of degree `n`. -/
noncomputable def esymFuncBasis (n : ℕ) (R : Type*) [CommRing R] :
    Module.Basis (PartIdx n n) R (symFuncHomogeneous n R) :=
  (eBasis n n R).map (symFuncHomogeneousEquiv (le_refl n) R).symm

@[simp] lemma esymFuncBasis_apply (η : PartIdx n n) :
    esymFuncBasis n R η = esymFunc n R η := by
  rw [esymFuncBasis, Module.Basis.map_apply, eBasis, Module.Basis.mk_apply, esymFunc,
    symFuncOfPoly]

/-- **The power sums `p_η` form a basis** of the homogeneous symmetric functions of
degree `n` over a ring containing the rationals. -/
noncomputable def psymFuncBasis (n : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] :
    Module.Basis (PartIdx n n) R (symFuncHomogeneous n R) :=
  (pBasis n n R).map (symFuncHomogeneousEquiv (le_refl n) R).symm

@[simp] lemma psymFuncBasis_apply [Algebra ℚ R] (η : PartIdx n n) :
    psymFuncBasis n R η = psymFunc n R η := by
  rw [psymFuncBasis, Module.Basis.map_apply, pBasis, Module.Basis.mk_apply, psymFunc,
    symFuncOfPoly]

/-! ### The Hall scalar product on symmetric functions -/

/-- **The Hall scalar product** on the homogeneous symmetric functions of degree `n`. -/
noncomputable def hallInnerFunc (n : ℕ) (R : Type*) [CommRing R] :
    symFuncHomogeneous n R →ₗ[R] symFuncHomogeneous n R →ₗ[R] R :=
  ((hallInner n n R).compl₂ (symFuncHomogeneousEquiv (le_refl n) R :
      symFuncHomogeneous n R →ₗ[R] symHomogeneousSubmodule n n R)).comp
    (symFuncHomogeneousEquiv (le_refl n) R :
      symFuncHomogeneous n R →ₗ[R] symHomogeneousSubmodule n n R)

lemma hallInnerFunc_apply (f g : symFuncHomogeneous n R) :
    hallInnerFunc n R f g
      = hallInner n n R (symFuncHomogeneousEquiv (le_refl n) R f)
          (symFuncHomogeneousEquiv (le_refl n) R g) := rfl

/-- Truncating the component in `m ≥ n` variables of a homogeneous symmetric function of
degree `n` gives its component in `n` variables. -/
@[simp] lemma truncSub_symFuncHomogeneousEquiv (hn : n ≤ m) (f : symFuncHomogeneous n R) :
    truncSub hn n R (symFuncHomogeneousEquiv hn R f)
      = symFuncHomogeneousEquiv (le_refl n) R f := by
  refine Subtype.ext ?_
  rw [coe_truncSub, symFuncHomogeneousEquiv_apply, symFuncHomogeneousEquiv_apply,
    f.1.truncVars_poly_of_le hn]

/-- The Hall scalar product of symmetric functions can be computed in any number `m ≥ n`
of variables. -/
theorem hallInnerFunc_eq_hallInner (hn : n ≤ m) (f g : symFuncHomogeneous n R) :
    hallInnerFunc n R f g
      = hallInner m n R (symFuncHomogeneousEquiv hn R f) (symFuncHomogeneousEquiv hn R g) := by
  rw [hallInnerFunc_apply, ← truncSub_symFuncHomogeneousEquiv hn f,
    ← truncSub_symFuncHomogeneousEquiv hn g, hallInner_truncSub (le_refl n) hn]

/-- The Hall scalar product is symmetric. -/
theorem hallInnerFunc_comm (f g : symFuncHomogeneous n R) :
    hallInnerFunc n R f g = hallInnerFunc n R g f := by
  rw [hallInnerFunc_apply, hallInnerFunc_apply, hallInner_comm]

/-- **The Schur functions are orthonormal** for the Hall scalar product. -/
theorem hallInnerFunc_schurFunc (η μ : PartIdx n n) :
    hallInnerFunc n R (schurFunc n R η) (schurFunc n R μ) = if η = μ then 1 else 0 := by
  simp only [hallInnerFunc_apply, schurFunc, symFuncOfPoly, LinearEquiv.apply_symm_apply]
  exact hallInner_schurSub η μ

/-- **The bases `h` and `m` of symmetric functions are dual** for the Hall scalar
product. -/
theorem hallInnerFunc_hsymFunc_msymFunc (η μ : PartIdx n n) :
    hallInnerFunc n R (hsymFunc n R η) (msymFunc n R μ) = if η = μ then 1 else 0 := by
  simp only [hallInnerFunc_apply, hsymFunc, msymFunc, symFuncOfPoly,
    LinearEquiv.apply_symm_apply]
  exact hallInner_hSub_mSub η μ

/-! ### The involution `omega` on symmetric functions -/

/-- **The involution `omega`** on the homogeneous symmetric functions of degree `n`: the
linear automorphism exchanging the Schur functions of two conjugate shapes. -/
noncomputable def omegaFunc (n : ℕ) (R : Type*) [CommRing R] :
    symFuncHomogeneous n R ≃ₗ[R] symFuncHomogeneous n R :=
  (symFuncHomogeneousEquiv (le_refl n) R).trans
    ((omegaSym n n R (le_refl n)).trans (symFuncHomogeneousEquiv (le_refl n) R).symm)

lemma omegaFunc_apply (f : symFuncHomogeneous n R) :
    omegaFunc n R f
      = symFuncOfPoly n R
          (omegaSym n n R (le_refl n) (symFuncHomogeneousEquiv (le_refl n) R f)) := rfl

/-- `omega` exchanges the Schur functions of two conjugate shapes. -/
@[simp] theorem omegaFunc_schurFunc (η : PartIdx n n) :
    omegaFunc n R (schurFunc n R η) = schurFunc n R (conjIdx (le_refl n) η) := by
  simp only [omegaFunc_apply, schurFunc, symFuncOfPoly, LinearEquiv.apply_symm_apply,
    omegaSym_schurSub]

/-- **`omega` is an involution**. -/
theorem omegaFunc_omegaFunc (f : symFuncHomogeneous n R) :
    omegaFunc n R (omegaFunc n R f) = f := by
  simp only [omegaFunc_apply, symFuncOfPoly, LinearEquiv.apply_symm_apply, omegaSym_omegaSym]
  exact (symFuncHomogeneousEquiv (le_refl n) R).symm_apply_apply f

/-- **`omega` is an isometry** for the Hall scalar product. -/
theorem hallInnerFunc_omegaFunc (f g : symFuncHomogeneous n R) :
    hallInnerFunc n R (omegaFunc n R f) (omegaFunc n R g) = hallInnerFunc n R f g := by
  simp only [hallInnerFunc_apply, omegaFunc_apply, symFuncOfPoly, LinearEquiv.apply_symm_apply]
  exact hallInner_omegaSym (le_refl n) _ _

/-- **`omega` exchanges the complete homogeneous and the elementary symmetric
functions**: `omega h_η = e_{η'}`. -/
theorem omegaFunc_hsymFunc (η : PartIdx n n) :
    omegaFunc n R (hsymFunc n R η) = esymFunc n R (conjIdx (le_refl n) η) := by
  have hcoe : eSubOfPart n n R (le_refl n) η = eSub n n R (conjIdx (le_refl n) η) := by
    refine Subtype.ext ?_
    rw [coe_eSubOfPart, coe_eSub, conjIdx_val, conjPart_conjPart η.2.1]
  simp only [omegaFunc_apply, hsymFunc, esymFunc, symFuncOfPoly, LinearEquiv.apply_symm_apply,
    omegaSym_hSub, hcoe]

/-- `omega` exchanges the elementary and the complete homogeneous symmetric functions. -/
theorem omegaFunc_esymFunc (η : PartIdx n n) :
    omegaFunc n R (esymFunc n R η) = hsymFunc n R (conjIdx (le_refl n) η) := by
  have h := omegaFunc_hsymFunc (R := R) (conjIdx (le_refl n) η)
  rw [conjIdx_conjIdx] at h
  rw [← h, omegaFunc_omegaFunc]

/-- **`omega` acts on the power sum symmetric functions by the sign
`(-1)^(n - length η)`**. -/
theorem omegaFunc_psymFunc (η : PartIdx n n) :
    omegaFunc n R (psymFunc n R η) = ((-1) ^ (n - η.1.length) : R) • psymFunc n R η := by
  have key : symFuncHomogeneousEquiv (le_refl n) R (omegaFunc n R (psymFunc n R η))
      = ((-1) ^ (n - η.1.length) : R) • pSub n n R η := by
    simp only [omegaFunc_apply, psymFunc, symFuncOfPoly, LinearEquiv.apply_symm_apply]
    refine Subtype.ext ?_
    rw [SetLike.val_smul, coe_pSub, omegaSym_pSub, MvPolynomial.smul_eq_C_mul, map_pow,
      map_neg, map_one]
  refine (symFuncHomogeneousEquiv (le_refl n) R).injective ?_
  rw [key, LinearEquiv.map_smul]
  congr 1
  simp only [psymFunc, symFuncOfPoly, LinearEquiv.apply_symm_apply]

/-! ### The Littlewood–Richardson rule for symmetric functions -/

/-- **The Littlewood–Richardson rule for symmetric functions**: the product of two Schur
functions is the sum, over the partitions `ν` of `|η| + |μ|`, of `c^ν_{η μ}` copies
of the Schur function of shape `ν`. -/
theorem schurFunc_mul_schurFunc {a b : ℕ} (hab : a + b = n) (η : PartIdx a a)
    (μ : PartIdx b b) :
    (schurFunc a R η).1 * (schurFunc b R μ).1
      = ∑ ν : PartIdx n n, lrCoeff η.1 μ.1 ν.1 • (schurFunc n R ν).1 := by
  have ha : a ≤ n := by omega
  have hb : b ≤ n := by omega
  have hL : ((schurFunc a R η).1 * (schurFunc b R μ).1).IsHomogeneous n := by
    rw [← hab]
    exact (schurFunc a R η).2.mul (schurFunc b R μ).2
  have hR : (∑ ν : PartIdx n n, lrCoeff η.1 μ.1 ν.1 • (schurFunc n R ν).1).IsHomogeneous n :=
    Submodule.sum_mem _ fun ν _ => nsmul_mem (schurFunc n R ν).2 _
  refine SymFunc.ext_of_poly_eq (le_refl n) hL hR ?_
  have hsum : (∑ ν : PartIdx n n, lrCoeff η.1 μ.1 ν.1 • (schurFunc n R ν).1).poly n
      = ∑ ν : PartIdx n n, lrCoeff η.1 μ.1 ν.1 • schurPoly (Fin n) R ν.1 := by
    rw [← SymFunc.polyAlgHom_apply, map_sum]
    exact Finset.sum_congr rfl fun ν _ => by
      rw [map_nsmul, SymFunc.polyAlgHom_apply, poly_schurFunc (le_refl n)]
  rw [SymFunc.poly_mul, hsum, poly_schurFunc ha, poly_schurFunc hb,
    schurPoly_mul_eq_sum_partIdx (by rw [η.2.2.1, μ.2.2.1, hab]) (le_refl n)]

end SymFunc
