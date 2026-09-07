/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.Elementary
import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.HallInnerProduct

/-!
# Truncating the number of variables

Following `theories/MPoly/homogsym.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we study the effect on symmetric
polynomials of the algebra map `truncVars m M` setting the variables `x_m, …, x_{M-1}` to
zero.  This is the transition map of the inverse system whose limit is the ring of
symmetric functions: the main result is that, in degree `n`, it is an isomorphism as soon
as `n ≤ m ≤ M`.

## Main definitions

* `MvPolynomial.truncVars m M R` : the algebra map `MvPolynomial (Fin M) R →ₐ[R]
  MvPolynomial (Fin m) R` sending `X i` to `X i` for `i < m` and to `0` otherwise.
* `MvPolynomial.truncSub h n R` : the induced map on the modules of symmetric homogeneous
  polynomials of degree `n`.
* `MvPolynomial.truncEquiv` : the induced map is a linear equivalence when `n ≤ m ≤ M`.

## Main results

* `MvPolynomial.coeff_truncVars` : the coefficients of `truncVars m M R p` are coefficients of
  `p`.
* `MvPolynomial.isSymmetric_truncVars`, `MvPolynomial.isHomogeneous_truncVars` : truncation
  preserves symmetry and homogeneity.
* `MvPolynomial.truncSub_mSub`, `MvPolynomial.truncVars_monomialSym` : truncation maps the monomial
  symmetric polynomial of a partition to the monomial symmetric polynomial of the same
  partition.  Similarly for the Schur polynomials (`MvPolynomial.truncSub_schurSub`) and for the
  products `h_lam`, `e_lam` and `p_lam` (`MvPolynomial.truncSub_hSub`, `MvPolynomial.truncSub_eSub`,
  `MvPolynomial.truncVars_pProd`).
* `MvPolynomial.hallInner_truncSub` : the Hall scalar product is invariant under truncation.
-/

namespace MvPolynomial

open List MvPolynomial Finsupp

variable {k m M n : ℕ}

/-! ### The truncation map -/

/-- The algebra map setting the variables of index at least `m` to zero. -/
noncomputable def truncVars (m M : ℕ) (R : Type*) [CommSemiring R] :
    MvPolynomial (Fin M) R →ₐ[R] MvPolynomial (Fin m) R :=
  aeval fun i => if h : (i : ℕ) < m then X ⟨i, h⟩ else 0

section CommSemiring

variable {R : Type*} [CommSemiring R]

@[simp] lemma truncVars_X (i : Fin M) :
    truncVars m M R (X i) = if h : (i : ℕ) < m then X ⟨i, h⟩ else 0 := by
  rw [truncVars, aeval_X]

/-- Truncating a polynomial in `m` variables, seen as a polynomial in `M ≥ m` variables,
gives it back. -/
lemma truncVars_rename (h : m ≤ M) (q : MvPolynomial (Fin m) R) :
    truncVars m M R (rename (Fin.castLE h) q) = q := by
  induction q using MvPolynomial.induction_on with
  | C r => simp [truncVars]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      rw [map_mul, map_mul, hp, rename_X, truncVars_X, dite_eq_left (by simp)]
      congr 2

/-- A monomial involving a variable of index at least `m` is killed by truncation. -/
lemma truncVars_monomial_eq_zero {d : Fin M →₀ ℕ} (r : R) {i : Fin M} (hi : i ∈ d.support)
    (hilt : m ≤ (i : ℕ)) : truncVars m M R (monomial d r) = 0 := by
  rw [truncVars, aeval_monomial, Finsupp.prod]
  have hz : ((if h : (i : ℕ) < m then X (σ := Fin m) (R := R) ⟨i, h⟩ else 0) ^ d i) = 0 := by
    rw [dite_eq_right (by omega)]
    exact zero_pow (Finsupp.mem_support_iff.1 hi)
  rw [Finset.prod_eq_zero hi hz, mul_zero]

/-- The coefficients of the truncation are the coefficients of the original polynomial at
the exponent vectors supported by the first `m` variables. -/
lemma coeff_truncVars (h : m ≤ M) (p : MvPolynomial (Fin M) R) (e : Fin m →₀ ℕ) :
    (truncVars m M R p).coeff e = p.coeff (e.mapDomain (Fin.castLE h)) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d r =>
      rcases eq_or_ne r 0 with rfl | hr
      · simp
      by_cases hd : ∀ i ∈ d.support, (i : ℕ) < m
      · have hvars : ↑(monomial d r : MvPolynomial (Fin M) R).vars ⊆ Set.range (Fin.castLE h) := by
          intro i hi
          rw [vars_monomial hr] at hi
          exact ⟨⟨i, hd i (by simpa using hi)⟩, rfl⟩
        obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range _ (Fin.castLE h)
          (Fin.castLE_injective h) hvars
        rw [← hq, truncVars_rename, coeff_rename_mapDomain _ (Fin.castLE_injective h)]
      · push_neg at hd
        obtain ⟨i, hi, hilt⟩ := hd
        rw [truncVars_monomial_eq_zero r hi hilt]
        simp only [coeff_zero, coeff_monomial]
        rw [ite_eq_right]
        intro hcontra
        have hmem : i ∈ (Finsupp.mapDomain (Fin.castLE h) e).support := hcontra ▸ hi
        have hmem2 := Finsupp.mapDomain_support hmem
        rw [Finset.mem_image] at hmem2
        obtain ⟨j, -, hj⟩ := hmem2
        have : (i : ℕ) < m := by rw [← hj]; exact j.isLt
        omega
  | add p q hp hq => simp [hp, hq]

@[simp] lemma truncVars_self (p : MvPolynomial (Fin m) R) : truncVars m m R p = p := by
  ext e
  rw [coeff_truncVars (le_refl m)]
  congr 1
  rw [show (Fin.castLE (le_refl m) : Fin m → Fin m) = id from funext fun i => Fin.ext rfl,
    Finsupp.mapDomain_id]

/-- Truncating twice is truncating once. -/
lemma truncVars_truncVars (h1 : k ≤ m) (h2 : m ≤ M) (p : MvPolynomial (Fin M) R) :
    truncVars k m R (truncVars m M R p) = truncVars k M R p := by
  ext e
  rw [coeff_truncVars h1, coeff_truncVars h2, coeff_truncVars (h1.trans h2),
    ← Finsupp.mapDomain_comp]
  congr 2

/-! ### Truncation preserves symmetry and homogeneity -/

/-- The extension of a permutation of `Fin m` to a permutation of `Fin M`, fixing the
indices at least `m`. -/
def extPerm (h : m ≤ M) (sigma : Equiv.Perm (Fin m)) : Equiv.Perm (Fin M) where
  toFun i := if hi : (i : ℕ) < m then Fin.castLE h (sigma ⟨i, hi⟩) else i
  invFun i := if hi : (i : ℕ) < m then Fin.castLE h (sigma.symm ⟨i, hi⟩) else i
  left_inv i := by
    by_cases hi : (i : ℕ) < m
    · simp only [dite_eq_left hi]
      rw [dite_eq_left (by simp)]
      simp
    · simp only [dite_eq_right hi]
  right_inv i := by
    by_cases hi : (i : ℕ) < m
    · simp only [dite_eq_left hi]
      rw [dite_eq_left (by simp)]
      simp
    · simp only [dite_eq_right hi]

@[simp] lemma extPerm_castLE (h : m ≤ M) (sigma : Equiv.Perm (Fin m)) (j : Fin m) :
    extPerm h sigma (Fin.castLE h j) = Fin.castLE h (sigma j) := by
  change (if hi : ((Fin.castLE h j : Fin M) : ℕ) < m then Fin.castLE h (sigma ⟨_, hi⟩) else _) = _
  rw [dite_eq_left (by simp)]
  congr 2

/-- The coefficients of a symmetric polynomial are invariant under permuting the
exponents. -/
lemma coeff_mapDomain_perm {p : MvPolynomial (Fin M) R} (hp : p.IsSymmetric)
    (sigma : Equiv.Perm (Fin M)) (d : Fin M →₀ ℕ) :
    coeff (Finsupp.mapDomain (⇑sigma) d) p = coeff d p :=
  calc coeff (Finsupp.mapDomain (⇑sigma) d) p
      = coeff (Finsupp.mapDomain (⇑sigma) d) (rename (⇑sigma) p) := by rw [hp sigma]
    _ = coeff d p := coeff_rename_mapDomain _ sigma.injective _ _

/-- The truncation of a symmetric polynomial is symmetric. -/
lemma isSymmetric_truncVars (h : m ≤ M) {p : MvPolynomial (Fin M) R} (hp : p.IsSymmetric) :
    (truncVars m M R p).IsSymmetric := by
  intro sigma
  ext e
  calc coeff e (rename (⇑sigma) (truncVars m M R p))
      = coeff (Finsupp.mapDomain (⇑sigma) (Finsupp.mapDomain (⇑sigma.symm) e))
        (rename (⇑sigma) (truncVars m M R p)) := by
        rw [← Finsupp.mapDomain_comp]
        simp
    _ = coeff (Finsupp.mapDomain (⇑sigma.symm) e) (truncVars m M R p) :=
        coeff_rename_mapDomain _ sigma.injective _ _
    _ = coeff (Finsupp.mapDomain (Fin.castLE h) (Finsupp.mapDomain (⇑sigma.symm) e)) p :=
        coeff_truncVars h _ _
    _ = coeff (Finsupp.mapDomain (⇑(extPerm h sigma.symm))
          (Finsupp.mapDomain (Fin.castLE h) e)) p := by
        have hfun : (Fin.castLE h ∘ (⇑sigma.symm : Fin m → Fin m))
            = ((⇑(extPerm h sigma.symm) : Fin M → Fin M) ∘ Fin.castLE h) :=
          funext fun j => (extPerm_castLE h sigma.symm j).symm
        rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, hfun]
    _ = coeff (Finsupp.mapDomain (Fin.castLE h) e) p :=
        coeff_mapDomain_perm hp (extPerm h sigma.symm) _
    _ = coeff e (truncVars m M R p) := (coeff_truncVars h _ _).symm

/-- The truncation of a homogeneous polynomial is homogeneous of the same degree. -/
lemma isHomogeneous_truncVars {p : MvPolynomial (Fin M) R} (hp : p.IsHomogeneous n) :
    (truncVars m M R p).IsHomogeneous n := by
  have hg : ∀ i : Fin M,
      MvPolynomial.IsHomogeneous
        (if h : (i : ℕ) < m then X (σ := Fin m) (R := R) ⟨i, h⟩ else 0) 1 := by
    intro i
    by_cases hi : (i : ℕ) < m
    · rw [dite_eq_left hi]
      exact isHomogeneous_X _ _
    · rw [dite_eq_right hi]
      exact isHomogeneous_zero (Fin m) R 1
  have := hp.aeval (fun i => if h : (i : ℕ) < m then X (σ := Fin m) (R := R) ⟨i, h⟩ else 0) hg
  rwa [one_mul] at this

/-- A polynomial whose coefficients are invariant under permuting the exponents is
symmetric. -/
lemma isSymmetric_of_coeff_mapDomain_perm {p : MvPolynomial (Fin M) R}
    (h : ∀ (sigma : Equiv.Perm (Fin M)) (d : Fin M →₀ ℕ),
      coeff (Finsupp.mapDomain (⇑sigma) d) p = coeff d p) :
    p.IsSymmetric := by
  intro sigma
  ext e
  calc coeff e (rename (⇑sigma) p)
      = coeff (Finsupp.mapDomain (⇑sigma) (Finsupp.mapDomain (⇑sigma.symm) e))
        (rename (⇑sigma) p) := by
        rw [← Finsupp.mapDomain_comp]
        simp
    _ = coeff (Finsupp.mapDomain (⇑sigma.symm) e) p :=
        coeff_rename_mapDomain _ sigma.injective _ _
    _ = coeff e p := h sigma.symm e

/-- The degree of an exponent vector is not changed by reindexing the variables. -/
lemma degree_mapDomain {alpha beta : Type*} (f : alpha → beta) (d : alpha →₀ ℕ) :
    (Finsupp.mapDomain f d).degree = d.degree := by
  classical
  have h1 : (Finsupp.mapDomain f d).degree = (Finsupp.mapDomain f d).sum fun _ v => v := by
    simp [Finsupp.degree, Finsupp.sum]
  have h2 : d.degree = d.sum fun _ v => v := by simp [Finsupp.degree, Finsupp.sum]
  rw [h1, h2, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

/-- The homogeneous components of a symmetric polynomial are symmetric. -/
lemma isSymmetric_homogeneousComponent {p : MvPolynomial (Fin M) R} (hp : p.IsSymmetric)
    (d : ℕ) : (homogeneousComponent d p).IsSymmetric := by
  refine isSymmetric_of_coeff_mapDomain_perm fun sigma e => ?_
  rw [coeff_homogeneousComponent, coeff_homogeneousComponent, degree_mapDomain,
    coeff_mapDomain_perm hp]

/-- Truncation commutes with taking homogeneous components. -/
lemma truncVars_homogeneousComponent (h : m ≤ M) (d : ℕ) (p : MvPolynomial (Fin M) R) :
    truncVars m M R (homogeneousComponent d p) = homogeneousComponent d (truncVars m M R p) := by
  ext e
  rw [coeff_truncVars h, coeff_homogeneousComponent, coeff_homogeneousComponent,
    coeff_truncVars h, degree_mapDomain]

/-! ### Truncation of the monomials `x^lam` -/

/-- The exponent vector of the monomial `x^lam` does not depend on the number of
variables, as long as there are at least as many as the parts of `lam`. -/
lemma mapDomain_castLE_shapeContent (h : m ≤ M) {lam : List ℕ} (hlen : lam.length ≤ m) :
    Finsupp.mapDomain (Fin.castLE h) (shapeContent m lam) = shapeContent M lam := by
  ext i
  by_cases hi : (i : ℕ) < m
  · have hcast : i = Fin.castLE h ⟨i, hi⟩ := Fin.ext rfl
    rw [hcast, Finsupp.mapDomain_apply (Fin.castLE_injective h)]
    simp
  · rw [Finsupp.mapDomain_notin_range, shapeContent_apply,
      List.getD_eq_default _ _ (by omega)]
    rintro ⟨j, rfl⟩
    exact hi (by simp)

/-- The coefficient of the monomial `x^lam` is not changed by truncation. -/
lemma coeff_shapeContent_truncVars (h : m ≤ M) {lam : List ℕ} (hlen : lam.length ≤ m)
    (p : MvPolynomial (Fin M) R) :
    coeff (shapeContent m lam) (truncVars m M R p) = coeff (shapeContent M lam) p := by
  rw [coeff_truncVars h, mapDomain_castLE_shapeContent h hlen]

end CommSemiring

/-! ### Truncation in a fixed degree -/

/-- The index set of the bases does not depend on the number of variables, as long as
there are at least `n` of them. -/
def partIdxEquiv (hm : n ≤ m) (hM : n ≤ M) : PartIdx n m ≃ PartIdx n M where
  toFun mu := ⟨mu.1, mu.2.1, mu.2.2.1, mu.2.1.length_le_sum.trans (mu.2.2.1.symm ▸ hM)⟩
  invFun mu := ⟨mu.1, mu.2.1, mu.2.2.1, mu.2.1.length_le_sum.trans (mu.2.2.1.symm ▸ hm)⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma partIdxEquiv_coe (hm : n ≤ m) (hM : n ≤ M) (mu : PartIdx n m) :
    (partIdxEquiv hm hM mu).1 = mu.1 := rfl

@[simp] lemma partIdxEquiv_symm_coe (hm : n ≤ m) (hM : n ≤ M) (mu : PartIdx n M) :
    ((partIdxEquiv hm hM).symm mu).1 = mu.1 := rfl

/-- The truncation of the symmetric homogeneous polynomials of degree `n` in `M` variables
to the ones in `m` variables. -/
noncomputable def truncSub (h : m ≤ M) (n : ℕ) (R : Type*) [CommRing R] :
    symHomogeneousSubmodule M n R →ₗ[R] symHomogeneousSubmodule m n R :=
  LinearMap.restrict (truncVars m M R).toLinearMap
    fun _ hx => ⟨isHomogeneous_truncVars hx.1, isSymmetric_truncVars h hx.2⟩

@[simp] lemma coe_truncSub {R : Type*} [CommRing R] (h : m ≤ M)
    (f : symHomogeneousSubmodule M n R) :
    (truncSub h n R f : MvPolynomial (Fin m) R) = truncVars m M R f := rfl

/-- Truncation does not change the coordinates in the bases of monomial symmetric
polynomials. -/
lemma repr_mBasis_truncSub {R : Type*} [CommRing R] (hn : n ≤ m) (h : m ≤ M)
    (f : symHomogeneousSubmodule M n R) (mu : PartIdx n m) :
    (mBasis m n R).repr (truncSub h n R f) mu
      = (mBasis M n R).repr f (partIdxEquiv hn (hn.trans h) mu) := by
  rw [repr_mBasis_apply, repr_mBasis_apply, coe_truncSub,
    coeff_shapeContent_truncVars h (mu.2.1.length_le_sum.trans (mu.2.2.1.symm ▸ hn))]
  rfl

/-- Truncation maps the monomial symmetric polynomial of a partition of `n` to the
monomial symmetric polynomial of the same partition. -/
theorem truncSub_mSub {R : Type*} [CommRing R] (hn : n ≤ m) (h : m ≤ M) (mu : PartIdx n m) :
    truncSub h n R (mSub M n R (partIdxEquiv hn (hn.trans h) mu)) = mSub m n R mu := by
  apply (mBasis m n R).repr.injective
  ext nu
  rw [repr_mBasis_truncSub hn h, ← mBasis_apply, ← mBasis_apply, Module.Basis.repr_self,
    Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
  by_cases hnu : mu = nu
  · rw [ite_eq_left hnu, ite_eq_left (by rw [hnu])]
  · rw [ite_eq_right hnu, ite_eq_right fun hc => hnu ((partIdxEquiv hn (hn.trans h)).injective hc)]

/-- Truncating twice is truncating once, in a fixed degree. -/
lemma truncSub_truncSub {R : Type*} [CommRing R] (h1 : k ≤ m) (h2 : m ≤ M)
    (f : symHomogeneousSubmodule M n R) :
    truncSub h1 n R (truncSub h2 n R f) = truncSub (h1.trans h2) n R f :=
  Subtype.ext (truncVars_truncVars h1 h2 _)

/-- **Truncation is an isomorphism in degree `n` as soon as there are at least `n`
variables**: the module of symmetric homogeneous polynomials of degree `n` does not depend
on the number of variables. -/
noncomputable def truncEquiv (hn : n ≤ m) (h : m ≤ M) (R : Type*) [CommRing R] :
    symHomogeneousSubmodule M n R ≃ₗ[R] symHomogeneousSubmodule m n R :=
  LinearEquiv.ofLinear (truncSub h n R)
    ((mBasis m n R).constr R fun mu => mSub M n R (partIdxEquiv hn (hn.trans h) mu))
    (by
      refine (mBasis m n R).ext fun mu => ?_
      rw [LinearMap.comp_apply, mBasis_apply, ← mBasis_apply, Module.Basis.constr_basis,
        truncSub_mSub hn h, LinearMap.id_apply, mBasis_apply])
    (by
      refine (mBasis M n R).ext fun mu => ?_
      have hmu : mu = partIdxEquiv hn (hn.trans h) ((partIdxEquiv hn (hn.trans h)).symm mu) :=
        ((partIdxEquiv hn (hn.trans h)).apply_symm_apply mu).symm
      rw [LinearMap.comp_apply, mBasis_apply, hmu, truncSub_mSub hn h, ← mBasis_apply,
        Module.Basis.constr_basis, LinearMap.id_apply, ← hmu])

@[simp] lemma truncEquiv_apply {R : Type*} [CommRing R] (hn : n ≤ m) (h : m ≤ M)
    (f : symHomogeneousSubmodule M n R) :
    truncEquiv hn h R f = truncSub h n R f := rfl

/-- Truncation maps the monomial symmetric polynomial of a partition of size at most `m`
to the monomial symmetric polynomial of the same partition. -/
theorem truncVars_monomialSym {R : Type*} [CommRing R] (h : m ≤ M) {lam : List ℕ}
    (hlam : IsPart lam) (hn : lam.sum ≤ m) :
    truncVars m M R (monomialSym M R lam) = monomialSym m R lam := by
  simpa using congrArg Subtype.val (truncSub_mSub (R := R) hn h
    (⟨lam, hlam, rfl, hlam.length_le_sum.trans hn⟩ : PartIdx lam.sum m))

/-- Truncation maps the Schur polynomial of a partition of `n` to the Schur polynomial of
the same partition. -/
theorem truncSub_schurSub {R : Type*} [CommRing R] (hn : n ≤ m) (h : m ≤ M)
    (lam : PartIdx n m) :
    truncSub h n R (schurSub M n R (partIdxEquiv hn (hn.trans h) lam)) = schurSub m n R lam := by
  apply Subtype.ext
  rw [coe_truncSub, coe_schurSub, coe_schurSub, schurPoly_eq_sum_partIdx, map_sum]
  rw [schurPoly_eq_sum_partIdx]
  refine Fintype.sum_equiv (partIdxEquiv hn (hn.trans h)).symm _ _ fun mu => ?_
  rw [map_smul, truncVars_monomialSym h mu.2.1 (mu.2.2.1.symm ▸ hn)]
  rfl

/-- Truncation maps the Schur polynomial of a partition of size at most `m` to the Schur
polynomial of the same partition. -/
theorem truncVars_schurPoly {R : Type*} [CommRing R] (h : m ≤ M) {lam : List ℕ}
    (hlam : IsPart lam) (hn : lam.sum ≤ m) :
    truncVars m M R (schurPoly (Fin M) R lam) = schurPoly (Fin m) R lam := by
  simpa using congrArg Subtype.val (truncSub_schurSub (R := R) hn h
    (⟨lam, hlam, rfl, hlam.length_le_sum.trans hn⟩ : PartIdx lam.sum m))

/-- Truncation maps the product of complete homogeneous symmetric polynomials of a
partition of `n` to the one of the same partition. -/
theorem truncSub_hSub {R : Type*} [CommRing R] (hn : n ≤ m) (h : m ≤ M) (lam : PartIdx n m) :
    truncSub h n R (hSub M n R (partIdxEquiv hn (hn.trans h) lam)) = hSub m n R lam := by
  apply Subtype.ext
  rw [coe_truncSub, coe_hSub, coe_hSub, hProd_eq_sum_partIdx, map_sum, hProd_eq_sum_partIdx]
  refine Fintype.sum_equiv (partIdxEquiv hn (hn.trans h)).symm _ _ fun nu => ?_
  rw [map_smul, truncVars_schurPoly h nu.2.1 (nu.2.2.1.symm ▸ hn)]
  rfl

/-- Truncation maps the product of elementary symmetric polynomials of a partition of `n`
to the one of the same partition. -/
theorem truncSub_eSub {R : Type*} [CommRing R] (hn : n ≤ m) (h : m ≤ M) (lam : PartIdx n m) :
    truncSub h n R (eSub M n R (partIdxEquiv hn (hn.trans h) lam)) = eSub m n R lam := by
  apply Subtype.ext
  rw [coe_truncSub, coe_eSub, coe_eSub, eProd_conj_eq_sum_partIdx, map_sum,
    eProd_conj_eq_sum_partIdx]
  refine Fintype.sum_equiv (partIdxEquiv hn (hn.trans h)).symm _ _ fun nu => ?_
  rw [map_smul, truncVars_schurPoly h nu.2.1 (nu.2.2.1.symm ▸ hn)]
  rfl

/-- Truncation maps a power sum to the power sum in fewer variables. -/
theorem truncVars_psum {R : Type*} [CommRing R] (h : m ≤ M) {r : ℕ} (hr : 0 < r) :
    truncVars m M R (psum (Fin M) R r) = psum (Fin m) R r := by
  classical
  simp only [psum]
  rw [map_sum]
  have hf : ∀ i : Fin M, truncVars m M R (X i ^ r)
      = if hi : (i : ℕ) < m then (X (⟨i, hi⟩ : Fin m)) ^ r else 0 := by
    intro i
    rw [map_pow, truncVars_X]
    by_cases hi : (i : ℕ) < m
    · rw [dite_eq_left hi, dite_eq_left hi]
    · rw [dite_eq_right hi, dite_eq_right hi, zero_pow hr.ne']
  rw [Finset.sum_congr rfl fun i _ => hf i,
    ← Finset.sum_subset (Finset.subset_univ (Finset.image (Fin.castLE h) Finset.univ))]
  · rw [Finset.sum_image (fun a _ b _ hab => Fin.castLE_injective h hab)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dite_eq_left (show ((Fin.castLE h j : Fin M) : ℕ) < m by simp)]
    congr 2
  · intro i _ hi
    rw [dite_eq_right]
    intro hlt
    exact hi (Finset.mem_image.2 ⟨⟨i, hlt⟩, Finset.mem_univ _, rfl⟩)

/-- Truncation maps the product of power sums of a partition to the one of the same
partition. -/
theorem truncVars_pProd {R : Type*} [CommRing R] (h : m ≤ M) {lam : List ℕ}
    (hlam : IsPart lam) : truncVars m M R (pProd M R lam) = pProd m R lam := by
  rw [pProd, pProd, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun r hr => truncVars_psum h (hlam.pos_of_mem hr)

/-! ### Truncation and the Hall scalar product -/

/-- Truncation does not change the coordinates in the bases of Schur polynomials. -/
lemma repr_schurBasis_truncSub {R : Type*} [CommRing R] (hn : n ≤ m) (h : m ≤ M)
    (f : symHomogeneousSubmodule M n R) (lam : PartIdx n m) :
    (schurBasis m n R).repr (truncSub h n R f) lam
      = (schurBasis M n R).repr f (partIdxEquiv hn (hn.trans h) lam) := by
  classical
  have key : ((Finsupp.lapply lam).comp
        ((schurBasis m n R).repr : symHomogeneousSubmodule m n R →ₗ[R] (PartIdx n m →₀ R))).comp
        (truncSub h n R)
      = (Finsupp.lapply (partIdxEquiv hn (hn.trans h) lam)).comp
        ((schurBasis M n R).repr : symHomogeneousSubmodule M n R →ₗ[R] (PartIdx n M →₀ R)) := by
    refine (schurBasis M n R).ext fun nu => ?_
    have hnu : nu = partIdxEquiv hn (hn.trans h)
        ((partIdxEquiv hn (hn.trans h)).symm nu) :=
      ((partIdxEquiv hn (hn.trans h)).apply_symm_apply nu).symm
    simp only [LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe, schurBasis_apply]
    rw [hnu, truncSub_schurSub hn h, ← schurBasis_apply, ← schurBasis_apply,
      Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.single_apply,
      Finsupp.single_apply]
    by_cases hc : (partIdxEquiv hn (hn.trans h)).symm nu = lam
    · rw [ite_eq_left hc, ite_eq_left (by rw [hc])]
    · refine (ite_eq_right hc).trans (ite_eq_right fun hc' => hc ?_).symm
      exact (partIdxEquiv hn (hn.trans h)).injective hc'
  exact congrFun (congrArg (fun L : symHomogeneousSubmodule M n R →ₗ[R] R => (L : _ → R)) key) f

/-- **The Hall scalar product does not depend on the number of variables**: it is
invariant under truncation, as soon as there are at least `n` variables. -/
theorem hallInner_truncSub {R : Type*} [CommRing R] (hn : n ≤ m) (h : m ≤ M)
    (f g : symHomogeneousSubmodule M n R) :
    hallInner m n R (truncSub h n R f) (truncSub h n R g) = hallInner M n R f g := by
  rw [hallInner_apply, hallInner_apply]
  refine Fintype.sum_equiv (partIdxEquiv hn (hn.trans h)) _ _ fun lam => ?_
  rw [repr_schurBasis_truncSub hn h, repr_schurBasis_truncSub hn h]

end MvPolynomial
