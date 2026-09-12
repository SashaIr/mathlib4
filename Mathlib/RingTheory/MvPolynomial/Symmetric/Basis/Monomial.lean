/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Combinatorics.Enumerative.Partition.List.Multiset
public import Mathlib.Combinatorics.Enumerative.Partition.List.TrimZeros
public import Mathlib.Data.Fintype.Perm
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Kostka

/-!
# Monomial symmetric polynomials

Following `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we introduce the monomial symmetric
polynomials `m_μ` in `m` variables and prove that they span (indeed form a basis of) the
symmetric polynomials.

The shape `degShape d` of an exponent vector `d : Fin m →₀ ℕ` is the partition obtained by
sorting its entries decreasingly, and `monomialSym m R μ` is the sum of the monomials
whose exponent vector has shape `μ`, i.e. the orbit sum of the monomial `x ^ μ` under
the permutations of the variables.

## Main definitions

* `MvPolynomial.degShape d` : the partition of the exponents of a monomial.
* `MvPolynomial.degOrbit d` : the orbit of an exponent vector under the permutations of the
  variables.
* `MvPolynomial.monomialSym m R μ` : the monomial symmetric polynomial of shape `μ`.

## Main results

* `MvPolynomial.monomialSym_isSymmetric` : the monomial symmetric polynomials are symmetric.
* `MvPolynomial.eq_sum_monomialSym` : a symmetric polynomial is the sum of the
  monomial symmetric polynomials of the shapes occurring in it, with the corresponding
  coefficients.
* `MvPolynomial.span_monomialSym` : the monomial symmetric polynomials span the symmetric
  polynomials.
* `MvPolynomial.linearIndependent_monomialSym` : the monomial symmetric polynomials of distinct
  shapes are linearly independent.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {m : ℕ} {R : Type*}

/-! ### The multiset of exponents of a monomial -/

/-- The multiset of the exponents of a monomial in `m` variables. -/
def degMultiset (d : Fin m →₀ ℕ) : Multiset ℕ := Multiset.map d Finset.univ.val

@[simp] lemma card_degMultiset (d : Fin m →₀ ℕ) : Multiset.card (degMultiset d) = m := by
  simp [degMultiset]

/-- Two exponent vectors with the same multiset of exponents differ by a permutation of the
variables. -/
lemma exists_perm_of_degMultiset_eq {d d' : Fin m →₀ ℕ} (h : degMultiset d = degMultiset d') :
    ∃ e : Equiv.Perm (Fin m), ∀ i, d' (e i) = d i := by
  classical
  have hcard : ∀ n : ℕ,
      Fintype.card {i : Fin m // d i = n} = Fintype.card {i : Fin m // d' i = n} := by
    intro n
    have hc := congrArg (Multiset.count n) h
    rw [degMultiset, degMultiset, Multiset.count_map, Multiset.count_map] at hc
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.filter, eq_comm] using hc
  let e0 : (Σ n : ℕ, {i : Fin m // d i = n}) ≃ (Σ n : ℕ, {i : Fin m // d' i = n}) :=
    Equiv.sigmaCongrRight fun n => Fintype.equivOfCardEq (hcard n)
  exact ⟨(Equiv.sigmaFiberEquiv (d : Fin m → ℕ)).symm.trans
    (e0.trans (Equiv.sigmaFiberEquiv (d' : Fin m → ℕ))), fun i => (e0 ⟨d i, i, rfl⟩).2.2⟩

lemma degMultiset_equivMapDomain (d : Fin m →₀ ℕ) (e : Equiv.Perm (Fin m)) :
    degMultiset (Finsupp.equivMapDomain e d) = degMultiset d := by
  classical
  rw [degMultiset, degMultiset]
  have hmap : Multiset.map (fun i => d (e.symm i)) Finset.univ.val
      = Multiset.map (fun i => d i) (Multiset.map e.symm Finset.univ.val) := by
    rw [Multiset.map_map]; rfl
  rw [show ((Finsupp.equivMapDomain e d : Fin m →₀ ℕ) : Fin m → ℕ) = fun i => d (e.symm i) from rfl,
    hmap, Multiset.map_univ_val_equiv]

/-! ### The shape of a monomial -/

/-- The exponents of a monomial in `m` variables, sorted decreasingly. -/
noncomputable def degSorted (d : Fin m →₀ ℕ) : List ℕ := sortDesc (degMultiset d)

@[simp] lemma coe_degSorted (d : Fin m →₀ ℕ) : (degSorted d : Multiset ℕ) = degMultiset d :=
  coe_sortDesc _

@[simp] lemma length_degSorted (d : Fin m →₀ ℕ) : (degSorted d).length = m := by
  rw [degSorted, sortDesc, Multiset.length_sort, card_degMultiset]

lemma degSorted_antitone (d : Fin m →₀ ℕ) (i : ℕ) :
    (degSorted d).getD (i + 1) 0 ≤ (degSorted d).getD i 0 := by
  by_cases h : i + 1 < (degSorted d).length
  · have hp : List.Pairwise (· ≥ ·) (degSorted d) := pairwise_sortDesc _
    rw [List.getD_eq_getElem _ _ (by omega : i < (degSorted d).length),
      List.getD_eq_getElem _ _ h]
    exact List.pairwise_iff_getElem.1 hp i (i + 1) (by omega) h (by omega)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

/-- The shape of a monomial: the partition given by its exponents sorted decreasingly. -/
noncomputable def degShape (d : Fin m →₀ ℕ) : List ℕ := trimZeros (degSorted d)

lemma degShape_eq_shapeOfFn (d : Fin m →₀ ℕ) :
    degShape d = shapeOfFn m (fun i => (degSorted d).getD i 0) := by
  rw [degShape, shapeOfFn]
  congr 1
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

lemma isPart_degShape (d : Fin m →₀ ℕ) : IsPart (degShape d) := by
  rw [degShape_eq_shapeOfFn]
  exact isPart_shapeOfFn (degSorted_antitone d)

lemma length_degShape_le (d : Fin m →₀ ℕ) : (degShape d).length ≤ m := by
  rw [degShape_eq_shapeOfFn]
  exact length_shapeOfFn_le _ _

lemma getD_degShape (d : Fin m →₀ ℕ) (i : ℕ) :
    (degShape d).getD i 0 = (degSorted d).getD i 0 := getD_trimZeros _ _

lemma sum_degShape (d : Fin m →₀ ℕ) : (degShape d).sum = ∑ i, d i := by
  rw [degShape, sum_trimZeros, degSorted, sum_sortDesc, degMultiset, Finset.sum]

/-! ### Recovering the exponents from the shape -/

lemma degMultiset_shapeContent (μ : List ℕ) :
    degMultiset (shapeContent m μ) = Multiset.map (fun i : Fin m => μ.getD i 0)
      Finset.univ.val := rfl

lemma degMultiset_shapeContent_degShape (d : Fin m →₀ ℕ) :
    degMultiset (shapeContent m (degShape d)) = degMultiset d := by
  rw [degMultiset_shapeContent]
  have : ∀ i : Fin m, (degShape d).getD i 0 = (degSorted d).getD i 0 := fun i => getD_degShape d i
  rw [Multiset.map_congr rfl (fun i _ => this i)]
  have hofFn : List.ofFn (fun i : Fin m => (degSorted d).getD (i : ℕ) 0) = degSorted d := by
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp
  have hmap : Multiset.map (fun i : Fin m => (degSorted d).getD (i : ℕ) 0) Finset.univ.val
      = ((List.ofFn (fun i : Fin m => (degSorted d).getD (i : ℕ) 0) : List ℕ) : Multiset ℕ) := by
    rw [List.ofFn_eq_map]
    rfl
  rw [hmap, hofFn, coe_degSorted]

lemma degShape_shapeContent {μ : List ℕ} (hμ : IsPart μ) (hlen : μ.length ≤ m) :
    degShape (shapeContent m μ) = μ := by
  have hpair : List.Pairwise (· ≥ ·) (List.ofFn (fun i : Fin m => μ.getD (i : ℕ) 0)) := by
    refine List.pairwise_iff_getElem.2 fun i j hi hj hij => ?_
    simp only [List.getElem_ofFn]
    exact hμ.getD_antitone (le_of_lt hij)
  have hperm : (degSorted (shapeContent m μ)).Perm
      (List.ofFn (fun i : Fin m => μ.getD (i : ℕ) 0)) := by
    rw [← Multiset.coe_eq_coe, coe_degSorted, degMultiset_shapeContent, List.ofFn_eq_map]
    rfl
  have hsorted : degSorted (shapeContent m μ)
      = List.ofFn (fun i : Fin m => μ.getD (i : ℕ) 0) :=
    List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hba hab)
      (pairwise_sortDesc _) hpair hperm
  rw [degShape, hsorted]
  exact shapeOfFn_getD hμ hlen

/-! ### The orbit of a monomial -/

/-- The orbit of an exponent vector under the permutations of the variables. -/
noncomputable def degOrbit (d : Fin m →₀ ℕ) : Finset (Fin m →₀ ℕ) := by
  classical
  exact Finset.image (fun e : Equiv.Perm (Fin m) => Finsupp.equivMapDomain e d) Finset.univ

lemma mem_degOrbit_iff {d d' : Fin m →₀ ℕ} :
    d' ∈ degOrbit d ↔ degMultiset d' = degMultiset d := by
  classical
  constructor
  · rintro hd'
    rw [degOrbit] at hd'
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hd'
    exact degMultiset_equivMapDomain d e
  · intro h
    obtain ⟨e, he⟩ := exists_perm_of_degMultiset_eq h
    refine Finset.mem_image.2 ⟨e.symm, Finset.mem_univ _, ?_⟩
    ext i
    simpa using he i

lemma self_mem_degOrbit (d : Fin m →₀ ℕ) : d ∈ degOrbit d := mem_degOrbit_iff.2 rfl

lemma degOrbit_eq_of_mem {d d' : Fin m →₀ ℕ} (h : d' ∈ degOrbit d) : degOrbit d' = degOrbit d := by
  ext x
  rw [mem_degOrbit_iff, mem_degOrbit_iff, mem_degOrbit_iff.1 h]

/-- Two monomials have the same shape exactly when they have the same multiset of
exponents. -/
lemma degShape_eq_iff {d d' : Fin m →₀ ℕ} :
    degShape d = degShape d' ↔ degMultiset d = degMultiset d' := by
  constructor
  · intro h
    rw [← degMultiset_shapeContent_degShape d, ← degMultiset_shapeContent_degShape d', h]
  · intro h
    rw [degShape, degShape, degSorted, degSorted, h]

lemma mem_degOrbit_shapeContent_degShape (d : Fin m →₀ ℕ) :
    d ∈ degOrbit (shapeContent m (degShape d)) :=
  mem_degOrbit_iff.2 (degMultiset_shapeContent_degShape d).symm

/-! ### Coefficients of a symmetric polynomial -/

/-- The coefficients of a symmetric polynomial only depend on the multiset of exponents. -/
lemma coeff_eq_of_degMultiset_eq [CommSemiring R] {p : MvPolynomial (Fin m) R}
    (hp : p.IsSymmetric) {d d' : Fin m →₀ ℕ} (h : degMultiset d = degMultiset d') :
    p.coeff d = p.coeff d' := by
  obtain ⟨e, he⟩ := exists_perm_of_degMultiset_eq h
  have hd : d = Finsupp.mapDomain (⇑e.symm) d' := by
    rw [← Finsupp.equivMapDomain_eq_mapDomain]
    ext i
    simpa using (he i).symm
  calc p.coeff d = ((rename ⇑e.symm) p).coeff (Finsupp.mapDomain (⇑e.symm) d') := by
        rw [hd, hp e.symm]
    _ = p.coeff d' := coeff_rename_mapDomain _ e.symm.injective _ _

/-! ### The monomial symmetric polynomials -/

/-- The monomial symmetric polynomial `m_μ` in `m` variables: the sum of all the
monomials whose exponents are, up to a permutation of the variables, the parts of `μ`. -/
noncomputable def monomialSym (m : ℕ) (R : Type*) [CommSemiring R] (μ : List ℕ) :
    MvPolynomial (Fin m) R :=
  ∑ d ∈ degOrbit (shapeContent m μ), monomial d 1

lemma coeff_monomialSym [CommSemiring R] (μ : List ℕ) (d : Fin m →₀ ℕ) :
    (monomialSym m R μ).coeff d = if d ∈ degOrbit (shapeContent m μ) then 1 else 0 := by
  classical
  rw [monomialSym, coeff_sum]
  rw [Finset.sum_congr rfl (fun d' _ => coeff_monomial d d' (1 : R))]
  by_cases hd : d ∈ degOrbit (shapeContent m μ)
  · rw [ite_eq_left hd, Finset.sum_ite_eq' (degOrbit (shapeContent m μ)) d (fun _ => (1 : R)),
      ite_eq_left hd]
  · rw [ite_eq_right hd,
      Finset.sum_eq_zero fun d' hd' => ite_eq_right (by rintro rfl; exact hd hd')]

lemma coeff_monomialSym_shapeContent [CommSemiring R] (μ : List ℕ) :
    (monomialSym m R μ).coeff (shapeContent m μ) = 1 := by
  rw [coeff_monomialSym, ite_eq_left (self_mem_degOrbit _)]

/-- The monomial symmetric polynomials are symmetric. -/
theorem monomialSym_isSymmetric [CommSemiring R] (μ : List ℕ) :
    (monomialSym m R μ).IsSymmetric := by
  classical
  intro e
  rw [monomialSym, map_sum]
  refine Finset.sum_nbij' (i := fun d => Finsupp.equivMapDomain e d)
    (j := fun d => Finsupp.equivMapDomain e.symm d) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [mem_degOrbit_iff, degMultiset_equivMapDomain]
    exact mem_degOrbit_iff.1 hd
  · intro d hd
    rw [mem_degOrbit_iff, degMultiset_equivMapDomain]
    exact mem_degOrbit_iff.1 hd
  · intro d _
    ext i
    simp
  · intro d _
    ext i
    simp
  · intro d _
    rw [rename_monomial, ← Finsupp.equivMapDomain_eq_mapDomain]

/-- All the monomials of `m_μ` have degree the size of `μ`. -/
lemma sum_eq_of_mem_degOrbit_shapeContent {μ : List ℕ} (hμ : IsPart μ)
    (hlen : μ.length ≤ m) {d : Fin m →₀ ℕ} (hd : d ∈ degOrbit (shapeContent m μ)) :
    ∑ i, d i = μ.sum := by
  have hν : degShape d = μ := by
    rw [degShape_eq_iff.2 (mem_degOrbit_iff.1 hd), degShape_shapeContent hμ hlen]
  rw [← sum_degShape d, hν]

/-! ### Expansion of a symmetric polynomial in the monomial symmetric polynomials -/

/-- **A symmetric polynomial is a combination of monomial symmetric polynomials**: it is
the sum, over the shapes of the monomials occurring in it, of the corresponding coefficient
times the monomial symmetric polynomial of that shape. -/
theorem eq_sum_monomialSym [CommSemiring R] {p : MvPolynomial (Fin m) R}
    (hp : p.IsSymmetric) :
    p = ∑ μ ∈ p.support.image degShape,
      p.coeff (shapeContent m μ) • monomialSym m R μ := by
  classical
  conv_lhs => rw [← support_sum_monomial_coeff p]
  rw [← Finset.sum_fiberwise_of_maps_to (g := degShape) (t := p.support.image degShape)
    (fun d hd => Finset.mem_image_of_mem _ hd)
    (fun d => (monomial d) (p.coeff d))]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  obtain ⟨d0, hd0, hd0shape⟩ := Finset.mem_image.1 hμ
  have hμContent : degShape (shapeContent m μ) = μ := by
    rw [← hd0shape]
    exact degShape_shapeContent (isPart_degShape d0) (length_degShape_le d0)
  have hcoeff : ∀ d : Fin m →₀ ℕ, d ∈ degOrbit (shapeContent m μ) →
      p.coeff d = p.coeff (shapeContent m μ) := fun d hd =>
    coeff_eq_of_degMultiset_eq hp (mem_degOrbit_iff.1 hd)
  have hfilter : p.support.filter (fun d => degShape d = μ)
      = degOrbit (shapeContent m μ) := by
    ext d
    rw [Finset.mem_filter, mem_degOrbit_iff]
    constructor
    · rintro ⟨-, hdlam⟩
      exact degShape_eq_iff.1 (by rw [hdlam, hμContent])
    · intro hd
      have hdshape : degShape d = μ := by rw [degShape_eq_iff.2 hd, hμContent]
      refine ⟨?_, hdshape⟩
      have h0 : p.coeff (shapeContent m μ) = p.coeff d0 :=
        coeff_eq_of_degMultiset_eq hp (by
          rw [← hd0shape, degMultiset_shapeContent_degShape])
      have hd0ne : p.coeff d0 ≠ 0 := mem_support_iff.1 hd0
      refine mem_support_iff.2 ?_
      rw [hcoeff d (mem_degOrbit_iff.2 hd), h0]
      exact hd0ne
  rw [hfilter, monomialSym, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [smul_monomial, smul_eq_mul, mul_one, hcoeff d hd]

/-- **The monomial symmetric polynomials span the symmetric polynomials**: they generate,
as a module over the base ring, the symmetric polynomials in `m` variables. -/
theorem span_monomialSym (m : ℕ) (R : Type*) [CommRing R] :
    Submodule.span R (Set.range fun μ : {l : List ℕ // IsPart l ∧ l.length ≤ m} =>
        monomialSym m R μ.1)
      = (symmetricSubalgebra (Fin m) R).toSubmodule := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) fun p hp => ?_
  · rintro q ⟨μ, rfl⟩
    exact monomialSym_isSymmetric μ.1
  · rw [eq_sum_monomialSym ((mem_symmetricSubalgebra p).1 hp)]
    refine Submodule.sum_mem _ fun μ hμ => ?_
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hμ
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨⟨degShape d, isPart_degShape d, length_degShape_le d⟩, rfl⟩)

/-- The monomial symmetric polynomials of distinct partitions with at most `m` parts are
linearly independent. -/
theorem linearIndependent_monomialSym (m : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R fun μ : {l : List ℕ // IsPart l ∧ l.length ≤ m} =>
      monomialSym m R μ.1 := by
  classical
  rw [linearIndependent_iff']
  intro s g hg μ hμ
  have hcoeff := congrArg (·.coeff (shapeContent m μ.1)) hg
  rw [coeff_sum] at hcoeff
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoeff
  have hsingle : ∀ ν ∈ s, ν ≠ μ →
      (g ν • monomialSym m R ν.1).coeff (shapeContent m μ.1) = 0 := by
    intro ν _ hne
    rw [coeff_smul, smul_eq_mul, coeff_monomialSym, ite_eq_right, mul_zero]
    intro hmem
    refine hne (Subtype.ext ?_)
    have := degShape_eq_iff.2 (mem_degOrbit_iff.1 hmem)
    rw [degShape_shapeContent μ.2.1 μ.2.2, degShape_shapeContent ν.2.1 ν.2.2] at this
    exact this.symm
  rw [Finset.sum_eq_single μ hsingle (fun h => absurd hμ h), coeff_smul, smul_eq_mul,
    coeff_monomialSym_shapeContent, mul_one] at hcoeff
  exact hcoeff

/-! ### The basis of monomial symmetric polynomials -/

/-- The monomial symmetric polynomial of a partition with at most `m` parts, as an element
of the module of symmetric polynomials. -/
noncomputable def monomialSymSub (m : ℕ) (R : Type*) [CommRing R]
    (μ : {l : List ℕ // IsPart l ∧ l.length ≤ m}) :
    (symmetricSubalgebra (Fin m) R).toSubmodule :=
  ⟨monomialSym m R μ.1, monomialSym_isSymmetric μ.1⟩

@[simp] lemma coe_monomialSymSub (m : ℕ) (R : Type*) [CommRing R]
    (μ : {l : List ℕ // IsPart l ∧ l.length ≤ m}) :
    (monomialSymSub m R μ : MvPolynomial (Fin m) R) = monomialSym m R μ.1 := rfl

lemma linearIndependent_monomialSymSub (m : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R (monomialSymSub m R) :=
  LinearIndependent.of_comp (symmetricSubalgebra (Fin m) R).toSubmodule.subtype
    (linearIndependent_monomialSym m R)

lemma span_monomialSymSub (m : ℕ) (R : Type*) [CommRing R] :
    ⊤ ≤ Submodule.span R (Set.range (monomialSymSub m R)) := by
  intro p _
  have hmap : Submodule.map (symmetricSubalgebra (Fin m) R).toSubmodule.subtype
      (Submodule.span R (Set.range (monomialSymSub m R)))
      = (symmetricSubalgebra (Fin m) R).toSubmodule := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact span_monomialSym m R
  have hp : (p : MvPolynomial (Fin m) R) ∈ Submodule.map
      (symmetricSubalgebra (Fin m) R).toSubmodule.subtype
      (Submodule.span R (Set.range (monomialSymSub m R))) := by
    rw [hmap]
    exact p.2
  obtain ⟨q, hq, hqp⟩ := hp
  have hqp' : q = p := Subtype.ext hqp
  rwa [hqp'] at hq

/-- **The monomial symmetric polynomials form a basis** of the module of symmetric
polynomials in `m` variables, indexed by the partitions with at most `m` parts. -/
noncomputable def monomialSymBasis (m : ℕ) (R : Type*) [CommRing R] :
    Module.Basis {l : List ℕ // IsPart l ∧ l.length ≤ m} R
      (symmetricSubalgebra (Fin m) R).toSubmodule :=
  Module.Basis.mk (linearIndependent_monomialSymSub m R) (span_monomialSymSub m R)

@[simp] lemma coe_monomialSymBasis (m : ℕ) (R : Type*) [CommRing R]
    (μ : {l : List ℕ // IsPart l ∧ l.length ≤ m}) :
    (monomialSymBasis m R μ : MvPolynomial (Fin m) R) = monomialSym m R μ.1 := by
  rw [monomialSymBasis, Module.Basis.mk_apply, coe_monomialSymSub]

end MvPolynomial
