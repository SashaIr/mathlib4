/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.List.LengthLe
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.Monomial
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.LinearIndependent
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric

/-!
# The Schur polynomials form a basis of the symmetric polynomials

Following `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove that the Schur polynomials of
the partitions of `n` with at most `m` parts form a basis of the module of symmetric
homogeneous polynomials of degree `n` in `m` variables.

Linear independence is `MvPolynomial.linearIndependent_schurPoly`.  Spanning follows from two
ingredients: a symmetric polynomial is a combination of monomial symmetric polynomials
(`MvPolynomial.eq_sum_monomialSym`) and, by the unitriangularity `s_μ = m_μ + (lower terms)`, each
monomial symmetric polynomial is a combination of Schur polynomials
(`MvPolynomial.monomialSym_mem_span_schurPoly`).

## Main results

* `MvPolynomial.monomialSym_mem_span_schurPoly` : the monomial symmetric polynomial of a partition
  of `n` with at most `m` parts is a linear combination of Schur polynomials.
* `MvPolynomial.span_schurPoly` : the Schur polynomials of the partitions of `n` with at most `m`
  parts span the symmetric homogeneous polynomials of degree `n`.
* `MvPolynomial.schurBasis` : the corresponding basis.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {m : ℕ} {R : Type*}

/-- The submodule of the symmetric homogeneous polynomials of degree `n` in `m`
variables. -/
noncomputable def symHomogeneousSubmodule (m n : ℕ) (R : Type*) [CommSemiring R] :
    Submodule R (MvPolynomial (Fin m) R) :=
  homogeneousSubmodule (Fin m) R n ⊓ (symmetricSubalgebra (Fin m) R).toSubmodule

lemma mem_symHomogeneousSubmodule [CommSemiring R] {n : ℕ} {p : MvPolynomial (Fin m) R} :
    p ∈ symHomogeneousSubmodule m n R ↔ p.IsHomogeneous n ∧ p.IsSymmetric := Iff.rfl

/-- A Schur polynomial of a shape of size `n` is homogeneous of degree `n`. -/
lemma isHomogeneous_schurPoly_of_sum [CommSemiring R] {n : ℕ} {μ : List ℕ}
    (hsum : μ.sum = n) : (schurPoly (Fin m) R μ).IsHomogeneous n := by
  rw [← hsum]
  exact isHomogeneous_schurPoly μ

lemma schurPoly_mem_symHomogeneousSubmodule [CommSemiring R] {n : ℕ} (ν : PartLengthLe n m) :
    schurPoly (Fin m) R ν.1 ∈ symHomogeneousSubmodule m n R :=
  ⟨isHomogeneous_schurPoly_of_sum ν.2.2.1, schurPoly_isSymmetric ν.1⟩

/-- The exponents of a monomial occurring in a homogeneous polynomial of degree `n` sum
to `n`. -/
lemma sum_eq_of_isHomogeneous [CommSemiring R] {n : ℕ} {p : MvPolynomial (Fin m) R}
    (hp : p.IsHomogeneous n) {d : Fin m →₀ ℕ} (hd : d ∈ p.support) : ∑ i : Fin m, d i = n := by
  classical
  have h := hp (mem_support_iff.1 hd)
  rw [Finsupp.weight_apply] at h
  simp only [smul_eq_mul, Pi.one_apply, mul_one, Finsupp.sum] at h
  rw [← h]
  exact (Finset.sum_subset (Finset.subset_univ d.support)
    fun i _ hi => by simpa using hi).symm

/-! ### Monomial symmetric polynomials are combinations of Schur polynomials -/

/-- **Unitriangularity**: the monomial symmetric polynomial of a partition of `n` with at
most `m` parts is a linear combination of the Schur polynomials of the partitions of `n`
with at most `m` parts. -/
theorem monomialSym_mem_span_schurPoly [CommRing R] (n : ℕ) {μ : List ℕ}
    (hμ : IsPart μ) (hsum : μ.sum = n) (hlen : μ.length ≤ m) :
    monomialSym m R μ ∈
      Submodule.span R (Set.range fun ν : PartLengthLe n m => schurPoly (Fin m) R ν.1) := by
  classical
  set W := Submodule.span R (Set.range fun ν : PartLengthLe n m => schurPoly (Fin m) R ν.1) with hW
  suffices H : ∀ w : ℕ, ∀ μ : List ℕ, IsPart μ → μ.sum = n → μ.length ≤ m →
      domWeight n μ = w → monomialSym m R μ ∈ W from H _ μ hμ hsum hlen rfl
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro μ hμ hsum hlen hw
    set p := schurPoly (Fin m) R μ with hp
    have hsym : p.IsSymmetric := schurPoly_isSymmetric μ
    have hhom : p.IsHomogeneous n := hsum ▸ isHomogeneous_schurPoly (R := R) μ
    set S := p.support.image degShape with hS
    have hmem : ∀ ν ∈ S, IsPart ν ∧ ν.sum = n ∧ ν.length ≤ m ∧
        coeff (shapeContent m ν) p ≠ 0 := by
      intro ν hν
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hν
      refine ⟨isPart_degShape d, ?_, length_degShape_le d, ?_⟩
      · rw [sum_degShape d]
        exact sum_eq_of_isHomogeneous hhom hd
      · rw [coeff_eq_of_degMultiset_eq hsym (degMultiset_shapeContent_degShape d)]
        exact mem_support_iff.1 hd
    have hexp : p = ∑ ν ∈ insert μ S, coeff (shapeContent m ν) p • monomialSym m R ν := by
      refine (eq_sum_monomialSym hsym).trans (Finset.sum_subset (Finset.subset_insert _ _)
        fun ν hνins hnotin => ?_)
      have hνμ : ν = μ := by
        rcases Finset.mem_insert.1 hνins with h | h
        · exact h
        · exact absurd h hnotin
      subst hνμ
      have hzero : coeff (shapeContent m ν) p = 0 := by
        by_contra hne
        exact hnotin (Finset.mem_image.2 ⟨shapeContent m ν, mem_support_iff.2 hne,
          degShape_shapeContent hμ hlen⟩)
      rw [hzero, zero_smul]
    have hone : coeff (shapeContent m μ) p = 1 := coeff_schurPoly_self hμ hlen
    have hsplit := Finset.add_sum_erase (insert μ S)
      (fun ν => coeff (shapeContent m ν) p • monomialSym m R ν)
      (Finset.mem_insert_self μ S)
    simp only [hone, one_smul] at hsplit
    have hrest : ∀ ν ∈ (insert μ S).erase μ,
        coeff (shapeContent m ν) p • monomialSym m R ν ∈ W := by
      intro ν hν
      have hne : ν ≠ μ := Finset.ne_of_mem_erase hν
      have hνS : ν ∈ S := by
        rcases Finset.mem_insert.1 (Finset.mem_of_mem_erase hν) with h | h
        · exact absurd h hne
        · exact h
      obtain ⟨hνpart, hνsum, hνlen, hνcoeff⟩ := hmem ν hνS
      have hdom : Partdom ν μ := partdom_of_coeff_ne_zero hνlen hνcoeff
      have hlt : domWeight n ν < w := by
        rcases lt_or_eq_of_le (domWeight_le_domWeight (n := n) hdom) with h | h
        · omega
        · exact absurd (eq_of_partdom_of_domWeight_eq hνpart hμ hνsum hsum hdom
            (le_of_eq h.symm)) hne
      exact Submodule.smul_mem _ _ (ih _ hlt ν hνpart hνsum hνlen rfl)
    have hpW : p ∈ W :=
      Submodule.subset_span ⟨⟨μ, hμ, hsum, hlen⟩, rfl⟩
    have hkey : monomialSym m R μ
        = p - ∑ ν ∈ (insert μ S).erase μ,
            coeff (shapeContent m ν) p • monomialSym m R ν :=
      eq_sub_of_add_eq (hsplit.trans hexp.symm)
    rw [hkey]
    exact Submodule.sub_mem _ hpW (Submodule.sum_mem _ hrest)


/-! ### The expansion of a Schur polynomial in the monomial symmetric polynomials -/

lemma finContent_shapeContent {μ : List ℕ} (hlen : μ.length ≤ m) :
    finContent m (shapeContent m μ) = fun i => μ.getD i 0 := by
  funext i
  by_cases hi : i < m
  · rw [finContent, dite_eq_left hi, shapeContent_apply]
  · rw [finContent, dite_eq_right hi, List.getD_eq_default _ _ (by omega)]

/-- **The Schur polynomial is the sum of the Kostka numbers times the monomial symmetric
polynomials**: `s_μ = ∑_ν K_{μ ν} m_ν`, the sum being over the partitions `ν` of
the size of `μ` with at most `m` parts. -/
theorem schurPoly_eq_sum_kostkaNum_monomialSym [CommRing R] (μ : List ℕ) :
    schurPoly (Fin m) R μ
      = ∑ ν ∈ partFinsetLengthLe μ.sum m,
          (kostkaNum m μ (fun i => ν.getD i 0) : R) • monomialSym m R ν := by
  classical
  set p := schurPoly (Fin m) R μ with hp
  have hsym : p.IsSymmetric := schurPoly_isSymmetric μ
  have hhom : p.IsHomogeneous μ.sum := isHomogeneous_schurPoly μ
  have hcoeff : ∀ ν ∈ partFinsetLengthLe μ.sum m,
      coeff (shapeContent m ν) p = (kostkaNum m μ (fun i => ν.getD i 0) : R) := by
    intro ν hν
    rw [hp, coeff_schurPoly_eq_kostkaNum, finContent_shapeContent (mem_partFinsetLengthLe.1 hν).2.2]
  have hsub : p.support.image degShape ⊆ partFinsetLengthLe μ.sum m := by
    intro ρ hρ
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hρ
    refine mem_partFinsetLengthLe.2 ⟨isPart_degShape d, ?_, length_degShape_le d⟩
    rw [sum_degShape d]
    exact sum_eq_of_isHomogeneous hhom hd
  have hzero : ∀ ν ∈ partFinsetLengthLe μ.sum m, ν ∉ p.support.image degShape →
      coeff (shapeContent m ν) p • monomialSym m R ν = 0 := by
    intro ν hν hnotin
    have : coeff (shapeContent m ν) p = 0 := by
      by_contra hne
      exact hnotin (Finset.mem_image.2 ⟨shapeContent m ν, mem_support_iff.2 hne,
        degShape_shapeContent (mem_partFinsetLengthLe.1 hν).1 (mem_partFinsetLengthLe.1 hν).2.2⟩)
    rw [this, zero_smul]
  calc p = ∑ ν ∈ p.support.image degShape, coeff (shapeContent m ν) p • monomialSym m R ν :=
        eq_sum_monomialSym hsym
    _ = ∑ ν ∈ partFinsetLengthLe μ.sum m, coeff (shapeContent m ν) p • monomialSym m R ν :=
        Finset.sum_subset hsub hzero
    _ = ∑ ν ∈ partFinsetLengthLe μ.sum m,
          (kostkaNum m μ (fun i => ν.getD i 0) : R) • monomialSym m R ν :=
        Finset.sum_congr rfl fun ν hν => by rw [hcoeff ν hν]

/-! ### The Schur polynomials span, and form a basis -/

/-- **The Schur polynomials span**: the Schur polynomials of the partitions of `n` with at
most `m` parts span the module of symmetric homogeneous polynomials of degree `n` in `m`
variables. -/
theorem span_schurPoly [CommRing R] (m n : ℕ) :
    Submodule.span R (Set.range fun ν : PartLengthLe n m => schurPoly (Fin m) R ν.1)
      = symHomogeneousSubmodule m n R := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) fun p hp => ?_
  · rintro q ⟨ν, rfl⟩
    exact schurPoly_mem_symHomogeneousSubmodule ν
  · obtain ⟨hhom, hsym⟩ := hp
    rw [eq_sum_monomialSym hsym]
    refine Submodule.sum_mem _ fun μ hμ => ?_
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hμ
    refine Submodule.smul_mem _ _ (monomialSym_mem_span_schurPoly n (isPart_degShape d) ?_
      (length_degShape_le d))
    rw [sum_degShape d]
    exact sum_eq_of_isHomogeneous hhom hd

/-- The Schur polynomial of a partition of `n` with at most `m` parts, as an element of the
module of symmetric homogeneous polynomials of degree `n`. -/
noncomputable def schurSub (m n : ℕ) (R : Type*) [CommRing R] (ν : PartLengthLe n m) :
    symHomogeneousSubmodule m n R :=
  ⟨schurPoly (Fin m) R ν.1, schurPoly_mem_symHomogeneousSubmodule ν⟩

@[simp] lemma coe_schurSub (m n : ℕ) (R : Type*) [CommRing R] (ν : PartLengthLe n m) :
    (schurSub m n R ν : MvPolynomial (Fin m) R) = schurPoly (Fin m) R ν.1 := rfl

lemma linearIndependent_schurSub (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R (schurSub m n R) :=
  LinearIndependent.of_comp (symHomogeneousSubmodule m n R).subtype
    (linearIndependent_schurPoly m n R)

lemma span_schurSub (m n : ℕ) (R : Type*) [CommRing R] :
    ⊤ ≤ Submodule.span R (Set.range (schurSub m n R)) := by
  intro p _
  have hmap : Submodule.map (symHomogeneousSubmodule m n R).subtype
      (Submodule.span R (Set.range (schurSub m n R))) = symHomogeneousSubmodule m n R := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact span_schurPoly m n
  have hp : (p : MvPolynomial (Fin m) R) ∈ Submodule.map
      (symHomogeneousSubmodule m n R).subtype
      (Submodule.span R (Set.range (schurSub m n R))) := by
    rw [hmap]
    exact p.2
  obtain ⟨q, hq, hqp⟩ := hp
  have hqp' : q = p := Subtype.ext hqp
  rwa [hqp'] at hq

/-- **The Schur polynomials form a basis** of the module of symmetric homogeneous
polynomials of degree `n` in `m` variables, indexed by the partitions of `n` with at most
`m` parts. -/
noncomputable def schurBasis (m n : ℕ) (R : Type*) [CommRing R] :
    Module.Basis (PartLengthLe n m) R (symHomogeneousSubmodule m n R) :=
  Module.Basis.mk (linearIndependent_schurSub m n R) (span_schurSub m n R)

lemma coe_schurBasis (m n : ℕ) (R : Type*) [CommRing R] (ν : PartLengthLe n m) :
    (schurBasis m n R ν : MvPolynomial (Fin m) R) = schurPoly (Fin m) R ν.1 := by
  rw [schurBasis, Module.Basis.mk_apply, coe_schurSub]

/-- The dimension of the space of symmetric homogeneous polynomials of degree `n` in `m`
variables is the number of partitions of `n` with at most `m` parts. -/
theorem finrank_symHomogeneousSubmodule (m n : ℕ) (R : Type*) [CommRing R]
    [StrongRankCondition R] :
    Module.finrank R (symHomogeneousSubmodule m n R) = Fintype.card (PartLengthLe n m) :=
  Module.finrank_eq_card_basis (schurBasis m n R)

end MvPolynomial
