/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Combinatorics.Young.Shape.Finset
import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.Monomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.LinearIndependent
import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric

/-!
# The Schur polynomials form a basis of the symmetric polynomials

Following `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove that the Schur polynomials of
the partitions of `n` with at most `m` parts form a basis of the module of symmetric
homogeneous polynomials of degree `n` in `m` variables.

Linear independence is `MvPolynomial.linearIndependent_schurPoly`.  Spanning follows from two
ingredients: a symmetric polynomial is a combination of monomial symmetric polynomials
(`MvPolynomial.eq_sum_monomialSym`) and, by the unitriangularity `s_λ = m_λ + (lower terms)`, each
monomial symmetric polynomial is a combination of Schur polynomials
(`MvPolynomial.monomialSym_mem_span_schurPoly`).

## Main results

* `MvPolynomial.monomialSym_mem_span_schurPoly` : the monomial symmetric polynomial of a partition
  of `n` with at most `m` parts is a linear combination of Schur polynomials.
* `MvPolynomial.span_schurPoly` : the Schur polynomials of the partitions of `n` with at most `m`
  parts span the symmetric homogeneous polynomials of degree `n`.
* `MvPolynomial.schurBasis` : the corresponding basis.
-/

namespace MvPolynomial

open List MvPolynomial

variable {m : ℕ} {R : Type*}

/-- The index set of the Schur basis: the partitions of `n` with at most `m` parts. -/
abbrev PartIdx (n m : ℕ) : Type := {p : List ℕ // IsPart p ∧ p.sum = n ∧ p.length ≤ m}

/-- The submodule of the symmetric homogeneous polynomials of degree `n` in `m`
variables. -/
def symHomogeneousSubmodule (m n : ℕ) (R : Type*) [CommSemiring R] :
    Submodule R (MvPolynomial (Fin m) R) :=
  homogeneousSubmodule (Fin m) R n ⊓ (symmetricSubalgebra (Fin m) R).toSubmodule

lemma mem_symHomogeneousSubmodule [CommSemiring R] {n : ℕ} {p : MvPolynomial (Fin m) R} :
    p ∈ symHomogeneousSubmodule m n R ↔ p.IsHomogeneous n ∧ p.IsSymmetric := Iff.rfl

/-- A Schur polynomial of a shape of size `n` is homogeneous of degree `n`. -/
lemma isHomogeneous_schurPoly_of_sum [CommSemiring R] {n : ℕ} {lam : List ℕ}
    (hsum : lam.sum = n) : (schurPoly (Fin m) R lam).IsHomogeneous n := by
  rw [← hsum]
  exact isHomogeneous_schurPoly lam

lemma schurPoly_mem_symHomogeneousSubmodule [CommSemiring R] {n : ℕ} (nu : PartIdx n m) :
    schurPoly (Fin m) R nu.1 ∈ symHomogeneousSubmodule m n R :=
  ⟨isHomogeneous_schurPoly_of_sum nu.2.2.1, schurPoly_isSymmetric nu.1⟩

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
theorem monomialSym_mem_span_schurPoly [CommRing R] (n : ℕ) {lam : List ℕ}
    (hlam : IsPart lam) (hsum : lam.sum = n) (hlen : lam.length ≤ m) :
    monomialSym m R lam ∈
      Submodule.span R (Set.range fun nu : PartIdx n m => schurPoly (Fin m) R nu.1) := by
  classical
  set W := Submodule.span R (Set.range fun nu : PartIdx n m => schurPoly (Fin m) R nu.1) with hW
  suffices H : ∀ w : ℕ, ∀ lam : List ℕ, IsPart lam → lam.sum = n → lam.length ≤ m →
      domWeight n lam = w → monomialSym m R lam ∈ W from H _ lam hlam hsum hlen rfl
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro lam hlam hsum hlen hw
    set p := schurPoly (Fin m) R lam with hp
    have hsym : p.IsSymmetric := schurPoly_isSymmetric lam
    have hhom : p.IsHomogeneous n := hsum ▸ isHomogeneous_schurPoly (R := R) lam
    set S := p.support.image degShape with hS
    have hmem : ∀ nu ∈ S, IsPart nu ∧ nu.sum = n ∧ nu.length ≤ m ∧
        coeff (shapeContent m nu) p ≠ 0 := by
      intro nu hnu
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hnu
      refine ⟨isPart_degShape d, ?_, length_degShape_le d, ?_⟩
      · rw [sum_degShape d]
        exact sum_eq_of_isHomogeneous hhom hd
      · rw [coeff_eq_of_degMultiset_eq hsym (degMultiset_shapeContent_degShape d)]
        exact mem_support_iff.1 hd
    have hexp : p = ∑ nu ∈ insert lam S, coeff (shapeContent m nu) p • monomialSym m R nu := by
      refine (eq_sum_monomialSym hsym).trans (Finset.sum_subset (Finset.subset_insert _ _)
        fun nu hnuins hnotin => ?_)
      have hnulam : nu = lam := by
        rcases Finset.mem_insert.1 hnuins with h | h
        · exact h
        · exact absurd h hnotin
      subst hnulam
      have hzero : coeff (shapeContent m nu) p = 0 := by
        by_contra hne
        exact hnotin (Finset.mem_image.2 ⟨shapeContent m nu, mem_support_iff.2 hne,
          degShape_shapeContent hlam hlen⟩)
      rw [hzero, zero_smul]
    have hone : coeff (shapeContent m lam) p = 1 := coeff_schurPoly_self hlam hlen
    have hsplit := Finset.add_sum_erase (insert lam S)
      (fun nu => coeff (shapeContent m nu) p • monomialSym m R nu)
      (Finset.mem_insert_self lam S)
    simp only [hone, one_smul] at hsplit
    have hrest : ∀ nu ∈ (insert lam S).erase lam,
        coeff (shapeContent m nu) p • monomialSym m R nu ∈ W := by
      intro nu hnu
      have hne : nu ≠ lam := Finset.ne_of_mem_erase hnu
      have hnuS : nu ∈ S := by
        rcases Finset.mem_insert.1 (Finset.mem_of_mem_erase hnu) with h | h
        · exact absurd h hne
        · exact h
      obtain ⟨hnupart, hnusum, hnulen, hnucoeff⟩ := hmem nu hnuS
      have hdom : Partdom nu lam := partdom_of_coeff_ne_zero hnulen hnucoeff
      have hlt : domWeight n nu < w := by
        rcases lt_or_eq_of_le (domWeight_le_domWeight (n := n) hdom) with h | h
        · omega
        · exact absurd (eq_of_partdom_of_domWeight_eq hnupart hlam hnusum hsum hdom
            (le_of_eq h.symm)) hne
      exact Submodule.smul_mem _ _ (ih _ hlt nu hnupart hnusum hnulen rfl)
    have hpW : p ∈ W :=
      Submodule.subset_span ⟨⟨lam, hlam, hsum, hlen⟩, rfl⟩
    have hkey : monomialSym m R lam
        = p - ∑ nu ∈ (insert lam S).erase lam,
            coeff (shapeContent m nu) p • monomialSym m R nu :=
      eq_sub_of_add_eq (hsplit.trans hexp.symm)
    rw [hkey]
    exact Submodule.sub_mem _ hpW (Submodule.sum_mem _ hrest)


/-! ### The expansion of a Schur polynomial in the monomial symmetric polynomials -/

instance fintypePartIdx (n m : ℕ) : Fintype (PartIdx n m) :=
  Fintype.ofEquiv {q : {p : List ℕ // IsPart p ∧ p.sum = n} // q.1.length ≤ m}
    { toFun := fun q => ⟨q.1.1, q.1.2.1, q.1.2.2, q.2⟩
      invFun := fun p => ⟨⟨p.1, p.2.1, p.2.2.1⟩, p.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The partitions of `n` with at most `m` parts, as a finite set of lists. -/
noncomputable def partsFinset (n m : ℕ) : Finset (List ℕ) :=
  Finset.univ.image (fun p : PartIdx n m => p.1)

lemma mem_partsFinset {n m : ℕ} {l : List ℕ} :
    l ∈ partsFinset n m ↔ IsPart l ∧ l.sum = n ∧ l.length ≤ m := by
  rw [partsFinset, Finset.mem_image]
  constructor
  · rintro ⟨q, -, rfl⟩
    exact q.2
  · intro h
    exact ⟨⟨l, h⟩, Finset.mem_univ _, rfl⟩

/-- When `n ≤ m`, every partition of `n` has at most `m` parts. -/
lemma partsFinset_eq_partFinset (n m : ℕ) (hnm : n ≤ m) : partsFinset n m = partFinset n := by
  ext l
  rw [mem_partsFinset, mem_partFinset]
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, ?_⟩⟩
  exact le_trans (le_trans h.1.length_le_sum (le_of_eq h.2)) hnm

/-- A sum over the partitions of `n` with at most `m` parts, as a sum over `PartIdx n m`. -/
lemma sum_partFinset_eq_sum_partIdx {n : ℕ} {M : Type*} [AddCommMonoid M] (hnm : n ≤ m)
    (f : List ℕ → M) : ∑ l ∈ partFinset n, f l = ∑ lam : PartIdx n m, f lam.1 := by
  rw [← partsFinset_eq_partFinset n m hnm, partsFinset,
    Finset.sum_image fun x _ y _ h => Subtype.ext h]

lemma finContent_shapeContent {mu : List ℕ} (hlen : mu.length ≤ m) :
    finContent m (shapeContent m mu) = fun i => mu.getD i 0 := by
  funext i
  by_cases hi : i < m
  · rw [finContent, dif_pos hi, shapeContent_apply]
  · rw [finContent, dif_neg hi, List.getD_eq_default _ _ (by omega)]

/-- **The Schur polynomial is the sum of the Kostka numbers times the monomial symmetric
polynomials**: `s_lam = ∑_mu K_{lam mu} m_mu`, the sum being over the partitions `mu` of
the size of `lam` with at most `m` parts. -/
theorem schurPoly_eq_sum_kostkaNum_monomialSym [CommRing R] (lam : List ℕ) :
    schurPoly (Fin m) R lam
      = ∑ mu ∈ partsFinset lam.sum m,
          (kostkaNum m lam (fun i => mu.getD i 0) : R) • monomialSym m R mu := by
  classical
  set p := schurPoly (Fin m) R lam with hp
  have hsym : p.IsSymmetric := schurPoly_isSymmetric lam
  have hhom : p.IsHomogeneous lam.sum := isHomogeneous_schurPoly lam
  have hcoeff : ∀ mu ∈ partsFinset lam.sum m,
      coeff (shapeContent m mu) p = (kostkaNum m lam (fun i => mu.getD i 0) : R) := by
    intro mu hmu
    rw [hp, coeff_schurPoly_eq_kostkaNum, finContent_shapeContent (mem_partsFinset.1 hmu).2.2]
  have hsub : p.support.image degShape ⊆ partsFinset lam.sum m := by
    intro nu hnu
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hnu
    refine mem_partsFinset.2 ⟨isPart_degShape d, ?_, length_degShape_le d⟩
    rw [sum_degShape d]
    exact sum_eq_of_isHomogeneous hhom hd
  have hzero : ∀ mu ∈ partsFinset lam.sum m, mu ∉ p.support.image degShape →
      coeff (shapeContent m mu) p • monomialSym m R mu = 0 := by
    intro mu hmu hnotin
    have : coeff (shapeContent m mu) p = 0 := by
      by_contra hne
      exact hnotin (Finset.mem_image.2 ⟨shapeContent m mu, mem_support_iff.2 hne,
        degShape_shapeContent (mem_partsFinset.1 hmu).1 (mem_partsFinset.1 hmu).2.2⟩)
    rw [this, zero_smul]
  calc p = ∑ mu ∈ p.support.image degShape, coeff (shapeContent m mu) p • monomialSym m R mu :=
        eq_sum_monomialSym hsym
    _ = ∑ mu ∈ partsFinset lam.sum m, coeff (shapeContent m mu) p • monomialSym m R mu :=
        Finset.sum_subset hsub hzero
    _ = ∑ mu ∈ partsFinset lam.sum m,
          (kostkaNum m lam (fun i => mu.getD i 0) : R) • monomialSym m R mu :=
        Finset.sum_congr rfl fun mu hmu => by rw [hcoeff mu hmu]

/-! ### The Schur polynomials span, and form a basis -/

/-- **The Schur polynomials span**: the Schur polynomials of the partitions of `n` with at
most `m` parts span the module of symmetric homogeneous polynomials of degree `n` in `m`
variables. -/
theorem span_schurPoly [CommRing R] (m n : ℕ) :
    Submodule.span R (Set.range fun nu : PartIdx n m => schurPoly (Fin m) R nu.1)
      = symHomogeneousSubmodule m n R := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) fun p hp => ?_
  · rintro q ⟨nu, rfl⟩
    exact schurPoly_mem_symHomogeneousSubmodule nu
  · obtain ⟨hhom, hsym⟩ := hp
    rw [eq_sum_monomialSym hsym]
    refine Submodule.sum_mem _ fun lam hlam => ?_
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hlam
    refine Submodule.smul_mem _ _ (monomialSym_mem_span_schurPoly n (isPart_degShape d) ?_
      (length_degShape_le d))
    rw [sum_degShape d]
    exact sum_eq_of_isHomogeneous hhom hd

/-- The Schur polynomial of a partition of `n` with at most `m` parts, as an element of the
module of symmetric homogeneous polynomials of degree `n`. -/
noncomputable def schurSub (m n : ℕ) (R : Type*) [CommRing R] (nu : PartIdx n m) :
    symHomogeneousSubmodule m n R :=
  ⟨schurPoly (Fin m) R nu.1, schurPoly_mem_symHomogeneousSubmodule nu⟩

@[simp] lemma coe_schurSub (m n : ℕ) (R : Type*) [CommRing R] (nu : PartIdx n m) :
    (schurSub m n R nu : MvPolynomial (Fin m) R) = schurPoly (Fin m) R nu.1 := rfl

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
    Module.Basis (PartIdx n m) R (symHomogeneousSubmodule m n R) :=
  Module.Basis.mk (linearIndependent_schurSub m n R) (span_schurSub m n R)

lemma coe_schurBasis (m n : ℕ) (R : Type*) [CommRing R] (nu : PartIdx n m) :
    (schurBasis m n R nu : MvPolynomial (Fin m) R) = schurPoly (Fin m) R nu.1 := by
  rw [schurBasis, Module.Basis.mk_apply, coe_schurSub]

/-- The dimension of the space of symmetric homogeneous polynomials of degree `n` in `m`
variables is the number of partitions of `n` with at most `m` parts. -/
theorem finrank_symHomogeneousSubmodule (m n : ℕ) (R : Type*) [CommRing R]
    [StrongRankCondition R] :
    Module.finrank R (symHomogeneousSubmodule m n R) = Fintype.card (PartIdx n m) :=
  Module.finrank_eq_card_basis (schurBasis m n R)

end MvPolynomial
