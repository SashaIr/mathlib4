/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.DualPieriSchur

/-!
# The basis of products of elementary symmetric polynomials

Following `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we study the products

`e_η = e_{η_1} * ... * e_{η_k}`

of elementary symmetric polynomials.  Conjugation of partitions exchanges horizontal and vertical
strips, so the dual Pieri rule of
`Mathlib/RingTheory/MvPolynomial/Symmetric/Schur/DualPieriSchur.lean` becomes, for the family
`μ ↦ s_{μ'}`, an ordinary Pieri recursion; the general Kostka expansion of
`Mathlib/RingTheory/MvPolynomial/Symmetric/Basis/CompleteHomogeneous.lean` then gives

`e_η = ∑_nu K_{ν' η} s_ν`.

Since `K_{η' η'} = 1` and `K_{ν' η'} ≠ 0` forces `ν ⊴ η`, this expansion is
unitriangular for the dominance order, and the `e_{η'}` for `η` a partition of `n`
with at most `m` parts form a basis of the symmetric homogeneous polynomials of degree
`n` in `m` variables.

## Main definitions and results

* `MvPolynomial.eProd` : the product `e_η`.
* `MvPolynomial.eProd_eq_sum_kostka` : the expansion `e_η = ∑_nu K_{ν' η} s_ν`.
* `MvPolynomial.eBasis` : the basis of products of elementary symmetric polynomials.
-/

@[expose] public section

open Young

open List

namespace MvPolynomial

open MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-- Reindexing a sum over the partitions of `n` by conjugation. -/
lemma sum_partFinset_conjPart {M : Type*} [AddCommMonoid M] (n : ℕ) (f : List ℕ → M) :
    ∑ μ ∈ partFinset n, f μ = ∑ ν ∈ partFinset n, f (conjPart ν) := by
  refine Finset.sum_nbij' (fun μ => conjPart μ) (fun ν => conjPart ν) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hμ
    exact mem_partFinset.2 ⟨isPart_conjPart hpart, by rw [sum_conjPart, hsum]⟩
  · intro ν hν
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hν
    exact mem_partFinset.2 ⟨isPart_conjPart hpart, by rw [sum_conjPart, hsum]⟩
  · intro μ hμ
    exact conjPart_conjPart (mem_partFinset.1 hμ).1
  · intro ν hν
    exact conjPart_conjPart (mem_partFinset.1 hν).1
  · intro μ hμ
    rw [conjPart_conjPart (mem_partFinset.1 hμ).1]

/-! ### The Pieri recursion satisfied by the conjugate Schur polynomials -/

/-- The dual Pieri rule, transported by conjugation: the family `μ ↦ s_{μ'}` satisfies
the Pieri recursion with the elementary symmetric polynomials as multipliers. -/
theorem schurPoly_conjPart_mul_esymm {μ : List ℕ} (hμ : IsPart μ) (r : ℕ) :
    schurPoly (Fin m) R (conjPart μ) * esymm (Fin m) R r
      = ∑ ν ∈ partFinset (μ.sum + r),
          if HorizStrip ν μ then schurPoly (Fin m) R (conjPart ν) else 0 := by
  classical
  rw [schurPoly_mul_esymm (isPart_conjPart hμ) r, sum_conjPart,
    sum_partFinset_conjPart (μ.sum + r)
      (fun η => if VertStrip η (conjPart μ) then schurPoly (Fin m) R η else 0)]
  refine Finset.sum_congr rfl fun ν hν => ?_
  have hνpart : IsPart ν := (mem_partFinset.1 hν).1
  by_cases hstrip : HorizStrip ν μ
  · rw [ite_eq_left hstrip, ite_eq_left ((vertStrip_conjPart_iff hνpart hμ).2 hstrip)]
  · rw [ite_eq_right hstrip,
      ite_eq_right fun h => hstrip ((vertStrip_conjPart_iff hνpart hμ).1 h)]

/-! ### The products of elementary symmetric polynomials -/

/-- The product `e_η = e_{η_1} * ... * e_{η_k}` of elementary symmetric polynomials
attached to a list `η`. -/
noncomputable def eProd (m : ℕ) (R : Type*) [CommRing R] (η : List ℕ) :
    MvPolynomial (Fin m) R := (η.map (esymm (Fin m) R)).prod

@[simp] lemma eProd_nil (m : ℕ) (R : Type*) [CommRing R] : eProd m R [] = 1 := rfl

/-- **The expansion of `e_η` in the Schur polynomials**, with the Kostka numbers of
`Combinatorics/Young/Tableau/Restrict.lean` as coefficients. -/
theorem eProd_eq_sum_kostkaNum (m : ℕ) (η : List ℕ) :
    eProd m R η
      = ∑ μ ∈ partFinset η.sum,
          (kostkaNum η.length μ (contentOf η) : R) • schurPoly (Fin m) R (conjPart μ) := by
  have h := pieriProd_mul_eq_sum_kostkaNum (R := R) m (esymm (Fin m) R)
    (fun ν => schurPoly (Fin m) R (conjPart ν))
    (fun μ hμ r => schurPoly_conjPart_mul_esymm hμ r) η
  rwa [conjPart_nil, schurPoly_nil, mul_one] at h

/-- **The expansion of `e_η` in the Schur polynomials**: `e_η = ∑_nu K_{ν' η} s_ν`,
where `K_{ν' η}` is the number of tableaux of shape the conjugate of `ν` and content
`η`. -/
theorem eProd_eq_sum_kostka (m : ℕ) {η : List ℕ} (hη : IsPart η) :
    eProd m R η
      = ∑ ν ∈ partFinset η.sum, (kostka (conjPart ν) η : R) • schurPoly (Fin m) R ν := by
  rw [eProd_eq_sum_kostkaNum m η, sum_partFinset_conjPart η.sum
    (fun μ => (kostkaNum η.length μ (contentOf η) : R) • schurPoly (Fin m) R (conjPart μ))]
  refine Finset.sum_congr rfl fun ν hν => ?_
  rw [kostkaNum_eq_kostka hη (conjPart ν), conjPart_conjPart (mem_partFinset.1 hν).1]

/-! ### The expansion restricted to the partitions with at most `m` parts -/

lemma partsFinset_subset_partFinset (n m : ℕ) : partsFinset n m ⊆ partFinset n := by
  intro l hl
  obtain ⟨hp, hs, -⟩ := mem_partsFinset.1 hl
  exact mem_partFinset.2 ⟨hp, hs⟩

/-- The expansion of `e_η` in the Schur polynomials, restricted to the partitions with
at most `m` parts (the other Schur polynomials vanish). -/
theorem eProd_eq_sum_partsFinset (m : ℕ) {η : List ℕ} (hη : IsPart η) :
    eProd m R η
      = ∑ ν ∈ partsFinset η.sum m,
          (kostka (conjPart ν) η : R) • schurPoly (Fin m) R ν := by
  rw [eProd_eq_sum_kostka m hη]
  refine (Finset.sum_subset (partsFinset_subset_partFinset _ _) fun ν hν hnot => ?_).symm
  obtain ⟨hp, hs⟩ := mem_partFinset.1 hν
  have hlen : m < ν.length := by
    by_contra h
    exact hnot (mem_partsFinset.2 ⟨hp, hs, by omega⟩)
  rw [schurPoly_eq_zero_of_lt_length hlen, smul_zero]

/-- The expansion of `e_{η'}` in the Schur polynomials, indexed by `PartIdx n m`. -/
lemma eProd_conj_eq_sum_partIdx {n : ℕ} (η : PartIdx n m) :
    eProd m R (conjPart η.1)
      = ∑ ν : PartIdx n m,
          (kostka (conjPart ν.1) (conjPart η.1) : R) • schurPoly (Fin m) R ν.1 := by
  classical
  have hconj : IsPart (conjPart η.1) := isPart_conjPart η.2.1
  have hsum : (conjPart η.1).sum = n := by rw [sum_conjPart, η.2.2.1]
  rw [eProd_eq_sum_partsFinset m hconj, hsum, partsFinset,
    Finset.sum_image fun x _ y _ h => Subtype.ext h]

/-- Unitriangularity of the expansion of `e_{μ'}`: a nonzero coefficient forces the
dominance `ν ⊴ μ`. -/
lemma partdom_of_kostka_conjPart_ne_zero {n : ℕ} {ν μ : List ℕ} (hν : IsPart ν)
    (hμ : IsPart μ) (hνsum : ν.sum = n) (hμsum : μ.sum = n)
    (h : kostka (conjPart ν) (conjPart μ) ≠ 0) : Partdom ν μ :=
  (partdom_conjPart_iff hν hμ (by rw [hνsum, hμsum])).1 (partdom_of_kostka_ne_zero h)

/-! ### Linear independence -/

/-- **The products `e_{η'}` are linearly independent**: over any commutative ring, the
polynomials `e_{η'}` for `η` a partition of `n` with at most `m` parts (equivalently,
the `e_μ` for `μ` a partition of `n` with all parts at most `m`) are linearly
independent. -/
theorem linearIndependent_eProd (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R fun η : PartIdx n m => eProd m R (conjPart η.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg η
  have hexp : ∑ μ : PartIdx n m, g μ • eProd m R (conjPart μ.1)
      = ∑ ν : PartIdx n m,
          (∑ μ : PartIdx n m, g μ * (kostka (conjPart ν.1) (conjPart μ.1) : R))
            • schurPoly (Fin m) R ν.1 := by
    simp only [eProd_conj_eq_sum_partIdx, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have hcoef : ∀ ν : PartIdx n m,
      ∑ μ : PartIdx n m, g μ * (kostka (conjPart ν.1) (conjPart μ.1) : R) = 0 :=
    Fintype.linearIndependent_iff.1 (linearIndependent_schurPoly m n R) _ (by rw [← hexp, hg])
  by_contra hne
  obtain ⟨ν, hνt, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun μ : PartIdx n m => g μ ≠ 0) (fun μ => domWeight n μ.1)
    ⟨η, Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩⟩
  obtain ⟨-, hν0⟩ := Finset.mem_filter.1 hνt
  have hsingle : ∀ μ ∈ (Finset.univ : Finset (PartIdx n m)), μ ≠ ν →
      g μ * (kostka (conjPart ν.1) (conjPart μ.1) : R) = 0 := by
    intro μ _ hμne
    by_cases hgmu : g μ = 0
    · rw [hgmu, zero_mul]
    · have hμt : μ ∈ Finset.univ.filter fun μ : PartIdx n m => g μ ≠ 0 :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hgmu⟩
      have hzero : kostka (conjPart ν.1) (conjPart μ.1) = 0 := by
        by_contra hk
        have hdom : Partdom ν.1 μ.1 :=
          partdom_of_kostka_conjPart_ne_zero ν.2.1 μ.2.1 ν.2.2.1 μ.2.2.1 hk
        exact hμne (Subtype.ext (eq_of_partdom_of_domWeight_eq ν.2.1 μ.2.1 ν.2.2.1
          μ.2.2.1 hdom (hmax μ hμt)).symm)
      rw [hzero, Nat.cast_zero, mul_zero]
  have hzero := hcoef ν
  rw [Finset.sum_eq_single ν hsingle (fun h => absurd (Finset.mem_univ ν) h),
    kostka_self (isPart_conjPart ν.2.1), Nat.cast_one, mul_one] at hzero
  exact hν0 hzero

/-! ### Spanning -/

lemma eProd_conj_mem_symHomogeneousSubmodule {n : ℕ} (η : PartIdx n m) :
    eProd m R (conjPart η.1) ∈ symHomogeneousSubmodule m n R := by
  rw [eProd_conj_eq_sum_partIdx η]
  exact Submodule.sum_mem _ fun ν _ =>
    Submodule.smul_mem _ _ (schurPoly_mem_symHomogeneousSubmodule ν)

/-- Every Schur polynomial of a partition of `n` with at most `m` parts is a linear
combination of the products `e_{μ'}`. -/
theorem schurPoly_mem_span_eProd (n : ℕ) {η : List ℕ} (hη : IsPart η)
    (hsum : η.sum = n) (hlen : η.length ≤ m) :
    schurPoly (Fin m) R η
      ∈ Submodule.span R (Set.range fun μ : PartIdx n m => eProd m R (conjPart μ.1)) := by
  classical
  set W := Submodule.span R (Set.range fun μ : PartIdx n m => eProd m R (conjPart μ.1))
    with hW
  suffices H : ∀ k : ℕ, ∀ ν : List ℕ, IsPart ν → ν.sum = n → ν.length ≤ m →
      domWeight n ν ≤ k → schurPoly (Fin m) R ν ∈ W by
    exact H _ η hη hsum hlen le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro ν hν hνsum hνlen hk
    have hconj : IsPart (conjPart ν) := isPart_conjPart hν
    have hcsum : (conjPart ν).sum = n := by rw [sum_conjPart, hνsum]
    have hexp := eProd_eq_sum_partsFinset (R := R) m hconj
    rw [hcsum] at hexp
    have hmem : ν ∈ partsFinset n m := mem_partsFinset.2 ⟨hν, hνsum, hνlen⟩
    have hsplit := Finset.add_sum_erase (partsFinset n m)
      (fun μ => (kostka (conjPart μ) (conjPart ν) : R) • schurPoly (Fin m) R μ) hmem
    simp only [kostka_self hconj, Nat.cast_one, one_smul] at hsplit
    have hrest : ∀ μ ∈ (partsFinset n m).erase ν,
        (kostka (conjPart μ) (conjPart ν) : R) • schurPoly (Fin m) R μ ∈ W := by
      intro μ hμ
      have hμne : μ ≠ ν := Finset.ne_of_mem_erase hμ
      obtain ⟨hμpart, hμsum, hμlen⟩ := mem_partsFinset.1 (Finset.mem_of_mem_erase hμ)
      by_cases hk0 : kostka (conjPart μ) (conjPart ν) = 0
      · rw [hk0, Nat.cast_zero, zero_smul]
        exact Submodule.zero_mem _
      · have hdom : Partdom μ ν :=
          partdom_of_kostka_conjPart_ne_zero hμpart hν hμsum hνsum hk0
        have hlt : domWeight n μ < domWeight n ν := by
          rcases lt_or_eq_of_le (domWeight_le_domWeight (n := n) hdom) with h | h
          · exact h
          · exact absurd (eq_of_partdom_of_domWeight_eq hμpart hν hμsum hνsum hdom
              (le_of_eq h.symm)) hμne
        exact Submodule.smul_mem _ _
          (ih (domWeight n μ) (by omega) μ hμpart hμsum hμlen le_rfl)
    have hkey : schurPoly (Fin m) R ν
        = eProd m R (conjPart ν) - ∑ μ ∈ (partsFinset n m).erase ν,
            (kostka (conjPart μ) (conjPart ν) : R) • schurPoly (Fin m) R μ :=
      eq_sub_of_add_eq (hsplit.trans hexp.symm)
    rw [hkey]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨⟨ν, hν, hνsum, hνlen⟩, rfl⟩)
      (Submodule.sum_mem _ hrest)

/-- **The products `e_{η'}` span** the module of symmetric homogeneous polynomials of
degree `n` in `m` variables. -/
theorem span_eProd (m n : ℕ) :
    Submodule.span R (Set.range fun η : PartIdx n m => eProd m R (conjPart η.1))
      = symHomogeneousSubmodule m n R := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro q ⟨η, rfl⟩
    exact eProd_conj_mem_symHomogeneousSubmodule η
  · rw [← span_schurPoly m n]
    refine Submodule.span_le.2 ?_
    rintro q ⟨ν, rfl⟩
    exact schurPoly_mem_span_eProd n ν.2.1 ν.2.2.1 ν.2.2.2

/-! ### The basis -/

/-- The product `e_{η'}`, as an element of the module of symmetric homogeneous
polynomials of degree `n`. -/
noncomputable def eSub (m n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n m) :
    symHomogeneousSubmodule m n R :=
  ⟨eProd m R (conjPart η.1), eProd_conj_mem_symHomogeneousSubmodule η⟩

@[simp] lemma coe_eSub (m n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n m) :
    (eSub m n R η : MvPolynomial (Fin m) R) = eProd m R (conjPart η.1) := rfl

lemma linearIndependent_eSub (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R (eSub m n R) :=
  LinearIndependent.of_comp (symHomogeneousSubmodule m n R).subtype
    (linearIndependent_eProd m n R)

lemma span_eSub (m n : ℕ) (R : Type*) [CommRing R] :
    ⊤ ≤ Submodule.span R (Set.range (eSub m n R)) := by
  intro p _
  have hmap : Submodule.map (symHomogeneousSubmodule m n R).subtype
      (Submodule.span R (Set.range (eSub m n R))) = symHomogeneousSubmodule m n R := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact span_eProd m n
  have hp : (p : MvPolynomial (Fin m) R) ∈ Submodule.map
      (symHomogeneousSubmodule m n R).subtype
      (Submodule.span R (Set.range (eSub m n R))) := by
    rw [hmap]
    exact p.2
  obtain ⟨q, hq, hqp⟩ := hp
  have hqp' : q = p := Subtype.ext hqp
  rwa [hqp'] at hq

/-- **The products of elementary symmetric polynomials form a basis** of the module of
symmetric homogeneous polynomials of degree `n` in `m` variables, indexed by the
partitions of `n` with at most `m` parts through conjugation (equivalently, by the
partitions of `n` all of whose parts are at most `m`). -/
noncomputable def eBasis (m n : ℕ) (R : Type*) [CommRing R] :
    Module.Basis (PartIdx n m) R (symHomogeneousSubmodule m n R) :=
  Module.Basis.mk (linearIndependent_eSub m n R) (span_eSub m n R)

@[simp] lemma coe_eBasis (m n : ℕ) (R : Type*) [CommRing R] (η : PartIdx n m) :
    (eBasis m n R η : MvPolynomial (Fin m) R) = eProd m R (conjPart η.1) := by
  rw [eBasis, Module.Basis.mk_apply, coe_eSub]

end MvPolynomial
