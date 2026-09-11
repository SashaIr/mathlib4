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

`e_μ = e_{μ_1} * ... * e_{μ_k}`

of elementary symmetric polynomials.  Conjugation of partitions exchanges horizontal and vertical
strips, so the dual Pieri rule of
`Mathlib/RingTheory/MvPolynomial/Symmetric/Schur/DualPieriSchur.lean` becomes, for the family
`ν ↦ s_{ν'}`, an ordinary Pieri recursion; the general Kostka expansion of
`Mathlib/RingTheory/MvPolynomial/Symmetric/Basis/CompleteHomogeneous.lean` then gives

`e_μ = ∑_nu K_{ρ' μ} s_ρ`.

Since `K_{μ' μ'} = 1` and `K_{ρ' μ'} ≠ 0` forces `ρ ⊴ μ`, this expansion is
unitriangular for the dominance order, and the `e_{μ'}` for `μ` a partition of `n`
with at most `m` parts form a basis of the symmetric homogeneous polynomials of degree
`n` in `m` variables.

## Main definitions and results

* `MvPolynomial.eProd` : the product `e_μ`.
* `MvPolynomial.eProd_eq_sum_kostka` : the expansion `e_μ = ∑_nu K_{ρ' μ} s_ρ`.
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

/-- The dual Pieri rule, transported by conjugation: the family `ν ↦ s_{ν'}` satisfies
the Pieri recursion with the elementary symmetric polynomials as multipliers. -/
theorem schurPoly_conjPart_mul_esymm {ν : List ℕ} (hν : IsPart ν) (r : ℕ) :
    schurPoly (Fin m) R (conjPart ν) * esymm (Fin m) R r
      = ∑ ρ ∈ partFinset (ν.sum + r),
          if HorizStrip ρ ν then schurPoly (Fin m) R (conjPart ρ) else 0 := by
  classical
  rw [schurPoly_mul_esymm (isPart_conjPart hν) r, sum_conjPart,
    sum_partFinset_conjPart (ν.sum + r)
      (fun μ => if VertStrip μ (conjPart ν) then schurPoly (Fin m) R μ else 0)]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  have hρpart : IsPart ρ := (mem_partFinset.1 hρ).1
  by_cases hstrip : HorizStrip ρ ν
  · rw [ite_eq_left hstrip, ite_eq_left ((vertStrip_conjPart_iff hρpart hν).2 hstrip)]
  · rw [ite_eq_right hstrip,
      ite_eq_right fun h => hstrip ((vertStrip_conjPart_iff hρpart hν).1 h)]

/-! ### The products of elementary symmetric polynomials -/

/-- The product `e_μ = e_{μ_1} * ... * e_{μ_k}` of elementary symmetric polynomials
attached to a list `μ`. -/
noncomputable def eProd (m : ℕ) (R : Type*) [CommRing R] (μ : List ℕ) :
    MvPolynomial (Fin m) R := (μ.map (esymm (Fin m) R)).prod

@[simp] lemma eProd_nil (m : ℕ) (R : Type*) [CommRing R] : eProd m R [] = 1 := rfl

/-- **The expansion of `e_μ` in the Schur polynomials**, with the Kostka numbers of
`Combinatorics/Young/Tableau/Restrict.lean` as coefficients. -/
theorem eProd_eq_sum_kostkaNum (m : ℕ) (μ : List ℕ) :
    eProd m R μ
      = ∑ ν ∈ partFinset μ.sum,
          (kostkaNum μ.length ν (contentOf μ) : R) • schurPoly (Fin m) R (conjPart ν) := by
  have h := pieriProd_mul_eq_sum_kostkaNum (R := R) m (esymm (Fin m) R)
    (fun ρ => schurPoly (Fin m) R (conjPart ρ))
    (fun ν hν r => schurPoly_conjPart_mul_esymm hν r) μ
  rwa [conjPart_nil, schurPoly_nil, mul_one] at h

/-- **The expansion of `e_μ` in the Schur polynomials**: `e_μ = ∑_nu K_{ρ' μ} s_ρ`,
where `K_{ρ' μ}` is the number of tableaux of shape the conjugate of `ρ` and content
`μ`. -/
theorem eProd_eq_sum_kostka (m : ℕ) {μ : List ℕ} (hμ : IsPart μ) :
    eProd m R μ
      = ∑ ρ ∈ partFinset μ.sum, (kostka (conjPart ρ) μ : R) • schurPoly (Fin m) R ρ := by
  rw [eProd_eq_sum_kostkaNum m μ, sum_partFinset_conjPart μ.sum
    (fun ν => (kostkaNum μ.length ν (contentOf μ) : R) • schurPoly (Fin m) R (conjPart ν))]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [kostkaNum_eq_kostka hμ (conjPart ρ), conjPart_conjPart (mem_partFinset.1 hρ).1]

/-! ### The expansion restricted to the partitions with at most `m` parts -/

lemma partsFinset_subset_partFinset (n m : ℕ) : partsFinset n m ⊆ partFinset n := by
  intro l hl
  obtain ⟨hp, hs, -⟩ := mem_partsFinset.1 hl
  exact mem_partFinset.2 ⟨hp, hs⟩

/-- The expansion of `e_μ` in the Schur polynomials, restricted to the partitions with
at most `m` parts (the other Schur polynomials vanish). -/
theorem eProd_eq_sum_partsFinset (m : ℕ) {μ : List ℕ} (hμ : IsPart μ) :
    eProd m R μ
      = ∑ ν ∈ partsFinset μ.sum m,
          (kostka (conjPart ν) μ : R) • schurPoly (Fin m) R ν := by
  rw [eProd_eq_sum_kostka m hμ]
  refine (Finset.sum_subset (partsFinset_subset_partFinset _ _) fun ν hν hnot => ?_).symm
  obtain ⟨hp, hs⟩ := mem_partFinset.1 hν
  have hlen : m < ν.length := by
    by_contra h
    exact hnot (mem_partsFinset.2 ⟨hp, hs, by omega⟩)
  rw [schurPoly_eq_zero_of_lt_length hlen, smul_zero]

/-- The expansion of `e_{μ'}` in the Schur polynomials, indexed by `PartIdx n m`. -/
lemma eProd_conj_eq_sum_partIdx {n : ℕ} (μ : PartIdx n m) :
    eProd m R (conjPart μ.1)
      = ∑ ν : PartIdx n m,
          (kostka (conjPart ν.1) (conjPart μ.1) : R) • schurPoly (Fin m) R ν.1 := by
  classical
  have hconj : IsPart (conjPart μ.1) := isPart_conjPart μ.2.1
  have hsum : (conjPart μ.1).sum = n := by rw [sum_conjPart, μ.2.2.1]
  rw [eProd_eq_sum_partsFinset m hconj, hsum, partsFinset,
    Finset.sum_image fun x _ y _ h => Subtype.ext h]

/-- Unitriangularity of the expansion of `e_{μ'}`: a nonzero coefficient forces the
dominance `ν ⊴ μ`. -/
lemma partdom_of_kostka_conjPart_ne_zero {n : ℕ} {ν μ : List ℕ} (hν : IsPart ν)
    (hμ : IsPart μ) (hνsum : ν.sum = n) (hμsum : μ.sum = n)
    (h : kostka (conjPart ν) (conjPart μ) ≠ 0) : Partdom ν μ :=
  (partdom_conjPart_iff hν hμ (by rw [hνsum, hμsum])).1 (partdom_of_kostka_ne_zero h)

/-! ### Linear independence -/

/-- **The products `e_{μ'}` are linearly independent**: over any commutative ring, the
polynomials `e_{μ'}` for `μ` a partition of `n` with at most `m` parts (equivalently,
the `e_ν` for `ν` a partition of `n` with all parts at most `m`) are linearly
independent. -/
theorem linearIndependent_eProd (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R fun μ : PartIdx n m => eProd m R (conjPart μ.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg μ
  have hexp : ∑ ν : PartIdx n m, g ν • eProd m R (conjPart ν.1)
      = ∑ ρ : PartIdx n m,
          (∑ ν : PartIdx n m, g ν * (kostka (conjPart ρ.1) (conjPart ν.1) : R))
            • schurPoly (Fin m) R ρ.1 := by
    simp only [eProd_conj_eq_sum_partIdx, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have hcoef : ∀ ρ : PartIdx n m,
      ∑ ν : PartIdx n m, g ν * (kostka (conjPart ρ.1) (conjPart ν.1) : R) = 0 :=
    Fintype.linearIndependent_iff.1 (linearIndependent_schurPoly m n R) _ (by rw [← hexp, hg])
  by_contra hne
  obtain ⟨ρ, hρt, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun ν : PartIdx n m => g ν ≠ 0) (fun ν => domWeight n ν.1)
    ⟨μ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩⟩
  obtain ⟨-, hρ0⟩ := Finset.mem_filter.1 hρt
  have hsingle : ∀ ν ∈ (Finset.univ : Finset (PartIdx n m)), ν ≠ ρ →
      g ν * (kostka (conjPart ρ.1) (conjPart ν.1) : R) = 0 := by
    intro ν _ hνne
    by_cases hgmu : g ν = 0
    · rw [hgmu, zero_mul]
    · have hνt : ν ∈ Finset.univ.filter fun ν : PartIdx n m => g ν ≠ 0 :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hgmu⟩
      have hzero : kostka (conjPart ρ.1) (conjPart ν.1) = 0 := by
        by_contra hk
        have hdom : Partdom ρ.1 ν.1 :=
          partdom_of_kostka_conjPart_ne_zero ρ.2.1 ν.2.1 ρ.2.2.1 ν.2.2.1 hk
        exact hνne (Subtype.ext (eq_of_partdom_of_domWeight_eq ρ.2.1 ν.2.1 ρ.2.2.1
          ν.2.2.1 hdom (hmax ν hνt)).symm)
      rw [hzero, Nat.cast_zero, mul_zero]
  have hzero := hcoef ρ
  rw [Finset.sum_eq_single ρ hsingle (fun h => absurd (Finset.mem_univ ρ) h),
    kostka_self (isPart_conjPart ρ.2.1), Nat.cast_one, mul_one] at hzero
  exact hρ0 hzero

/-! ### Spanning -/

lemma eProd_conj_mem_symHomogeneousSubmodule {n : ℕ} (μ : PartIdx n m) :
    eProd m R (conjPart μ.1) ∈ symHomogeneousSubmodule m n R := by
  rw [eProd_conj_eq_sum_partIdx μ]
  exact Submodule.sum_mem _ fun ν _ =>
    Submodule.smul_mem _ _ (schurPoly_mem_symHomogeneousSubmodule ν)

/-- Every Schur polynomial of a partition of `n` with at most `m` parts is a linear
combination of the products `e_{ν'}`. -/
theorem schurPoly_mem_span_eProd (n : ℕ) {μ : List ℕ} (hμ : IsPart μ)
    (hsum : μ.sum = n) (hlen : μ.length ≤ m) :
    schurPoly (Fin m) R μ
      ∈ Submodule.span R (Set.range fun ν : PartIdx n m => eProd m R (conjPart ν.1)) := by
  classical
  set W := Submodule.span R (Set.range fun ν : PartIdx n m => eProd m R (conjPart ν.1))
    with hW
  suffices H : ∀ k : ℕ, ∀ ρ : List ℕ, IsPart ρ → ρ.sum = n → ρ.length ≤ m →
      domWeight n ρ ≤ k → schurPoly (Fin m) R ρ ∈ W by
    exact H _ μ hμ hsum hlen le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro ρ hρ hρsum hρlen hk
    have hconj : IsPart (conjPart ρ) := isPart_conjPart hρ
    have hcsum : (conjPart ρ).sum = n := by rw [sum_conjPart, hρsum]
    have hexp := eProd_eq_sum_partsFinset (R := R) m hconj
    rw [hcsum] at hexp
    have hmem : ρ ∈ partsFinset n m := mem_partsFinset.2 ⟨hρ, hρsum, hρlen⟩
    have hsplit := Finset.add_sum_erase (partsFinset n m)
      (fun ν => (kostka (conjPart ν) (conjPart ρ) : R) • schurPoly (Fin m) R ν) hmem
    simp only [kostka_self hconj, Nat.cast_one, one_smul] at hsplit
    have hrest : ∀ ν ∈ (partsFinset n m).erase ρ,
        (kostka (conjPart ν) (conjPart ρ) : R) • schurPoly (Fin m) R ν ∈ W := by
      intro ν hν
      have hνne : ν ≠ ρ := Finset.ne_of_mem_erase hν
      obtain ⟨hνpart, hνsum, hνlen⟩ := mem_partsFinset.1 (Finset.mem_of_mem_erase hν)
      by_cases hk0 : kostka (conjPart ν) (conjPart ρ) = 0
      · rw [hk0, Nat.cast_zero, zero_smul]
        exact Submodule.zero_mem _
      · have hdom : Partdom ν ρ :=
          partdom_of_kostka_conjPart_ne_zero hνpart hρ hνsum hρsum hk0
        have hlt : domWeight n ν < domWeight n ρ := by
          rcases lt_or_eq_of_le (domWeight_le_domWeight (n := n) hdom) with h | h
          · exact h
          · exact absurd (eq_of_partdom_of_domWeight_eq hνpart hρ hνsum hρsum hdom
              (le_of_eq h.symm)) hνne
        exact Submodule.smul_mem _ _
          (ih (domWeight n ν) (by omega) ν hνpart hνsum hνlen le_rfl)
    have hkey : schurPoly (Fin m) R ρ
        = eProd m R (conjPart ρ) - ∑ ν ∈ (partsFinset n m).erase ρ,
            (kostka (conjPart ν) (conjPart ρ) : R) • schurPoly (Fin m) R ν :=
      eq_sub_of_add_eq (hsplit.trans hexp.symm)
    rw [hkey]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨⟨ρ, hρ, hρsum, hρlen⟩, rfl⟩)
      (Submodule.sum_mem _ hrest)

/-- **The products `e_{μ'}` span** the module of symmetric homogeneous polynomials of
degree `n` in `m` variables. -/
theorem span_eProd (m n : ℕ) :
    Submodule.span R (Set.range fun μ : PartIdx n m => eProd m R (conjPart μ.1))
      = symHomogeneousSubmodule m n R := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro q ⟨μ, rfl⟩
    exact eProd_conj_mem_symHomogeneousSubmodule μ
  · rw [← span_schurPoly m n]
    refine Submodule.span_le.2 ?_
    rintro q ⟨ν, rfl⟩
    exact schurPoly_mem_span_eProd n ν.2.1 ν.2.2.1 ν.2.2.2

/-! ### The basis -/

/-- The product `e_{μ'}`, as an element of the module of symmetric homogeneous
polynomials of degree `n`. -/
noncomputable def eSub (m n : ℕ) (R : Type*) [CommRing R] (μ : PartIdx n m) :
    symHomogeneousSubmodule m n R :=
  ⟨eProd m R (conjPart μ.1), eProd_conj_mem_symHomogeneousSubmodule μ⟩

@[simp] lemma coe_eSub (m n : ℕ) (R : Type*) [CommRing R] (μ : PartIdx n m) :
    (eSub m n R μ : MvPolynomial (Fin m) R) = eProd m R (conjPart μ.1) := rfl

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

@[simp] lemma coe_eBasis (m n : ℕ) (R : Type*) [CommRing R] (μ : PartIdx n m) :
    (eBasis m n R μ : MvPolynomial (Fin m) R) = eProd m R (conjPart μ.1) := by
  rw [eBasis, Module.Basis.mk_apply, coe_eSub]

end MvPolynomial
