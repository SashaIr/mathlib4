/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.DualPieriSchur

/-!
# The basis of products of elementary symmetric polynomials

Following `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we study the products

`e_lam = e_{lam_1} * ... * e_{lam_k}`

of elementary symmetric polynomials.  Conjugation of partitions exchanges horizontal and vertical
strips, so the dual Pieri rule of
`Mathlib/RingTheory/MvPolynomial/Symmetric/Schur/DualPieriSchur.lean` becomes, for the family
`mu ↦ s_{mu'}`, an ordinary Pieri recursion; the general Kostka expansion of
`Mathlib/RingTheory/MvPolynomial/Symmetric/Basis/CompleteHomogeneous.lean` then gives

`e_lam = ∑_nu K_{nu' lam} s_nu`.

Since `K_{lam' lam'} = 1` and `K_{nu' lam'} ≠ 0` forces `nu ⊴ lam`, this expansion is
unitriangular for the dominance order, and the `e_{lam'}` for `lam` a partition of `n`
with at most `m` parts form a basis of the symmetric homogeneous polynomials of degree
`n` in `m` variables.

## Main definitions and results

* `MvPolynomial.eProd` : the product `e_lam`.
* `MvPolynomial.eProd_eq_sum_kostka` : the expansion `e_lam = ∑_nu K_{nu' lam} s_nu`.
* `MvPolynomial.eBasis` : the basis of products of elementary symmetric polynomials.
-/

open List

namespace MvPolynomial

open MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-- Reindexing a sum over the partitions of `n` by conjugation. -/
lemma sum_partFinset_conjPart {M : Type*} [AddCommMonoid M] (n : ℕ) (f : List ℕ → M) :
    ∑ mu ∈ partFinset n, f mu = ∑ nu ∈ partFinset n, f (conjPart nu) := by
  refine Finset.sum_nbij' (fun mu => conjPart mu) (fun nu => conjPart nu) ?_ ?_ ?_ ?_ ?_
  · intro mu hmu
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hmu
    exact mem_partFinset.2 ⟨isPart_conjPart hpart, by rw [sum_conjPart, hsum]⟩
  · intro nu hnu
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hnu
    exact mem_partFinset.2 ⟨isPart_conjPart hpart, by rw [sum_conjPart, hsum]⟩
  · intro mu hmu
    exact conjPart_conjPart (mem_partFinset.1 hmu).1
  · intro nu hnu
    exact conjPart_conjPart (mem_partFinset.1 hnu).1
  · intro mu hmu
    rw [conjPart_conjPart (mem_partFinset.1 hmu).1]

/-! ### The Pieri recursion satisfied by the conjugate Schur polynomials -/

/-- The dual Pieri rule, transported by conjugation: the family `mu ↦ s_{mu'}` satisfies
the Pieri recursion with the elementary symmetric polynomials as multipliers. -/
theorem schurPoly_conjPart_mul_esymm {mu : List ℕ} (hmu : IsPart mu) (r : ℕ) :
    schurPoly (Fin m) R (conjPart mu) * esymm (Fin m) R r
      = ∑ nu ∈ partFinset (mu.sum + r),
          if HorizStrip nu mu then schurPoly (Fin m) R (conjPart nu) else 0 := by
  classical
  rw [schurPoly_mul_esymm (isPart_conjPart hmu) r, sum_conjPart,
    sum_partFinset_conjPart (mu.sum + r)
      (fun lam => if VertStrip lam (conjPart mu) then schurPoly (Fin m) R lam else 0)]
  refine Finset.sum_congr rfl fun nu hnu => ?_
  have hnupart : IsPart nu := (mem_partFinset.1 hnu).1
  by_cases hstrip : HorizStrip nu mu
  · rw [ite_eq_left hstrip, ite_eq_left ((vertStrip_conjPart_iff hnupart hmu).2 hstrip)]
  · rw [ite_eq_right hstrip, ite_eq_right fun h => hstrip ((vertStrip_conjPart_iff hnupart hmu).1 h)]

/-! ### The products of elementary symmetric polynomials -/

/-- The product `e_lam = e_{lam_1} * ... * e_{lam_k}` of elementary symmetric polynomials
attached to a list `lam`. -/
noncomputable def eProd (m : ℕ) (R : Type*) [CommRing R] (lam : List ℕ) :
    MvPolynomial (Fin m) R := (lam.map (esymm (Fin m) R)).prod

@[simp] lemma eProd_nil (m : ℕ) (R : Type*) [CommRing R] : eProd m R [] = 1 := rfl

/-- **The expansion of `e_lam` in the Schur polynomials**, with the Kostka numbers of
`Combinatorics/Young/Tableau/Restrict.lean` as coefficients. -/
theorem eProd_eq_sum_kostkaNum (m : ℕ) (lam : List ℕ) :
    eProd m R lam
      = ∑ mu ∈ partFinset lam.sum,
          (kostkaNum lam.length mu (contentOf lam) : R) • schurPoly (Fin m) R (conjPart mu) := by
  have h := pieriProd_mul_eq_sum_kostkaNum (R := R) m (esymm (Fin m) R)
    (fun nu => schurPoly (Fin m) R (conjPart nu))
    (fun mu hmu r => schurPoly_conjPart_mul_esymm hmu r) lam
  rwa [conjPart_nil, schurPoly_nil, mul_one] at h

/-- **The expansion of `e_lam` in the Schur polynomials**: `e_lam = ∑_nu K_{nu' lam} s_nu`,
where `K_{nu' lam}` is the number of tableaux of shape the conjugate of `nu` and content
`lam`. -/
theorem eProd_eq_sum_kostka (m : ℕ) {lam : List ℕ} (hlam : IsPart lam) :
    eProd m R lam
      = ∑ nu ∈ partFinset lam.sum, (kostka (conjPart nu) lam : R) • schurPoly (Fin m) R nu := by
  rw [eProd_eq_sum_kostkaNum m lam, sum_partFinset_conjPart lam.sum
    (fun mu => (kostkaNum lam.length mu (contentOf lam) : R) • schurPoly (Fin m) R (conjPart mu))]
  refine Finset.sum_congr rfl fun nu hnu => ?_
  rw [kostkaNum_eq_kostka hlam (conjPart nu), conjPart_conjPart (mem_partFinset.1 hnu).1]

/-! ### The expansion restricted to the partitions with at most `m` parts -/

lemma partsFinset_subset_partFinset (n m : ℕ) : partsFinset n m ⊆ partFinset n := by
  intro l hl
  obtain ⟨hp, hs, -⟩ := mem_partsFinset.1 hl
  exact mem_partFinset.2 ⟨hp, hs⟩

/-- The expansion of `e_lam` in the Schur polynomials, restricted to the partitions with
at most `m` parts (the other Schur polynomials vanish). -/
theorem eProd_eq_sum_partsFinset (m : ℕ) {lam : List ℕ} (hlam : IsPart lam) :
    eProd m R lam
      = ∑ nu ∈ partsFinset lam.sum m,
          (kostka (conjPart nu) lam : R) • schurPoly (Fin m) R nu := by
  rw [eProd_eq_sum_kostka m hlam]
  refine (Finset.sum_subset (partsFinset_subset_partFinset _ _) fun nu hnu hnot => ?_).symm
  obtain ⟨hp, hs⟩ := mem_partFinset.1 hnu
  have hlen : m < nu.length := by
    by_contra h
    exact hnot (mem_partsFinset.2 ⟨hp, hs, by omega⟩)
  rw [schurPoly_eq_zero_of_lt_length hlen, smul_zero]

/-- The expansion of `e_{lam'}` in the Schur polynomials, indexed by `PartIdx n m`. -/
lemma eProd_conj_eq_sum_partIdx {n : ℕ} (lam : PartIdx n m) :
    eProd m R (conjPart lam.1)
      = ∑ nu : PartIdx n m,
          (kostka (conjPart nu.1) (conjPart lam.1) : R) • schurPoly (Fin m) R nu.1 := by
  classical
  have hconj : IsPart (conjPart lam.1) := isPart_conjPart lam.2.1
  have hsum : (conjPart lam.1).sum = n := by rw [sum_conjPart, lam.2.2.1]
  rw [eProd_eq_sum_partsFinset m hconj, hsum, partsFinset,
    Finset.sum_image fun x _ y _ h => Subtype.ext h]

/-- Unitriangularity of the expansion of `e_{mu'}`: a nonzero coefficient forces the
dominance `nu ⊴ mu`. -/
lemma partdom_of_kostka_conjPart_ne_zero {n : ℕ} {nu mu : List ℕ} (hnu : IsPart nu)
    (hmu : IsPart mu) (hnusum : nu.sum = n) (hmusum : mu.sum = n)
    (h : kostka (conjPart nu) (conjPart mu) ≠ 0) : Partdom nu mu :=
  (partdom_conjPart_iff hnu hmu (by rw [hnusum, hmusum])).1 (partdom_of_kostka_ne_zero h)

/-! ### Linear independence -/

/-- **The products `e_{lam'}` are linearly independent**: over any commutative ring, the
polynomials `e_{lam'}` for `lam` a partition of `n` with at most `m` parts (equivalently,
the `e_mu` for `mu` a partition of `n` with all parts at most `m`) are linearly
independent. -/
theorem linearIndependent_eProd (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R fun lam : PartIdx n m => eProd m R (conjPart lam.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg lam
  have hexp : ∑ mu : PartIdx n m, g mu • eProd m R (conjPart mu.1)
      = ∑ nu : PartIdx n m,
          (∑ mu : PartIdx n m, g mu * (kostka (conjPart nu.1) (conjPart mu.1) : R))
            • schurPoly (Fin m) R nu.1 := by
    simp only [eProd_conj_eq_sum_partIdx, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have hcoef : ∀ nu : PartIdx n m,
      ∑ mu : PartIdx n m, g mu * (kostka (conjPart nu.1) (conjPart mu.1) : R) = 0 :=
    Fintype.linearIndependent_iff.1 (linearIndependent_schurPoly m n R) _ (by rw [← hexp, hg])
  by_contra hne
  obtain ⟨nu, hnut, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun mu : PartIdx n m => g mu ≠ 0) (fun mu => domWeight n mu.1)
    ⟨lam, Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩⟩
  obtain ⟨-, hnu0⟩ := Finset.mem_filter.1 hnut
  have hsingle : ∀ mu ∈ (Finset.univ : Finset (PartIdx n m)), mu ≠ nu →
      g mu * (kostka (conjPart nu.1) (conjPart mu.1) : R) = 0 := by
    intro mu _ hmune
    by_cases hgmu : g mu = 0
    · rw [hgmu, zero_mul]
    · have hmut : mu ∈ Finset.univ.filter fun mu : PartIdx n m => g mu ≠ 0 :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hgmu⟩
      have hzero : kostka (conjPart nu.1) (conjPart mu.1) = 0 := by
        by_contra hk
        have hdom : Partdom nu.1 mu.1 :=
          partdom_of_kostka_conjPart_ne_zero nu.2.1 mu.2.1 nu.2.2.1 mu.2.2.1 hk
        exact hmune (Subtype.ext (eq_of_partdom_of_domWeight_eq nu.2.1 mu.2.1 nu.2.2.1
          mu.2.2.1 hdom (hmax mu hmut)).symm)
      rw [hzero, Nat.cast_zero, mul_zero]
  have hzero := hcoef nu
  rw [Finset.sum_eq_single nu hsingle (fun h => absurd (Finset.mem_univ nu) h),
    kostka_self (isPart_conjPart nu.2.1), Nat.cast_one, mul_one] at hzero
  exact hnu0 hzero

/-! ### Spanning -/

lemma eProd_conj_mem_symHomogeneousSubmodule {n : ℕ} (lam : PartIdx n m) :
    eProd m R (conjPart lam.1) ∈ symHomogeneousSubmodule m n R := by
  rw [eProd_conj_eq_sum_partIdx lam]
  exact Submodule.sum_mem _ fun nu _ =>
    Submodule.smul_mem _ _ (schurPoly_mem_symHomogeneousSubmodule nu)

/-- Every Schur polynomial of a partition of `n` with at most `m` parts is a linear
combination of the products `e_{mu'}`. -/
theorem schurPoly_mem_span_eProd (n : ℕ) {lam : List ℕ} (hlam : IsPart lam)
    (hsum : lam.sum = n) (hlen : lam.length ≤ m) :
    schurPoly (Fin m) R lam
      ∈ Submodule.span R (Set.range fun mu : PartIdx n m => eProd m R (conjPart mu.1)) := by
  classical
  set W := Submodule.span R (Set.range fun mu : PartIdx n m => eProd m R (conjPart mu.1))
    with hW
  suffices H : ∀ k : ℕ, ∀ nu : List ℕ, IsPart nu → nu.sum = n → nu.length ≤ m →
      domWeight n nu ≤ k → schurPoly (Fin m) R nu ∈ W by
    exact H _ lam hlam hsum hlen le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro nu hnu hnusum hnulen hk
    have hconj : IsPart (conjPart nu) := isPart_conjPart hnu
    have hcsum : (conjPart nu).sum = n := by rw [sum_conjPart, hnusum]
    have hexp := eProd_eq_sum_partsFinset (R := R) m hconj
    rw [hcsum] at hexp
    have hmem : nu ∈ partsFinset n m := mem_partsFinset.2 ⟨hnu, hnusum, hnulen⟩
    have hsplit := Finset.add_sum_erase (partsFinset n m)
      (fun mu => (kostka (conjPart mu) (conjPart nu) : R) • schurPoly (Fin m) R mu) hmem
    simp only [kostka_self hconj, Nat.cast_one, one_smul] at hsplit
    have hrest : ∀ mu ∈ (partsFinset n m).erase nu,
        (kostka (conjPart mu) (conjPart nu) : R) • schurPoly (Fin m) R mu ∈ W := by
      intro mu hmu
      have hmune : mu ≠ nu := Finset.ne_of_mem_erase hmu
      obtain ⟨hmupart, hmusum, hmulen⟩ := mem_partsFinset.1 (Finset.mem_of_mem_erase hmu)
      by_cases hk0 : kostka (conjPart mu) (conjPart nu) = 0
      · rw [hk0, Nat.cast_zero, zero_smul]
        exact Submodule.zero_mem _
      · have hdom : Partdom mu nu :=
          partdom_of_kostka_conjPart_ne_zero hmupart hnu hmusum hnusum hk0
        have hlt : domWeight n mu < domWeight n nu := by
          rcases lt_or_eq_of_le (domWeight_le_domWeight (n := n) hdom) with h | h
          · exact h
          · exact absurd (eq_of_partdom_of_domWeight_eq hmupart hnu hmusum hnusum hdom
              (le_of_eq h.symm)) hmune
        exact Submodule.smul_mem _ _
          (ih (domWeight n mu) (by omega) mu hmupart hmusum hmulen le_rfl)
    have hkey : schurPoly (Fin m) R nu
        = eProd m R (conjPart nu) - ∑ mu ∈ (partsFinset n m).erase nu,
            (kostka (conjPart mu) (conjPart nu) : R) • schurPoly (Fin m) R mu :=
      eq_sub_of_add_eq (hsplit.trans hexp.symm)
    rw [hkey]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨⟨nu, hnu, hnusum, hnulen⟩, rfl⟩)
      (Submodule.sum_mem _ hrest)

/-- **The products `e_{lam'}` span** the module of symmetric homogeneous polynomials of
degree `n` in `m` variables. -/
theorem span_eProd (m n : ℕ) :
    Submodule.span R (Set.range fun lam : PartIdx n m => eProd m R (conjPart lam.1))
      = symHomogeneousSubmodule m n R := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro q ⟨lam, rfl⟩
    exact eProd_conj_mem_symHomogeneousSubmodule lam
  · rw [← span_schurPoly m n]
    refine Submodule.span_le.2 ?_
    rintro q ⟨nu, rfl⟩
    exact schurPoly_mem_span_eProd n nu.2.1 nu.2.2.1 nu.2.2.2

/-! ### The basis -/

/-- The product `e_{lam'}`, as an element of the module of symmetric homogeneous
polynomials of degree `n`. -/
noncomputable def eSub (m n : ℕ) (R : Type*) [CommRing R] (lam : PartIdx n m) :
    symHomogeneousSubmodule m n R :=
  ⟨eProd m R (conjPart lam.1), eProd_conj_mem_symHomogeneousSubmodule lam⟩

@[simp] lemma coe_eSub (m n : ℕ) (R : Type*) [CommRing R] (lam : PartIdx n m) :
    (eSub m n R lam : MvPolynomial (Fin m) R) = eProd m R (conjPart lam.1) := rfl

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

@[simp] lemma coe_eBasis (m n : ℕ) (R : Type*) [CommRing R] (lam : PartIdx n m) :
    (eBasis m n R lam : MvPolynomial (Fin m) R) = eProd m R (conjPart lam.1) := by
  rw [eBasis, Module.Basis.mk_apply, coe_eSub]

end MvPolynomial
