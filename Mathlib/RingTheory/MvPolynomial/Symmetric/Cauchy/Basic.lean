/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.CompleteHomogeneous

/-!
# The Cauchy identity

Following `theories/MPoly/Cauchy.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove the Cauchy identity in its
polynomial (degree by degree) form:

`∑_{lam ⊢ n} s_lam(x) * s_lam(y) = ∑_{a} h_{a_1}(x) ⋯ h_{a_k}(x) * y_1^{a_1} ⋯ y_k^{a_k}`,

the sum on the right being over the families `a : Fin k → ℕ` of total size `n`.  This is
the coefficient of degree `n` in `y` of the usual generating-function form
`∏_{i,j} 1 / (1 - x_i y_j) = ∑_lam s_lam(x) s_lam(y)`, since
`∏_i 1 / (1 - x_i t) = ∑_r h_r(x) t^r`.

The proof is by induction on the number `k` of variables `y`, exactly as for the dual Cauchy
identity of `Mathlib/RingTheory/MvPolynomial/Symmetric/Cauchy/Dual.lean`: splitting off the
last variable `y_k`, the right-hand side gets multiplied by `h_r(x) y_k^r`, and on the left the
branching rule `MvPolynomial.schurPoly_branching'` removes a horizontal strip from `lam`, which the
Pieri rule `MvPolynomial.schurPoly_mul_hsymm` puts back on the `x` side.

## Main results

* `MvPolynomial.sum_antidiagonalTuple_succ` : splitting off the last entry of a family of total
  size `n`.
* `MvPolynomial.cauchy` : the Cauchy identity.
-/

namespace MvPolynomial

open List MvPolynomial

/-! ### Splitting off the last variable -/

/-- Splitting off the last entry of a family of naturals of total size `n`. -/
lemma sum_antidiagonalTuple_succ {M : Type*} [AddCommMonoid M] (k n : ℕ)
    (f : (Fin (k + 1) → ℕ) → M) :
    ∑ a ∈ Finset.Nat.antidiagonalTuple (k + 1) n, f a
      = ∑ r ∈ Finset.range (n + 1),
          ∑ b ∈ Finset.Nat.antidiagonalTuple k (n - r), f (Fin.snoc b r) := by
  classical
  rw [Finset.sum_sigma' (Finset.range (n + 1))
    (fun r => Finset.Nat.antidiagonalTuple k (n - r)) (fun r b => f (Fin.snoc b r))]
  symm
  refine Finset.sum_nbij'
    (fun x : (_ : ℕ) × (Fin k → ℕ) => Fin.snoc x.2 x.1)
    (fun a : Fin (k + 1) → ℕ => ⟨a (Fin.last k), Fin.init a⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨r, b⟩ hx
    rw [Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple] at hx
    dsimp only at hx ⊢
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    omega
  · intro a ha
    rw [Finset.Nat.mem_antidiagonalTuple] at ha
    rw [Fin.sum_univ_castSucc] at ha
    have hinit : ∑ j : Fin k, Fin.init a j = n - a (Fin.last k) := by
      have hi : ∑ j : Fin k, Fin.init a j = ∑ j : Fin k, a (Fin.castSucc j) := rfl
      omega
    refine Finset.mem_sigma.2 ⟨Finset.mem_range.2 ?_, ?_⟩
    · change a (Fin.last k) < n + 1
      omega
    · change Fin.init a ∈ Finset.Nat.antidiagonalTuple k (n - a (Fin.last k))
      exact Finset.Nat.mem_antidiagonalTuple.2 hinit
  · rintro ⟨r, b⟩ _
    simp [Fin.init_snoc]
  · intro a _
    exact Fin.snoc_init_self a
  · rintro ⟨r, b⟩ _
    rfl

/-! ### The two sides of the induction -/

/-- The left-hand side of the Cauchy identity in `k` variables `y`. -/
noncomputable def cauchyLHS (m k n : ℕ) (R : Type*) [CommRing R] :
    MvPolynomial (Fin k) (MvPolynomial (Fin m) R) :=
  ∑ lam ∈ partFinset n,
    C (schurPoly (Fin m) R lam) * schurPoly (Fin k) (MvPolynomial (Fin m) R) lam

/-- The right-hand side of the Cauchy identity in `k` variables `y`. -/
noncomputable def cauchyRHS (m k n : ℕ) (R : Type*) [CommRing R] :
    MvPolynomial (Fin k) (MvPolynomial (Fin m) R) :=
  ∑ a ∈ Finset.Nat.antidiagonalTuple k n,
    C (∏ j : Fin k, hsymm (Fin m) R (a j)) * ∏ j : Fin k, X j ^ a j

/-- The recursion satisfied by the right-hand side of the Cauchy identity. -/
lemma cauchyRHS_succ (m k n : ℕ) (R : Type*) [CommRing R] :
    cauchyRHS m (k + 1) n R
      = ∑ r ∈ Finset.range (n + 1),
          C (hsymm (Fin m) R r) * X (Fin.last k) ^ r
            * rename Fin.castSucc (cauchyRHS m k (n - r) R) := by
  classical
  rw [cauchyRHS, sum_antidiagonalTuple_succ]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [cauchyRHS, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∏ i : Fin (k + 1), hsymm (Fin m) R ((Fin.snoc b r : Fin (k + 1) → ℕ) i)
      = (∏ j : Fin k, hsymm (Fin m) R (b j)) * hsymm (Fin m) R r := by
    rw [Fin.prod_univ_castSucc]
    simp
  have h2 : (∏ i : Fin (k + 1),
        (X i : MvPolynomial (Fin (k + 1)) (MvPolynomial (Fin m) R))
          ^ (Fin.snoc b r : Fin (k + 1) → ℕ) i)
      = (∏ j : Fin k, X (Fin.castSucc j) ^ b j) * X (Fin.last k) ^ r := by
    rw [Fin.prod_univ_castSucc]
    simp
  have h3 : rename Fin.castSucc
        (C (∏ j : Fin k, hsymm (Fin m) R (b j)) * ∏ j : Fin k, X j ^ b j)
      = (C (∏ j : Fin k, hsymm (Fin m) R (b j))
          * ∏ j : Fin k, X (Fin.castSucc j) ^ b j
          : MvPolynomial (Fin (k + 1)) (MvPolynomial (Fin m) R)) := by
    simp only [map_mul, rename_C, map_prod, map_pow, rename_X]
  rw [h1, h2, h3, map_mul]
  ring

/-- The recursion satisfied by the left-hand side of the Cauchy identity: the branching
rule on the `y` side and the Pieri rule on the `x` side. -/
lemma cauchyLHS_succ (m k n : ℕ) (R : Type*) [CommRing R] :
    cauchyLHS m (k + 1) n R
      = ∑ r ∈ Finset.range (n + 1),
          C (hsymm (Fin m) R r) * X (Fin.last k) ^ r
            * rename Fin.castSucc (cauchyLHS m k (n - r) R) := by
  classical
  have hbranch : cauchyLHS m (k + 1) n R
      = ∑ lam ∈ partFinset n, ∑ mu ∈ partFinsetLe n,
          if HorizStrip lam mu then
            C (schurPoly (Fin m) R lam)
              * (rename Fin.castSucc (schurPoly (Fin k) (MvPolynomial (Fin m) R) mu)
                * X (Fin.last k) ^ (n - mu.sum))
          else 0 := by
    refine Finset.sum_congr rfl fun lam hlam => ?_
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hlam
    rw [schurPoly_branching' k hpart, hsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun mu _ => by split_ifs <;> simp
  rw [hbranch, Finset.sum_comm, sum_partFinsetLe_eq]
  -- the outer sum is now over the size `p` of `mu`; reindex it by `r = n - p`
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [cauchyLHS, map_sum, Finset.mul_sum]
  -- collect the Pieri sum
  have hpieri : ∀ mu ∈ partFinset (n - r),
      (∑ lam ∈ partFinset n,
        if HorizStrip lam mu then
          C (schurPoly (Fin m) R lam)
            * (rename Fin.castSucc (schurPoly (Fin k) (MvPolynomial (Fin m) R) mu)
              * X (Fin.last k) ^ (n - mu.sum))
        else 0)
      = C (hsymm (Fin m) R r) * X (Fin.last k) ^ r
          * rename Fin.castSucc
              (C (schurPoly (Fin m) R mu) * schurPoly (Fin k) (MvPolynomial (Fin m) R) mu) := by
    intro mu hmu
    obtain ⟨hmupart, hmusum⟩ := mem_partFinset.1 hmu
    have hsum : mu.sum + r = n := by omega
    have hpieri' : (∑ lam ∈ partFinset n,
        if HorizStrip lam mu then schurPoly (Fin m) R lam else 0)
        = schurPoly (Fin m) R mu * hsymm (Fin m) R r := by
      rw [schurPoly_mul_hsymm m hmupart r, hsum]
    have hsplit : (∑ lam ∈ partFinset n,
        if HorizStrip lam mu then
          C (schurPoly (Fin m) R lam)
            * (rename Fin.castSucc (schurPoly (Fin k) (MvPolynomial (Fin m) R) mu)
              * X (Fin.last k) ^ (n - mu.sum))
        else 0)
        = (∑ lam ∈ partFinset n, if HorizStrip lam mu then C (schurPoly (Fin m) R lam) else 0)
            * (rename Fin.castSucc (schurPoly (Fin k) (MvPolynomial (Fin m) R) mu)
              * X (Fin.last k) ^ (n - mu.sum)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun lam _ => by split_ifs <;> simp
    have hC : (∑ lam ∈ partFinset n, if HorizStrip lam mu then C (schurPoly (Fin m) R lam) else 0
          : MvPolynomial (Fin (k + 1)) (MvPolynomial (Fin m) R))
        = C (schurPoly (Fin m) R mu * hsymm (Fin m) R r) := by
      rw [← hpieri', map_sum]
      exact Finset.sum_congr rfl fun lam _ => by split_ifs <;> simp
    rw [hsplit, hC, show n - mu.sum = r by omega, map_mul, map_mul, rename_C]
    ring
  exact Finset.sum_congr rfl hpieri

/-- **The Cauchy identity**, degree by degree: the sum over the partitions of `n` of the
products `s_lam(x) s_lam(y)` is the sum over the families `a` of total size `n` of
`h_{a_1}(x) ⋯ h_{a_k}(x) y^a`. -/
theorem cauchy (m k n : ℕ) (R : Type*) [CommRing R] :
    (∑ lam ∈ partFinset n,
        C (schurPoly (Fin m) R lam) * schurPoly (Fin k) (MvPolynomial (Fin m) R) lam
      : MvPolynomial (Fin k) (MvPolynomial (Fin m) R))
      = ∑ a ∈ Finset.Nat.antidiagonalTuple k n,
          C (∏ j : Fin k, hsymm (Fin m) R (a j)) * ∏ j : Fin k, X j ^ a j := by
  change cauchyLHS m k n R = cauchyRHS m k n R
  induction k generalizing n with
  | zero =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [cauchyLHS, cauchyRHS, partFinset_zero, Finset.Nat.antidiagonalTuple_zero_zero]
        simp [schurPoly_nil]
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        rw [cauchyLHS, cauchyRHS, Finset.Nat.antidiagonalTuple_zero_succ, Finset.sum_empty]
        refine Finset.sum_eq_zero fun lam hlam => ?_
        obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hlam
        have hne : lam ≠ [] := by
          rintro rfl
          simp at hsum
        rw [schurPoly_eq_zero_of_lt_length (List.length_pos_iff.2 hne), mul_zero]
  | succ k IH =>
      rw [cauchyLHS_succ, cauchyRHS_succ]
      exact Finset.sum_congr rfl fun r _ => by rw [IH]

/-! ### The Cauchy identity in terms of the dual bases `h` and `m` -/

/-- A monomial as a product of powers of all the variables. -/
lemma prod_X_pow_eq_monomial_finsupp {k : ℕ} {A : Type*} [CommSemiring A] (d : Fin k →₀ ℕ) :
    (∏ j : Fin k, (X j : MvPolynomial (Fin k) A) ^ d j) = monomial d 1 := by
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  refine (Finset.prod_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
  rw [Finsupp.notMem_support_iff.1 hj, pow_zero]

/-- Trailing zero parts do not change a product of complete homogeneous symmetric
polynomials. -/
lemma prod_map_hsymm_trimZeros (m : ℕ) (R : Type*) [CommRing R] (l : List ℕ) :
    (l.map (hsymm (Fin m) R)).prod = hProd m R (trimZeros l) := by
  conv_lhs => rw [← trimZeros_append l]
  rw [List.map_append, List.prod_append, hProd]
  have hone : ((l.rtakeWhile (fun y => y == 0)).map (hsymm (Fin m) R)).prod = 1 := by
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    rw [mem_rtakeWhile_zero hy, hsymm_zero]
  rw [hone, mul_one]

/-- The product of the complete homogeneous symmetric polynomials attached to the exponents
of a monomial only depends on the shape of the monomial. -/
lemma prod_hsymm_eq_hProd (m k : ℕ) (R : Type*) [CommRing R] (d : Fin k →₀ ℕ) :
    (∏ j : Fin k, hsymm (Fin m) R (d j)) = hProd m R (degShape d) := by
  have h1 : (∏ j : Fin k, hsymm (Fin m) R (d j))
      = (Multiset.map (hsymm (Fin m) R) (degMultiset d)).prod := by
    rw [Finset.prod_eq_multiset_prod, degMultiset, Multiset.map_map]
    rfl
  rw [h1, ← coe_degSorted d, Multiset.map_coe, Multiset.prod_coe, degShape]
  exact prod_map_hsymm_trimZeros m R (degSorted d)

/-- **The Cauchy identity in the dual bases form**: `∑_lam s_lam(x) s_lam(y)` is
`∑_mu h_mu(x) m_mu(y)`, the sum being over the partitions `mu` of `n` with at most `k`
parts. -/
theorem cauchy_hProd_monomialSym (m k n : ℕ) (R : Type*) [CommRing R] :
    (∑ lam ∈ partFinset n,
        C (schurPoly (Fin m) R lam) * schurPoly (Fin k) (MvPolynomial (Fin m) R) lam
      : MvPolynomial (Fin k) (MvPolynomial (Fin m) R))
      = ∑ mu : PartIdx n k, C (hProd m R mu.1) * monomialSym k (MvPolynomial (Fin m) R) mu.1 := by
  classical
  rw [cauchy]
  ext d
  have hL : coeff d (∑ a ∈ Finset.Nat.antidiagonalTuple k n,
        C (∏ j : Fin k, hsymm (Fin m) R (a j))
          * ∏ j : Fin k, (X j : MvPolynomial (Fin k) (MvPolynomial (Fin m) R)) ^ a j)
      = if ∑ j, d j = n then hProd m R (degShape d) else 0 := by
    rw [coeff_sum]
    have hterm : ∀ a ∈ Finset.Nat.antidiagonalTuple k n,
        coeff d (C (∏ j : Fin k, hsymm (Fin m) R (a j))
            * ∏ j : Fin k, (X j : MvPolynomial (Fin k) (MvPolynomial (Fin m) R)) ^ a j)
          = if a = (d : Fin k → ℕ) then hProd m R (degShape d) else 0 := by
      intro a _
      have hmon : (∏ j : Fin k, (X j : MvPolynomial (Fin k) (MvPolynomial (Fin m) R)) ^ a j)
          = monomial (Finsupp.equivFunOnFinite.symm a) 1 :=
        prod_X_pow_eq_monomial_finsupp (Finsupp.equivFunOnFinite.symm a)
      rw [hmon, C_mul_monomial, mul_one, coeff_monomial]
      by_cases h : a = (d : Fin k → ℕ)
      · subst h
        rw [if_pos rfl, if_pos (Finsupp.equivFunOnFinite_symm_coe d)]
        rw [← prod_hsymm_eq_hProd m k R d]
      · rw [if_neg h, if_neg]
        intro hc
        exact h (by rw [← hc]; rfl)
    rw [Finset.sum_congr rfl hterm,
      Finset.sum_ite_eq' (Finset.Nat.antidiagonalTuple k n) (d : Fin k → ℕ)
        (fun _ => hProd m R (degShape d))]
    simp only [Finset.Nat.mem_antidiagonalTuple]
  have hR : coeff d (∑ mu : PartIdx n k,
        C (hProd m R mu.1) * monomialSym k (MvPolynomial (Fin m) R) mu.1)
      = if ∑ j, d j = n then hProd m R (degShape d) else 0 := by
    rw [coeff_sum]
    have hterm : ∀ mu : PartIdx n k,
        coeff d (C (hProd m R mu.1) * monomialSym k (MvPolynomial (Fin m) R) mu.1)
          = if mu.1 = degShape d then hProd m R (degShape d) else 0 := by
      intro mu
      rw [coeff_C_mul, coeff_monomialSym]
      have hiff : d ∈ degOrbit (shapeContent k mu.1) ↔ mu.1 = degShape d := by
        rw [mem_degOrbit_iff]
        constructor
        · intro h
          have h2 := degShape_eq_iff.2 h
          rw [degShape_shapeContent mu.2.1 mu.2.2.2] at h2
          exact h2.symm
        · intro h
          refine degShape_eq_iff.1 ?_
          rw [degShape_shapeContent mu.2.1 mu.2.2.2, h]
      by_cases h : mu.1 = degShape d
      · rw [if_pos (hiff.2 h), if_pos h, mul_one, h]
      · rw [if_neg (fun hc => h (hiff.1 hc)), if_neg h, mul_zero]
    rw [Finset.sum_congr rfl (fun mu _ => hterm mu)]
    by_cases hn : ∑ j, d j = n
    · have hmu0 : IsPart (degShape d) ∧ (degShape d).sum = n ∧ (degShape d).length ≤ k :=
        ⟨isPart_degShape d, by rw [sum_degShape]; exact hn, length_degShape_le d⟩
      rw [if_pos hn, Finset.sum_eq_single (⟨degShape d, hmu0⟩ : PartIdx n k)]
      · rw [if_pos rfl]
      · intro mu _ hne
        exact if_neg fun hc => hne (Subtype.ext hc)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [if_neg hn]
      refine Finset.sum_eq_zero fun mu _ => if_neg fun hc => hn ?_
      rw [← sum_degShape d, ← hc, mu.2.2.1]
  rw [hL, hR]

end MvPolynomial
