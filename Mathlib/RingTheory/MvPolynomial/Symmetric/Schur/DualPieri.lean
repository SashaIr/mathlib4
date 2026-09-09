/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Shape.VerticalStrip
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Alternant.Bialternant
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.ElementaryHomogeneous

/-!
# The dual Pieri rule

Following `theories/MPoly/Schur_altdef.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove the dual Pieri rule:

`s_mu * e_r = ∑_{lam / mu a vertical strip of size r} s_lam`.

The proof is the alternant one: multiplying an alternant by `e_r` adds all the `0-1`
exponent vectors of weight `r`, and the terms which do not correspond to a partition have
two equal exponents, hence vanish.

## Main definitions and results

* `MvPolynomial.zeroOneAntidiag m r` : the `0-1` exponent vectors of weight `r`.
* `MvPolynomial.esymm_mul_alt` : `e_r * a_a = ∑_{d 0-1, |d| = r} a_{a+d}`.
* `MvPolynomial.schurPoly_mul_esymm` : the dual Pieri rule.
-/

@[expose] public section

open List

namespace MvPolynomial

open MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### The `0-1` exponent vectors -/

/-- The `0-1` exponent vectors of weight `r` in `m` variables. -/
noncomputable def zeroOneAntidiag (m r : ℕ) : Finset (Fin m →₀ ℕ) :=
  (Finset.finsuppAntidiag (univ : Finset (Fin m)) r).filter (fun d => ∀ i, d i ≤ 1)

lemma mem_zeroOneAntidiag {m r : ℕ} {d : Fin m →₀ ℕ} :
    d ∈ zeroOneAntidiag m r ↔ (∑ i, d i) = r ∧ ∀ i, d i ≤ 1 := by
  rw [zeroOneAntidiag, Finset.mem_filter, Finset.mem_finsuppAntidiag]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by simp⟩, h.2⟩⟩

/-- The elementary symmetric polynomial is the sum of the squarefree monomials. -/
lemma esymm_eq_sum_zeroOneAntidiag (m r : ℕ) (R : Type*) [CommRing R] :
    esymm (Fin m) R r = ∑ d ∈ zeroOneAntidiag m r, monomial d (1 : R) := by
  classical
  rw [esymm_eq_sum_indicVec]
  refine Finset.sum_nbij' (fun S => indicVec S) (fun d => d.support) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    obtain ⟨-, hcard⟩ := Finset.mem_powersetCard.1 hS
    exact mem_zeroOneAntidiag.2 ⟨by rw [sum_indicVec, hcard], fun i => by
      rw [indicVec_apply]; split_ifs <;> omega⟩
  · intro d hd
    obtain ⟨hsum, hone⟩ := mem_zeroOneAntidiag.1 hd
    refine Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, ?_⟩
    have hsupp : ∑ i ∈ d.support, d i = ∑ i, d i :=
      Finset.sum_subset (Finset.subset_univ _) (fun i _ h => Finsupp.notMem_support_iff.1 h)
    have hone' : ∀ i ∈ d.support, d i = 1 := fun i hi => by
      have h1 := hone i
      have h2 := Finsupp.mem_support_iff.1 hi
      omega
    rw [Finset.sum_congr rfl hone', Finset.sum_const, smul_eq_mul, mul_one] at hsupp
    omega
  · intro S hS
    ext i
    simp [Finsupp.mem_support_iff]
  · intro d hd
    obtain ⟨-, hone⟩ := mem_zeroOneAntidiag.1 hd
    refine Finsupp.ext fun i => ?_
    rw [indicVec_apply]
    by_cases h : i ∈ d.support
    · have h1 := hone i
      have h2 := Finsupp.mem_support_iff.1 h
      rw [ite_eq_left h]
      omega
    · rw [ite_eq_right h]
      exact (Finsupp.notMem_support_iff.1 h).symm
  · intro S _
    rfl

/-! ### Multiplying an alternant by an elementary symmetric polynomial -/

/-- Multiplying a single monomial of an alternant by `e_r`. -/
lemma esymm_mul_prod (r : ℕ) (w : Equiv.Perm (Fin m)) (a : Fin m → ℕ) :
    esymm (Fin m) R r * ∏ i, X (R := R) (w i) ^ a i
      = ∑ e ∈ zeroOneAntidiag m r, ∏ i, X (R := R) (w i) ^ (a i + e i) := by
  rw [esymm_eq_sum_zeroOneAntidiag, Finset.sum_mul]
  refine Finset.sum_nbij' (i := fun d => Finsupp.equivMapDomain w.symm d)
    (j := fun e => Finsupp.equivMapDomain w e) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    obtain ⟨hsum, hone⟩ := mem_zeroOneAntidiag.1 hd
    refine mem_zeroOneAntidiag.2 ⟨?_, fun i => by simpa using hone (w i)⟩
    rw [← hsum]
    exact Fintype.sum_equiv w _ _ (fun i => by simp)
  · intro e he
    obtain ⟨hsum, hone⟩ := mem_zeroOneAntidiag.1 he
    refine mem_zeroOneAntidiag.2 ⟨?_, fun i => by simpa using hone (w.symm i)⟩
    rw [← hsum]
    exact Fintype.sum_equiv w.symm _ _ (fun i => by simp)
  · intro d _
    ext i
    simp
  · intro e _
    ext i
    simp
  · intro d _
    have h1 : (monomial d (1 : R)) = ∏ i, X (R := R) (w i) ^ d (w i) := by
      rw [Equiv.prod_comp w (fun j => X (R := R) j ^ d j), monomial_eq]
      simp [Finsupp.prod, ← Finsupp.prod_pow]
    rw [h1, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add, Nat.add_comm]
    simp

/-- Multiplying an alternant by the elementary symmetric polynomial `e_r` adds all the
`0-1` exponent vectors of weight `r`. -/
theorem esymm_mul_alt (r : ℕ) (a : Fin m → ℕ) :
    esymm (Fin m) R r * alt m R a
      = ∑ d ∈ zeroOneAntidiag m r, alt m R (a + ⇑d) := by
  rw [alt, Finset.mul_sum]
  have hterm : ∀ w : Equiv.Perm (Fin m),
      esymm (Fin m) R r * ((Equiv.Perm.sign w : ℤ) • ∏ i, X (R := R) (w i) ^ a i)
        = ∑ d ∈ zeroOneAntidiag m r,
            (Equiv.Perm.sign w : ℤ) • ∏ i, X (R := R) (w i) ^ ((a + ⇑d) i) := by
    intro w
    rw [mul_smul_comm, esymm_mul_prod, Finset.smul_sum]
    rfl
  simp only [hterm]
  rw [Finset.sum_comm]
  rfl

/-! ### The dual Pieri rule for alternants -/

/-- If an exponent vector obtained by adding a `0-1` vector to a staircase-shifted
partition is not strictly decreasing, then it has two equal entries, and its alternant
vanishes. -/
lemma alt_eq_zero_of_not_strict {mu : List ℕ} (hmu : IsPart mu) {d : Fin m →₀ ℕ}
    (hone : ∀ i, d i ≤ 1) {i j : Fin m} (hij : (j : ℕ) = (i : ℕ) + 1)
    (hnot : ¬ (partVec m mu + ⇑d) j < (partVec m mu + ⇑d) i) :
    alt m R (partVec m mu + ⇑d) = 0 := by
  have hjm : (j : ℕ) < m := j.isLt
  have hmuji : mu.getD (j : ℕ) 0 ≤ mu.getD (i : ℕ) 0 := hmu.getD_antitone (by omega)
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  refine alt_eq_zero_of_eq hne ?_
  have h1 := hone i
  have h2 := hone j
  simp only [Pi.add_apply, partVec_apply] at hnot ⊢
  omega

/-- A strictly decreasing exponent vector above the staircase is the staircase shift of a
partition. -/
lemma isPart_vecPart_of_strict {c : Fin m → ℕ} (hge : ∀ i : Fin m, m - 1 - (i : ℕ) ≤ c i)
    (hs : ∀ i j : Fin m, (j : ℕ) = (i : ℕ) + 1 → c j < c i) : IsPart (vecPart m c) := by
  rw [vecPart]
  refine isPart_shapeOfFn fun i => ?_
  by_cases hi : i + 1 < m
  · have hi' : i < m := by omega
    have h1 := hs ⟨i, hi'⟩ ⟨i + 1, hi⟩ rfl
    have h2 := hge ⟨i, hi'⟩
    have h3 := hge ⟨i + 1, hi⟩
    simp only at h1 h2 h3
    rw [dite_eq_left hi, dite_eq_left hi']
    omega
  · simp [dite_eq_right hi]

/-- **The dual Pieri rule for alternants**, in terms of partitions. -/
theorem altPart_mul_esymm {mu : List ℕ} (hmu : IsPart mu) (r : ℕ) :
    altPart m R mu * esymm (Fin m) R r
      = ∑ lam ∈ partFinset (mu.sum + r), if VertStrip lam mu then altPart m R lam else 0 := by
  classical
  by_cases hmulen : mu.length ≤ m
  swap
  · rw [altPart_of_lt (by omega), zero_mul]
    refine (Finset.sum_eq_zero fun lam _ => ?_).symm
    split_ifs with hstrip
    · exact altPart_of_lt (lt_of_lt_of_le (by omega) hstrip.1.length_le)
    · rfl
  rw [altPart_of_le hmulen, mul_comm, esymm_mul_alt, ← Finset.sum_filter]
  -- discard the shapes with more than `m` rows
  have hsub : ∑ lam ∈ ((partFinset (mu.sum + r)).filter fun lam => VertStrip lam mu).filter
        (fun lam => lam.length ≤ m), altPart m R lam
      = ∑ lam ∈ (partFinset (mu.sum + r)).filter fun lam => VertStrip lam mu,
          altPart m R lam := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun lam hlam hnot => ?_
    exact altPart_of_lt (by
      by_contra hle
      exact hnot (Finset.mem_filter.2 ⟨hlam, by omega⟩))
  -- discard the vectors which are not strictly decreasing
  have hstrict : ∑ d ∈ (zeroOneAntidiag m r).filter
        (fun d : Fin m →₀ ℕ => ∀ i j : Fin m, (j : ℕ) = (i : ℕ) + 1 →
          (partVec m mu + ⇑d) j < (partVec m mu + ⇑d) i), alt m R (partVec m mu + ⇑d)
      = ∑ d ∈ zeroOneAntidiag m r, alt m R (partVec m mu + ⇑d) := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun d hd hnot => ?_
    obtain ⟨-, hone⟩ := mem_zeroOneAntidiag.1 hd
    have : ¬ ∀ i j : Fin m, (j : ℕ) = (i : ℕ) + 1 →
        (partVec m mu + ⇑d) j < (partVec m mu + ⇑d) i := fun h =>
      hnot (Finset.mem_filter.2 ⟨hd, h⟩)
    push Not at this
    obtain ⟨i, j, hij, hnotlt⟩ := this
    exact alt_eq_zero_of_not_strict hmu hone hij (by omega)
  rw [← hsub, ← hstrict]
  refine Finset.sum_nbij' (fun d => vecPart m (partVec m mu + ⇑d)) (stripFinsupp m mu)
    ?_ ?_ ?_ ?_ ?_
  · intro d hd
    obtain ⟨hd0, hs⟩ := Finset.mem_filter.1 hd
    obtain ⟨hdsum, hone⟩ := mem_zeroOneAntidiag.1 hd0
    have hge : ∀ i : Fin m, m - 1 - (i : ℕ) ≤ (partVec m mu + ⇑d) i := fun i =>
      le_trans (le_partVec mu i) (Nat.le_add_right _ _)
    have hpv : partVec m (vecPart m (partVec m mu + ⇑d)) = partVec m mu + ⇑d :=
      partVec_vecPart hge
    have hpart : IsPart (vecPart m (partVec m mu + ⇑d)) := isPart_vecPart_of_strict hge hs
    have hgetD : ∀ k : Fin m, (vecPart m (partVec m mu + ⇑d)).getD (k : ℕ) 0
        = mu.getD (k : ℕ) 0 + d k := by
      intro k
      have := congrFun hpv k
      simp only [partVec_apply, Pi.add_apply] at this ⊢
      omega
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨mem_partFinset.2 ⟨hpart,
      sum_vecPart hmulen hdsum⟩, ?_⟩, length_vecPart_le _⟩
    refine ⟨(hmu.included_iff_getD).2 fun k => ?_, fun k => ?_⟩
    · by_cases hk : k < m
      · rw [hgetD ⟨k, hk⟩]
        exact Nat.le_add_right _ _
      · rw [List.getD_eq_default _ _ (by omega)]
        exact Nat.zero_le _
    · by_cases hk : k < m
      · rw [hgetD ⟨k, hk⟩]
        have := hone ⟨k, hk⟩
        simp only
        omega
      · rw [getD_vecPart_of_le (by omega)]
        exact Nat.zero_le _
  · intro lam hlam
    obtain ⟨hlam', hlen⟩ := Finset.mem_filter.1 hlam
    obtain ⟨hlam'', hstrip⟩ := Finset.mem_filter.1 hlam'
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hlam''
    have hadd : partVec m mu + ⇑(stripFinsupp m mu lam) = partVec m lam :=
      add_stripFinsupp hstrip.1
    refine Finset.mem_filter.2 ⟨mem_zeroOneAntidiag.2 ⟨?_, fun k => ?_⟩, ?_⟩
    · rw [sum_stripFinsupp hstrip.1 hmulen hlen, hsum]
      omega
    · have h1 := hstrip.2 (k : ℕ)
      have h2 := hstrip.1.getD_le (k : ℕ)
      simp only [coe_stripFinsupp, partVec_apply]
      omega
    · intro i j hij
      rw [hadd]
      have hji : lam.getD (j : ℕ) 0 ≤ lam.getD (i : ℕ) 0 := hpart.getD_antitone (by omega)
      have hjm : (j : ℕ) < m := j.isLt
      simp only [partVec_apply]
      omega
  · intro d hd
    obtain ⟨hd0, -⟩ := Finset.mem_filter.1 hd
    have hge : ∀ i : Fin m, m - 1 - (i : ℕ) ≤ (partVec m mu + ⇑d) i := fun i =>
      le_trans (le_partVec mu i) (Nat.le_add_right _ _)
    have hpv : partVec m (vecPart m (partVec m mu + ⇑d)) = partVec m mu + ⇑d :=
      partVec_vecPart hge
    refine Finsupp.ext fun k => ?_
    have := congrFun hpv k
    simp only [coe_stripFinsupp, Pi.add_apply] at this ⊢
    omega
  · intro lam hlam
    obtain ⟨hlam', hlen⟩ := Finset.mem_filter.1 hlam
    obtain ⟨hlam'', hstrip⟩ := Finset.mem_filter.1 hlam'
    obtain ⟨hpart, -⟩ := mem_partFinset.1 hlam''
    rw [add_stripFinsupp hstrip.1, vecPart_partVec hpart hlen]
  · intro d hd
    obtain ⟨hd0, -⟩ := Finset.mem_filter.1 hd
    have hge : ∀ i : Fin m, m - 1 - (i : ℕ) ≤ (partVec m mu + ⇑d) i := fun i =>
      le_trans (le_partVec mu i) (Nat.le_add_right _ _)
    rw [altPart_of_le (length_vecPart_le _), partVec_vecPart hge]

end MvPolynomial
