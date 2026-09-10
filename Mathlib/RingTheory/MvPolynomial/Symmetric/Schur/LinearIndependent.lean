/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Kostka

/-!
# Linear independence of the Schur polynomials

Following `theories/MPoly/Schur_mpoly.v` and `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), the Schur polynomials of the
partitions of `n` with at most `m` parts are linearly independent in the polynomial ring
in `m` variables.

The proof is the classical unitriangularity argument: `s_λ = m_λ + (monomials of content
strictly dominated by λ)`, so extracting the coefficient of the monomial `x^λ` for a
partition `λ` which is maximal for the dominance order among those occurring in a
vanishing linear combination shows that its coefficient vanishes.

## Main results

* `MvPolynomial.linearIndependent_schurPoly` : the Schur polynomials of the partitions of `n`
  with at most `m` parts are linearly independent.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {m : ℕ} {R : Type*}

/-! ### A weight function strictly increasing along the dominance order -/

/-- The sum of the partial sums of `l`, a weight function monotone for the dominance
order. -/
def domWeight (n : ℕ) (l : List ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (l.take k).sum

lemma domWeight_le_domWeight {n : ℕ} {s t : List ℕ} (h : Partdom s t) :
    domWeight n s ≤ domWeight n t :=
  Finset.sum_le_sum fun k _ => h k

/-- Two partitions of `n` comparable for dominance and of the same weight are equal. -/
lemma eq_of_partdom_of_domWeight_eq {n : ℕ} {s t : List ℕ} (hs : IsPart s) (ht : IsPart t)
    (hsum : s.sum = n) (hsum' : t.sum = n) (h : Partdom s t)
    (hw : domWeight n t ≤ domWeight n s) : s = t := by
  have hle : ∀ k ∈ Finset.range (n + 1), (s.take k).sum ≤ (t.take k).sum := fun k _ => h k
  have heq : domWeight n s = domWeight n t :=
    le_antisymm (domWeight_le_domWeight h) hw
  have hall : ∀ k ∈ Finset.range (n + 1), (s.take k).sum = (t.take k).sum :=
    (Finset.sum_eq_sum_iff_of_le hle).1 heq
  refine sum_take_inj hs ht fun k => ?_
  rcases le_or_gt k n with hk | hk
  · exact hall k (Finset.mem_range.2 (by omega))
  · have hslen : s.length ≤ n := hsum ▸ hs.length_le_sum
    have htlen : t.length ≤ n := hsum' ▸ ht.length_le_sum
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega), hsum, hsum']

/-! ### The content vector of a partition -/

lemma getD_ofFn_shapeContent (μ : List ℕ) (hlen : μ.length ≤ m) (i : ℕ) :
    (List.ofFn fun j : Fin m => shapeContent m μ j).getD i 0 = μ.getD i 0 := by
  by_cases hi : i < m
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using hi),
      List.getD_eq_default _ _ (by omega)]

lemma sum_take_ofFn_shapeContent (μ : List ℕ) (hlen : μ.length ≤ m) (k : ℕ) :
    ((List.ofFn fun j : Fin m => shapeContent m μ j).take k).sum = (μ.take k).sum := by
  rw [sum_take_eq_sum_range, sum_take_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => getD_ofFn_shapeContent μ hlen i

lemma partdom_of_coeff_ne_zero [CommSemiring R] {ν μ : List ℕ} (hlen : ν.length ≤ m)
    (h : coeff (shapeContent m ν) (schurPoly (Fin m) R μ) ≠ 0) : Partdom ν μ := by
  by_contra hdom
  refine h (coeff_schurPoly_eq_zero_of_not_partdom μ _ ?_)
  intro hcon
  exact hdom fun k => by
    rw [← sum_take_ofFn_shapeContent ν hlen k]
    exact hcon k

/-- A Schur polynomial in `m` variables is nonzero as soon as its shape has at most `m`
rows. -/
theorem schurPoly_ne_zero [CommSemiring R] [Nontrivial R] {μ : List ℕ} (hμ : IsPart μ)
    (hlen : μ.length ≤ m) : schurPoly (Fin m) R μ ≠ 0 := by
  intro h
  have hone := coeff_schurPoly_self (R := R) hμ hlen
  rw [h, coeff_zero] at hone
  exact zero_ne_one hone

/-! ### Linear independence -/

/-- **The Schur polynomials are linearly independent**: the Schur polynomials of the
partitions of `n` with at most `m` parts are linearly independent over any commutative
ring. -/
theorem linearIndependent_schurPoly (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R fun η : {p : List ℕ // IsPart p ∧ p.sum = n ∧ p.length ≤ m} =>
      schurPoly (Fin m) R η.1 := by
  classical
  rw [linearIndependent_iff']
  intro s g hg η hη
  by_contra hne
  set t := s.filter (fun μ => g μ ≠ 0) with ht
  have hηt : η ∈ t := Finset.mem_filter.2 ⟨hη, hne⟩
  obtain ⟨ν, hνt, hmax⟩ :=
    Finset.exists_max_image t (fun μ => domWeight n μ.1) ⟨η, hηt⟩
  obtain ⟨hνs, hν0⟩ := Finset.mem_filter.1 hνt
  have hcoeff := congrArg (coeff (shapeContent m ν.1)) hg
  rw [coeff_zero, coeff_sum] at hcoeff
  have hsingle : ∀ μ ∈ s, μ ≠ ν →
      coeff (shapeContent m ν.1) (g μ • schurPoly (Fin m) R μ.1) = 0 := by
    intro μ hμs hμne
    rw [coeff_smul, smul_eq_mul]
    by_cases hμt : μ ∈ t
    · have hzero : coeff (shapeContent m ν.1) (schurPoly (Fin m) R μ.1) = 0 := by
        by_contra hc
        have hdom : Partdom ν.1 μ.1 := partdom_of_coeff_ne_zero ν.2.2.2 hc
        exact hμne (Subtype.ext (eq_of_partdom_of_domWeight_eq ν.2.1 μ.2.1 ν.2.2.1
          μ.2.2.1 hdom (hmax μ hμt))).symm
      rw [hzero, mul_zero]
    · have : g μ = 0 := by
        by_contra hgc
        exact hμt (Finset.mem_filter.2 ⟨hμs, hgc⟩)
      rw [this, zero_mul]
  rw [Finset.sum_eq_single ν hsingle (fun h => absurd hνs h), coeff_smul, smul_eq_mul,
    coeff_schurPoly_self ν.2.1 ν.2.2.2, mul_one] at hcoeff
  exact hν0 hcoeff

end MvPolynomial
