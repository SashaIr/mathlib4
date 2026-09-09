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

lemma getD_ofFn_shapeContent (sh : List ℕ) (hlen : sh.length ≤ m) (i : ℕ) :
    (List.ofFn fun j : Fin m => shapeContent m sh j).getD i 0 = sh.getD i 0 := by
  by_cases hi : i < m
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using hi),
      List.getD_eq_default _ _ (by omega)]

lemma sum_take_ofFn_shapeContent (sh : List ℕ) (hlen : sh.length ≤ m) (k : ℕ) :
    ((List.ofFn fun j : Fin m => shapeContent m sh j).take k).sum = (sh.take k).sum := by
  rw [sum_take_eq_sum_range, sum_take_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => getD_ofFn_shapeContent sh hlen i

lemma partdom_of_coeff_ne_zero [CommSemiring R] {sh mu : List ℕ} (hlen : sh.length ≤ m)
    (h : coeff (shapeContent m sh) (schurPoly (Fin m) R mu) ≠ 0) : Partdom sh mu := by
  by_contra hdom
  refine h (coeff_schurPoly_eq_zero_of_not_partdom mu _ ?_)
  intro hcon
  exact hdom fun k => by
    rw [← sum_take_ofFn_shapeContent sh hlen k]
    exact hcon k

/-- A Schur polynomial in `m` variables is nonzero as soon as its shape has at most `m`
rows. -/
theorem schurPoly_ne_zero [CommSemiring R] [Nontrivial R] {sh : List ℕ} (hsh : IsPart sh)
    (hlen : sh.length ≤ m) : schurPoly (Fin m) R sh ≠ 0 := by
  intro h
  have hone := coeff_schurPoly_self (R := R) hsh hlen
  rw [h, coeff_zero] at hone
  exact zero_ne_one hone

/-! ### Linear independence -/

/-- **The Schur polynomials are linearly independent**: the Schur polynomials of the
partitions of `n` with at most `m` parts are linearly independent over any commutative
ring. -/
theorem linearIndependent_schurPoly (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R fun lam : {p : List ℕ // IsPart p ∧ p.sum = n ∧ p.length ≤ m} =>
      schurPoly (Fin m) R lam.1 := by
  classical
  rw [linearIndependent_iff']
  intro s g hg lam hlam
  by_contra hne
  set t := s.filter (fun mu => g mu ≠ 0) with ht
  have hlamt : lam ∈ t := Finset.mem_filter.2 ⟨hlam, hne⟩
  obtain ⟨nu, hnut, hmax⟩ :=
    Finset.exists_max_image t (fun mu => domWeight n mu.1) ⟨lam, hlamt⟩
  obtain ⟨hnus, hnu0⟩ := Finset.mem_filter.1 hnut
  have hcoeff := congrArg (coeff (shapeContent m nu.1)) hg
  rw [coeff_zero, coeff_sum] at hcoeff
  have hsingle : ∀ mu ∈ s, mu ≠ nu →
      coeff (shapeContent m nu.1) (g mu • schurPoly (Fin m) R mu.1) = 0 := by
    intro mu hmus hmune
    rw [coeff_smul, smul_eq_mul]
    by_cases hmut : mu ∈ t
    · have hzero : coeff (shapeContent m nu.1) (schurPoly (Fin m) R mu.1) = 0 := by
        by_contra hc
        have hdom : Partdom nu.1 mu.1 := partdom_of_coeff_ne_zero nu.2.2.2 hc
        exact hmune (Subtype.ext (eq_of_partdom_of_domWeight_eq nu.2.1 mu.2.1 nu.2.2.1
          mu.2.2.1 hdom (hmax mu hmut))).symm
      rw [hzero, mul_zero]
    · have : g mu = 0 := by
        by_contra hgc
        exact hmut (Finset.mem_filter.2 ⟨hmus, hgc⟩)
      rw [this, zero_mul]
  rw [Finset.sum_eq_single nu hsingle (fun h => absurd hnus h), coeff_smul, smul_eq_mul,
    coeff_schurPoly_self nu.2.1 nu.2.2.2, mul_one] at hcoeff
  exact hnu0 hcoeff

end MvPolynomial
