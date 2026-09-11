/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.DualPieriSchur

/-!
# The dual Cauchy identity

Following `theories/MPoly/Cauchy.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove the dual Cauchy identity

`∏_{j < k} ∏_{i < m} (1 + x_i y_j) = ∑_lam s_μ(x) * s_{μ'}(y)`,

where the sum is over all partitions `μ` of size at most `m * k` (the terms attached to
the partitions that are not contained in the `m × k` rectangle vanish).

The proof is by induction on the number `k` of `y` variables.  Splitting off the last
variable, the left-hand side gets multiplied by `∑_r e_r(x) y_k^r`, which by the dual
Pieri rule `MvPolynomial.schurPoly_mul_esymm` adds a vertical strip to the `x` side; the
right-hand side is expanded by the branching rule `MvPolynomial.schurPoly_branching'`, which
removes a horizontal strip on the `y` side.  Conjugation exchanges the two kinds of
strips, which is `Young.vertStrip_conjPart_iff`.

## Main results

* `MvPolynomial.prod_one_add_C_X_mul` : the generating function of the elementary symmetric
  polynomials.
* `MvPolynomial.dual_cauchy` : the dual Cauchy identity.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

/-! ### The generating function of the elementary symmetric polynomials -/

/-- The expansion of a product `∏ (1 + a i * t)` over the subsets of the index set. -/
lemma prod_one_add_mul_eq_sum_powersetCard {A : Type*} [CommSemiring A] {m : ℕ}
    (a : Fin m → A) (t : A) :
    ∏ i : Fin m, (1 + a i * t)
      = ∑ r ∈ Finset.range (m + 1),
          (∑ s ∈ Finset.powersetCard r (Finset.univ : Finset (Fin m)), ∏ i ∈ s, a i) * t ^ r := by
  classical
  have h : ∏ i : Fin m, (1 + a i * t)
      = ∑ s ∈ (Finset.univ : Finset (Fin m)).powerset, (∏ i ∈ s, a i) * t ^ s.card := by
    rw [show (fun i : Fin m => 1 + a i * t) = (fun i : Fin m => a i * t + 1) by
      funext i; ring]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const_one, mul_one]
  rw [h, Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun s hs => by rw [(Finset.mem_powersetCard.1 hs).2]

/-- The generating function of the elementary symmetric polynomials: the product of the
`1 + x_i t` is `∑_r e_r(x) t^r`. -/
lemma prod_one_add_C_X_mul (m k : ℕ) (R : Type*) [CommRing R]
    (t : MvPolynomial (Fin k) (MvPolynomial (Fin m) R)) :
    ∏ i : Fin m, (1 + C (X i) * t)
      = ∑ r ∈ Finset.range (m + 1), C (esymm (Fin m) R r) * t ^ r := by
  rw [prod_one_add_mul_eq_sum_powersetCard]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  rw [esymm, map_sum]
  exact Finset.sum_congr rfl fun s _ => (map_prod _ _ _).symm

/-! ### Combinatorial preliminaries -/

/-- Reindexing a sum over the partitions of size at most `N` by conjugation. -/
lemma sum_partFinsetLe_conjPart {M : Type*} [AddCommMonoid M] (N : ℕ) (f : List ℕ → M) :
    ∑ μ ∈ partFinsetLe N, f μ = ∑ ν ∈ partFinsetLe N, f (conjPart ν) := by
  refine Finset.sum_nbij' (fun μ => conjPart μ) (fun ν => conjPart ν) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    obtain ⟨hpart, hsum⟩ := mem_partFinsetLe.1 hμ
    exact mem_partFinsetLe.2 ⟨isPart_conjPart hpart, by rw [sum_conjPart]; exact hsum⟩
  · intro ν hν
    obtain ⟨hpart, hsum⟩ := mem_partFinsetLe.1 hν
    exact mem_partFinsetLe.2 ⟨isPart_conjPart hpart, by rw [sum_conjPart]; exact hsum⟩
  · intro μ hμ
    exact conjPart_conjPart (mem_partFinsetLe.1 hμ).1
  · intro ν hν
    exact conjPart_conjPart (mem_partFinsetLe.1 hν).1
  · intro μ hμ
    rw [conjPart_conjPart (mem_partFinsetLe.1 hμ).1]

/-! ### The terms of the induction -/

open Classical in
/-- The term indexed by the pair of partitions `(μ, ν)` in the inductive step of the
dual Cauchy identity: `ν` is the shape on the first `k` variables `y`, and `μ` is
obtained from `ν` by adding a vertical strip, filled by the last variable. -/
noncomputable def dualCauchyTerm (m k : ℕ) (R : Type*) [CommRing R] (μ ν : List ℕ) :
    MvPolynomial (Fin (k + 1)) (MvPolynomial (Fin m) R) :=
  if VertStrip μ ν then
    C (schurPoly (Fin m) R μ)
      * (rename Fin.castSucc (schurPoly (Fin k) (MvPolynomial (Fin m) R) (conjPart ν))
          * X (Fin.last k) ^ (μ.sum - ν.sum))
  else 0

variable {m k : ℕ} {R : Type*} [CommRing R]

lemma dualCauchyTerm_eq_zero_of_sum_lt {μ ν : List ℕ} (h : μ.sum < ν.sum) :
    dualCauchyTerm m k R μ ν = 0 := by
  rw [dualCauchyTerm, ite_eq_right]
  exact fun hstrip => absurd hstrip.1.sum_le (by omega)

/-- Outside the `m × k` rectangle the terms of the dual Cauchy identity vanish. -/
lemma dualCauchyTerm_eq_zero_of_lt_sum {μ ν : List ℕ} (hν : IsPart ν)
    (h : m * k < ν.sum) : dualCauchyTerm m k R μ ν = 0 := by
  rw [dualCauchyTerm]
  split_ifs with hstrip
  · by_cases hlen : m < μ.length
    · rw [schurPoly_eq_zero_of_lt_length hlen, map_zero, zero_mul]
    · by_cases hlenc : k < (conjPart ν).length
      · rw [schurPoly_eq_zero_of_lt_length hlenc, map_zero, zero_mul, mul_zero]
      · exfalso
        have hνlen : ν.length ≤ m := le_trans hstrip.1.length_le (by omega)
        have hhead : ν.headD 0 ≤ k := by
          rw [length_conjPart hν] at hlenc; omega
        have hle : ν.sum ≤ m * k := by
          refine le_trans hν.sum_le_headD_mul_length ?_
          rw [Nat.mul_comm m k]
          exact Nat.mul_le_mul hhead hνlen
        omega
  · rfl

/-- Only the partitions inside the `m × k` rectangle contribute to the inner sum. -/
lemma sum_dualCauchyTerm_eq (m k : ℕ) (R : Type*) [CommRing R] {μ : List ℕ}
    (hμ : μ.sum ≤ m * (k + 1)) :
    ∑ ν ∈ partFinsetLe μ.sum, dualCauchyTerm m k R μ ν
      = ∑ ν ∈ partFinsetLe (m * k), dualCauchyTerm m k R μ ν := by
  have h1 : ∑ ν ∈ partFinsetLe μ.sum, dualCauchyTerm m k R μ ν
      = ∑ ν ∈ partFinsetLe (m * (k + 1)), dualCauchyTerm m k R μ ν := by
    refine Finset.sum_subset (fun ν hν => ?_) (fun ν hν hnot => ?_)
    · rw [mem_partFinsetLe] at hν ⊢
      exact ⟨hν.1, le_trans hν.2 hμ⟩
    · rw [mem_partFinsetLe] at hν hnot
      exact dualCauchyTerm_eq_zero_of_sum_lt
        (by by_contra hc; exact hnot ⟨hν.1, by omega⟩)
  have h2 : ∑ ν ∈ partFinsetLe (m * k), dualCauchyTerm m k R μ ν
      = ∑ ν ∈ partFinsetLe (m * (k + 1)), dualCauchyTerm m k R μ ν := by
    refine Finset.sum_subset (fun ν hν => ?_) (fun ν hν hnot => ?_)
    · rw [mem_partFinsetLe] at hν ⊢
      exact ⟨hν.1, le_trans hν.2 (Nat.mul_le_mul_left m (by omega))⟩
    · rw [mem_partFinsetLe] at hν hnot
      exact dualCauchyTerm_eq_zero_of_lt_sum hν.1
        (by by_contra hc; exact hnot ⟨hν.1, by omega⟩)
  rw [h1, h2]

/-- The sum over the possible sizes of the vertical strip collapses to a single term. -/
lemma sum_range_eq_dualCauchyTerm (m k : ℕ) (R : Type*) [CommRing R] (μ ν : List ℕ) :
    ∑ r ∈ Finset.range (m + 1),
        (if μ.sum = ν.sum + r then
          (if VertStrip μ ν then C (schurPoly (Fin m) R μ) else 0)
            * (rename Fin.castSucc (schurPoly (Fin k) (MvPolynomial (Fin m) R) (conjPart ν))
                * X (Fin.last k) ^ r)
        else 0)
      = dualCauchyTerm m k R μ ν := by
  classical
  rw [dualCauchyTerm]
  by_cases hstrip : VertStrip μ ν
  · simp only [ite_eq_left hstrip]
    by_cases hd : μ.sum - ν.sum ≤ m
    · rw [Finset.sum_eq_single (μ.sum - ν.sum)]
      · rw [ite_eq_left (by have := hstrip.1.sum_le; omega)]
      · intro r _ hr
        refine ite_eq_right ?_
        have := hstrip.1.sum_le
        omega
      · intro h
        exact absurd (Finset.mem_range.2 (by omega)) h
    · have hlen : m < μ.length := by
        have := hstrip.sum_le_sum_add_length
        omega
      rw [schurPoly_eq_zero_of_lt_length hlen, map_zero, zero_mul]
      refine Finset.sum_eq_zero fun r hr => ?_
      rw [Finset.mem_range] at hr
      refine ite_eq_right ?_
      have := hstrip.1.sum_le
      omega
  · simp only [ite_eq_right hstrip, zero_mul, ite_self, Finset.sum_const_zero]

/-- One term of the dual Pieri expansion, written as a sum over the partitions of size at
most `m * (k + 1)`. -/
lemma mul_esymm_eq_sum_partFinsetLe (m k : ℕ) (R : Type*) [CommRing R] {ν : List ℕ}
    (hν : IsPart ν) (hνsum : ν.sum ≤ m * k) {r : ℕ} (hr : r ≤ m) :
    C (schurPoly (Fin m) R ν)
        * rename Fin.castSucc (schurPoly (Fin k) (MvPolynomial (Fin m) R) (conjPart ν))
        * (C (esymm (Fin m) R r) * X (Fin.last k) ^ r)
      = ∑ μ ∈ partFinsetLe (m * (k + 1)),
          (if μ.sum = ν.sum + r then
            (if VertStrip μ ν then C (schurPoly (Fin m) R μ) else 0)
              * (rename Fin.castSucc (schurPoly (Fin k) (MvPolynomial (Fin m) R) (conjPart ν))
                  * X (Fin.last k) ^ r)
          else 0) := by
  classical
  have hle : ν.sum + r ≤ m * (k + 1) := by
    have : m * (k + 1) = m * k + m := by ring
    omega
  rw [← sum_partFinset_eq_sum_partFinsetLe hle, ← Finset.sum_mul,
    show (∑ μ ∈ partFinset (ν.sum + r),
        if VertStrip μ ν then C (schurPoly (Fin m) R μ) else 0)
      = C (∑ μ ∈ partFinset (ν.sum + r),
          if VertStrip μ ν then schurPoly (Fin m) R μ else 0) by
      rw [map_sum]
      exact Finset.sum_congr rfl fun μ _ => by split_ifs <;> simp,
    ← schurPoly_mul_esymm hν r, map_mul]
  ring

/-! ### The two sides of the inductive step -/

/-- The left-hand side of the dual Cauchy identity for `k + 1` variables `y`, rewritten
using the induction hypothesis, the generating function of the elementary symmetric
polynomials and the dual Pieri rule. -/
lemma dualCauchy_lhs (m k : ℕ) (R : Type*) [CommRing R]
    (IH : (∏ j : Fin k, ∏ i : Fin m,
        (1 + C (X i) * X j) : MvPolynomial (Fin k) (MvPolynomial (Fin m) R))
      = ∑ μ ∈ partFinsetLe (m * k),
          C (schurPoly (Fin m) R μ)
            * schurPoly (Fin k) (MvPolynomial (Fin m) R) (conjPart μ)) :
    (∏ j : Fin (k + 1), ∏ i : Fin m,
        (1 + C (X i) * X j) : MvPolynomial (Fin (k + 1)) (MvPolynomial (Fin m) R))
      = ∑ μ ∈ partFinsetLe (m * (k + 1)), ∑ ν ∈ partFinsetLe (m * k),
          dualCauchyTerm m k R μ ν := by
  classical
  have hfirst : (∏ j : Fin k, ∏ i : Fin m,
        (1 + C (X i) * X (Fin.castSucc j)) : MvPolynomial (Fin (k + 1)) (MvPolynomial (Fin m) R))
      = rename Fin.castSucc (∏ j : Fin k, ∏ i : Fin m, (1 + C (X i) * X j)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => by simp
  have key : ∀ ν ∈ partFinsetLe (m * k),
      rename Fin.castSucc (C (schurPoly (Fin m) R ν)
          * schurPoly (Fin k) (MvPolynomial (Fin m) R) (conjPart ν))
        * ∑ r ∈ Finset.range (m + 1), C (esymm (Fin m) R r) * X (Fin.last k) ^ r
      = ∑ μ ∈ partFinsetLe (m * (k + 1)), dualCauchyTerm m k R μ ν := by
    intro ν hν
    obtain ⟨hνpart, hνsum⟩ := mem_partFinsetLe.1 hν
    rw [map_mul, rename_C, Finset.mul_sum,
      Finset.sum_congr rfl (fun r hr => mul_esymm_eq_sum_partFinsetLe m k R hνpart hνsum
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr))), Finset.sum_comm]
    exact Finset.sum_congr rfl fun μ _ => sum_range_eq_dualCauchyTerm m k R μ ν
  rw [Fin.prod_univ_castSucc, hfirst, IH, map_sum, prod_one_add_C_X_mul, Finset.sum_mul,
    Finset.sum_congr rfl key, Finset.sum_comm]

/-- The right-hand side of the dual Cauchy identity for `k + 1` variables `y`, expanded by
the branching rule. -/
lemma dualCauchy_rhs (m k : ℕ) (R : Type*) [CommRing R] :
    (∑ μ ∈ partFinsetLe (m * (k + 1)),
        C (schurPoly (Fin m) R μ)
          * schurPoly (Fin (k + 1)) (MvPolynomial (Fin m) R) (conjPart μ))
      = ∑ μ ∈ partFinsetLe (m * (k + 1)), ∑ ν ∈ partFinsetLe (m * k),
          dualCauchyTerm m k R μ ν := by
  classical
  refine Finset.sum_congr rfl fun μ hμ => ?_
  obtain ⟨hμpart, hμsum⟩ := mem_partFinsetLe.1 hμ
  rw [← sum_dualCauchyTerm_eq m k R hμsum, schurPoly_branching' k (isPart_conjPart hμpart),
    sum_conjPart,
    sum_partFinsetLe_conjPart μ.sum (fun ρ => if HorizStrip (conjPart μ) ρ then
      rename Fin.castSucc (schurPoly (Fin k) (MvPolynomial (Fin m) R) ρ)
        * X (Fin.last k) ^ (μ.sum - ρ.sum) else 0), Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν hν => ?_
  have hνpart : IsPart ν := (mem_partFinsetLe.1 hν).1
  have hiff : HorizStrip (conjPart μ) (conjPart ν) ↔ VertStrip μ ν := by
    have h := vertStrip_conjPart_iff (isPart_conjPart hμpart) (isPart_conjPart hνpart)
    rw [conjPart_conjPart hμpart, conjPart_conjPart hνpart] at h
    exact h.symm
  rw [dualCauchyTerm, sum_conjPart]
  by_cases hstrip : VertStrip μ ν
  · rw [ite_eq_left (hiff.2 hstrip), ite_eq_left hstrip]
  · rw [ite_eq_right (fun h => hstrip (hiff.1 h)), ite_eq_right hstrip, mul_zero]

/-- **The dual Cauchy identity**: the product of the `1 + x_i y_j` is the sum over the
partitions `μ` of the products `s_μ(x) * s_{μ'}(y)`. -/
theorem dual_cauchy (m k : ℕ) (R : Type*) [CommRing R] :
    (∏ j : Fin k, ∏ i : Fin m,
        (1 + C (X i) * X j) : MvPolynomial (Fin k) (MvPolynomial (Fin m) R))
      = ∑ μ ∈ partFinsetLe (m * k),
          C (schurPoly (Fin m) R μ)
            * schurPoly (Fin k) (MvPolynomial (Fin m) R) (conjPart μ) := by
  induction k with
  | zero =>
      rw [Nat.mul_zero, partFinsetLe, show Finset.range (0 + 1) = {0} from rfl]
      simp [partFinset_zero, schurPoly_nil]
  | succ k IH => rw [dualCauchy_lhs m k R IH, dualCauchy_rhs m k R]

end MvPolynomial
