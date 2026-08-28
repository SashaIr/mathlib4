/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.DualPieriSchur

/-!
# The dual Cauchy identity

Following `theories/MPoly/Cauchy.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove the dual Cauchy identity

`∏_{j < k} ∏_{i < m} (1 + x_i y_j) = ∑_lam s_lam(x) * s_{lam'}(y)`,

where the sum is over all partitions `lam` of size at most `m * k` (the terms attached to
the partitions that are not contained in the `m × k` rectangle vanish).

The proof is by induction on the number `k` of `y` variables.  Splitting off the last
variable, the left-hand side gets multiplied by `∑_r e_r(x) y_k^r`, which by the dual
Pieri rule `MvPolynomial.schurPoly_mul_esymm` adds a vertical strip to the `x` side; the
right-hand side is expanded by the branching rule `MvPolynomial.schurPoly_branching'`, which
removes a horizontal strip on the `y` side.  Conjugation exchanges the two kinds of
strips, which is `List.vertStrip_conjPart_iff`.

## Main results

* `MvPolynomial.prod_one_add_C_X_mul` : the generating function of the elementary symmetric
  polynomials.
* `MvPolynomial.dual_cauchy` : the dual Cauchy identity.
-/

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
    ∑ mu ∈ partFinsetLe N, f mu = ∑ nu ∈ partFinsetLe N, f (conjPart nu) := by
  refine Finset.sum_nbij' (fun mu => conjPart mu) (fun nu => conjPart nu) ?_ ?_ ?_ ?_ ?_
  · intro mu hmu
    obtain ⟨hpart, hsum⟩ := mem_partFinsetLe.1 hmu
    exact mem_partFinsetLe.2 ⟨isPart_conjPart hpart, by rw [sum_conjPart]; exact hsum⟩
  · intro nu hnu
    obtain ⟨hpart, hsum⟩ := mem_partFinsetLe.1 hnu
    exact mem_partFinsetLe.2 ⟨isPart_conjPart hpart, by rw [sum_conjPart]; exact hsum⟩
  · intro mu hmu
    exact conjPart_conjPart (mem_partFinsetLe.1 hmu).1
  · intro nu hnu
    exact conjPart_conjPart (mem_partFinsetLe.1 hnu).1
  · intro mu hmu
    rw [conjPart_conjPart (mem_partFinsetLe.1 hmu).1]

/-! ### The terms of the induction -/

open Classical in
/-- The term indexed by the pair of partitions `(lam, mu)` in the inductive step of the
dual Cauchy identity: `mu` is the shape on the first `k` variables `y`, and `lam` is
obtained from `mu` by adding a vertical strip, filled by the last variable. -/
noncomputable def dualCauchyTerm (m k : ℕ) (R : Type*) [CommRing R] (lam mu : List ℕ) :
    MvPolynomial (Fin (k + 1)) (MvPolynomial (Fin m) R) :=
  if VertStrip lam mu then
    C (schurPoly (Fin m) R lam)
      * (rename Fin.castSucc (schurPoly (Fin k) (MvPolynomial (Fin m) R) (conjPart mu))
          * X (Fin.last k) ^ (lam.sum - mu.sum))
  else 0

variable {m k : ℕ} {R : Type*} [CommRing R]

lemma dualCauchyTerm_eq_zero_of_sum_lt {lam mu : List ℕ} (h : lam.sum < mu.sum) :
    dualCauchyTerm m k R lam mu = 0 := by
  rw [dualCauchyTerm, if_neg]
  exact fun hstrip => absurd hstrip.1.sum_le (by omega)

/-- Outside the `m × k` rectangle the terms of the dual Cauchy identity vanish. -/
lemma dualCauchyTerm_eq_zero_of_lt_sum {lam mu : List ℕ} (hmu : IsPart mu)
    (h : m * k < mu.sum) : dualCauchyTerm m k R lam mu = 0 := by
  rw [dualCauchyTerm]
  split_ifs with hstrip
  · by_cases hlen : m < lam.length
    · rw [schurPoly_eq_zero_of_lt_length hlen, map_zero, zero_mul]
    · by_cases hlenc : k < (conjPart mu).length
      · rw [schurPoly_eq_zero_of_lt_length hlenc, map_zero, zero_mul, mul_zero]
      · exfalso
        have hmulen : mu.length ≤ m := le_trans hstrip.1.length_le (by omega)
        have hhead : mu.headD 0 ≤ k := by
          rw [length_conjPart hmu] at hlenc; omega
        have hle : mu.sum ≤ m * k := by
          refine le_trans hmu.sum_le_headD_mul_length ?_
          rw [Nat.mul_comm m k]
          exact Nat.mul_le_mul hhead hmulen
        omega
  · rfl

/-- Only the partitions inside the `m × k` rectangle contribute to the inner sum. -/
lemma sum_dualCauchyTerm_eq (m k : ℕ) (R : Type*) [CommRing R] {lam : List ℕ}
    (hlam : lam.sum ≤ m * (k + 1)) :
    ∑ mu ∈ partFinsetLe lam.sum, dualCauchyTerm m k R lam mu
      = ∑ mu ∈ partFinsetLe (m * k), dualCauchyTerm m k R lam mu := by
  have h1 : ∑ mu ∈ partFinsetLe lam.sum, dualCauchyTerm m k R lam mu
      = ∑ mu ∈ partFinsetLe (m * (k + 1)), dualCauchyTerm m k R lam mu := by
    refine Finset.sum_subset (fun mu hmu => ?_) (fun mu hmu hnot => ?_)
    · rw [mem_partFinsetLe] at hmu ⊢
      exact ⟨hmu.1, le_trans hmu.2 hlam⟩
    · rw [mem_partFinsetLe] at hmu hnot
      exact dualCauchyTerm_eq_zero_of_sum_lt
        (by by_contra hc; exact hnot ⟨hmu.1, by omega⟩)
  have h2 : ∑ mu ∈ partFinsetLe (m * k), dualCauchyTerm m k R lam mu
      = ∑ mu ∈ partFinsetLe (m * (k + 1)), dualCauchyTerm m k R lam mu := by
    refine Finset.sum_subset (fun mu hmu => ?_) (fun mu hmu hnot => ?_)
    · rw [mem_partFinsetLe] at hmu ⊢
      exact ⟨hmu.1, le_trans hmu.2 (Nat.mul_le_mul_left m (by omega))⟩
    · rw [mem_partFinsetLe] at hmu hnot
      exact dualCauchyTerm_eq_zero_of_lt_sum hmu.1
        (by by_contra hc; exact hnot ⟨hmu.1, by omega⟩)
  rw [h1, h2]

/-- The sum over the possible sizes of the vertical strip collapses to a single term. -/
lemma sum_range_eq_dualCauchyTerm (m k : ℕ) (R : Type*) [CommRing R] (lam mu : List ℕ) :
    ∑ r ∈ Finset.range (m + 1),
        (if lam.sum = mu.sum + r then
          (if VertStrip lam mu then C (schurPoly (Fin m) R lam) else 0)
            * (rename Fin.castSucc (schurPoly (Fin k) (MvPolynomial (Fin m) R) (conjPart mu))
                * X (Fin.last k) ^ r)
        else 0)
      = dualCauchyTerm m k R lam mu := by
  classical
  rw [dualCauchyTerm]
  by_cases hstrip : VertStrip lam mu
  · simp only [if_pos hstrip]
    by_cases hd : lam.sum - mu.sum ≤ m
    · rw [Finset.sum_eq_single (lam.sum - mu.sum)]
      · rw [if_pos (by have := hstrip.1.sum_le; omega)]
      · intro r _ hr
        refine if_neg ?_
        have := hstrip.1.sum_le
        omega
      · intro h
        exact absurd (Finset.mem_range.2 (by omega)) h
    · have hlen : m < lam.length := by
        have := hstrip.sum_le_sum_add_length
        omega
      rw [schurPoly_eq_zero_of_lt_length hlen, map_zero, zero_mul]
      refine Finset.sum_eq_zero fun r hr => ?_
      rw [Finset.mem_range] at hr
      refine if_neg ?_
      have := hstrip.1.sum_le
      omega
  · simp only [if_neg hstrip, zero_mul, ite_self, Finset.sum_const_zero]

/-- One term of the dual Pieri expansion, written as a sum over the partitions of size at
most `m * (k + 1)`. -/
lemma mul_esymm_eq_sum_partFinsetLe (m k : ℕ) (R : Type*) [CommRing R] {mu : List ℕ}
    (hmu : IsPart mu) (hmusum : mu.sum ≤ m * k) {r : ℕ} (hr : r ≤ m) :
    C (schurPoly (Fin m) R mu)
        * rename Fin.castSucc (schurPoly (Fin k) (MvPolynomial (Fin m) R) (conjPart mu))
        * (C (esymm (Fin m) R r) * X (Fin.last k) ^ r)
      = ∑ lam ∈ partFinsetLe (m * (k + 1)),
          (if lam.sum = mu.sum + r then
            (if VertStrip lam mu then C (schurPoly (Fin m) R lam) else 0)
              * (rename Fin.castSucc (schurPoly (Fin k) (MvPolynomial (Fin m) R) (conjPart mu))
                  * X (Fin.last k) ^ r)
          else 0) := by
  classical
  have hle : mu.sum + r ≤ m * (k + 1) := by
    have : m * (k + 1) = m * k + m := by ring
    omega
  rw [← sum_partFinset_eq_sum_partFinsetLe hle, ← Finset.sum_mul,
    show (∑ lam ∈ partFinset (mu.sum + r),
        if VertStrip lam mu then C (schurPoly (Fin m) R lam) else 0)
      = C (∑ lam ∈ partFinset (mu.sum + r),
          if VertStrip lam mu then schurPoly (Fin m) R lam else 0) by
      rw [map_sum]
      exact Finset.sum_congr rfl fun lam _ => by split_ifs <;> simp,
    ← schurPoly_mul_esymm hmu r, map_mul]
  ring

/-! ### The two sides of the inductive step -/

/-- The left-hand side of the dual Cauchy identity for `k + 1` variables `y`, rewritten
using the induction hypothesis, the generating function of the elementary symmetric
polynomials and the dual Pieri rule. -/
lemma dualCauchy_lhs (m k : ℕ) (R : Type*) [CommRing R]
    (IH : (∏ j : Fin k, ∏ i : Fin m,
        (1 + C (X i) * X j) : MvPolynomial (Fin k) (MvPolynomial (Fin m) R))
      = ∑ lam ∈ partFinsetLe (m * k),
          C (schurPoly (Fin m) R lam)
            * schurPoly (Fin k) (MvPolynomial (Fin m) R) (conjPart lam)) :
    (∏ j : Fin (k + 1), ∏ i : Fin m,
        (1 + C (X i) * X j) : MvPolynomial (Fin (k + 1)) (MvPolynomial (Fin m) R))
      = ∑ lam ∈ partFinsetLe (m * (k + 1)), ∑ mu ∈ partFinsetLe (m * k),
          dualCauchyTerm m k R lam mu := by
  classical
  have hfirst : (∏ j : Fin k, ∏ i : Fin m,
        (1 + C (X i) * X (Fin.castSucc j)) : MvPolynomial (Fin (k + 1)) (MvPolynomial (Fin m) R))
      = rename Fin.castSucc (∏ j : Fin k, ∏ i : Fin m, (1 + C (X i) * X j)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => by simp
  have key : ∀ mu ∈ partFinsetLe (m * k),
      rename Fin.castSucc (C (schurPoly (Fin m) R mu)
          * schurPoly (Fin k) (MvPolynomial (Fin m) R) (conjPart mu))
        * ∑ r ∈ Finset.range (m + 1), C (esymm (Fin m) R r) * X (Fin.last k) ^ r
      = ∑ lam ∈ partFinsetLe (m * (k + 1)), dualCauchyTerm m k R lam mu := by
    intro mu hmu
    obtain ⟨hmupart, hmusum⟩ := mem_partFinsetLe.1 hmu
    rw [map_mul, rename_C, Finset.mul_sum,
      Finset.sum_congr rfl (fun r hr => mul_esymm_eq_sum_partFinsetLe m k R hmupart hmusum
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr))), Finset.sum_comm]
    exact Finset.sum_congr rfl fun lam _ => sum_range_eq_dualCauchyTerm m k R lam mu
  rw [Fin.prod_univ_castSucc, hfirst, IH, map_sum, prod_one_add_C_X_mul, Finset.sum_mul,
    Finset.sum_congr rfl key, Finset.sum_comm]

/-- The right-hand side of the dual Cauchy identity for `k + 1` variables `y`, expanded by
the branching rule. -/
lemma dualCauchy_rhs (m k : ℕ) (R : Type*) [CommRing R] :
    (∑ lam ∈ partFinsetLe (m * (k + 1)),
        C (schurPoly (Fin m) R lam)
          * schurPoly (Fin (k + 1)) (MvPolynomial (Fin m) R) (conjPart lam))
      = ∑ lam ∈ partFinsetLe (m * (k + 1)), ∑ mu ∈ partFinsetLe (m * k),
          dualCauchyTerm m k R lam mu := by
  classical
  refine Finset.sum_congr rfl fun lam hlam => ?_
  obtain ⟨hlampart, hlamsum⟩ := mem_partFinsetLe.1 hlam
  rw [← sum_dualCauchyTerm_eq m k R hlamsum, schurPoly_branching' k (isPart_conjPart hlampart),
    sum_conjPart,
    sum_partFinsetLe_conjPart lam.sum (fun nu => if HorizStrip (conjPart lam) nu then
      rename Fin.castSucc (schurPoly (Fin k) (MvPolynomial (Fin m) R) nu)
        * X (Fin.last k) ^ (lam.sum - nu.sum) else 0), Finset.mul_sum]
  refine Finset.sum_congr rfl fun mu hmu => ?_
  have hmupart : IsPart mu := (mem_partFinsetLe.1 hmu).1
  have hiff : HorizStrip (conjPart lam) (conjPart mu) ↔ VertStrip lam mu := by
    have h := vertStrip_conjPart_iff (isPart_conjPart hlampart) (isPart_conjPart hmupart)
    rw [conjPart_conjPart hlampart, conjPart_conjPart hmupart] at h
    exact h.symm
  rw [dualCauchyTerm, sum_conjPart]
  by_cases hstrip : VertStrip lam mu
  · rw [if_pos (hiff.2 hstrip), if_pos hstrip]
  · rw [if_neg (fun h => hstrip (hiff.1 h)), if_neg hstrip, mul_zero]

/-- **The dual Cauchy identity**: the product of the `1 + x_i y_j` is the sum over the
partitions `lam` of the products `s_lam(x) * s_{lam'}(y)`. -/
theorem dual_cauchy (m k : ℕ) (R : Type*) [CommRing R] :
    (∏ j : Fin k, ∏ i : Fin m,
        (1 + C (X i) * X j) : MvPolynomial (Fin k) (MvPolynomial (Fin m) R))
      = ∑ lam ∈ partFinsetLe (m * k),
          C (schurPoly (Fin m) R lam)
            * schurPoly (Fin k) (MvPolynomial (Fin m) R) (conjPart lam) := by
  induction k with
  | zero =>
      rw [Nat.mul_zero, partFinsetLe, show Finset.range (0 + 1) = {0} from rfl]
      simp [partFinset_zero, schurPoly_nil]
  | succ k IH => rw [dualCauchy_lhs m k R IH, dualCauchy_rhs m k R]

end MvPolynomial
