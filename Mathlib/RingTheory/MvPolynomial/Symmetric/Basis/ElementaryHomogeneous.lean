/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.MvPolynomial.Symmetric.Alternant.Basic

/-!
# The relation between the elementary and the complete homogeneous symmetric polynomials

Following `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove the fundamental relation

`∑_{i = 0}^{n} (-1)^i e_i h_{n-i} = 0`  (for `n ≥ 1`),

between the elementary symmetric polynomials `e_i` and the complete homogeneous symmetric
polynomials `h_r`.

The proof is by expanding both families as sums of monomials: the coefficient of a
monomial `x^e` of degree `n` in the left hand side is `∑_{S ⊆ supp e} (-1)^{|S|}`, which
vanishes because the support of `e` is nonempty.

## Main definitions and results

* `MvPolynomial.indicVec S` : the `0-1` exponent vector of a finite set of variables.
* `MvPolynomial.sum_neg_one_pow_esymm_mul_hsymm` : the relation above.
-/

namespace MvPolynomial

open MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### The exponent vector of a set of variables -/

/-- The `0-1` exponent vector attached to a finite set of variables. -/
noncomputable def indicVec (S : Finset (Fin m)) : Fin m →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1

@[simp] lemma indicVec_apply (S : Finset (Fin m)) (j : Fin m) :
    indicVec S j = if j ∈ S then 1 else 0 := by
  simp [indicVec, Finset.sum_apply', Finsupp.single_apply]

lemma sum_indicVec (S : Finset (Fin m)) : ∑ j, indicVec S j = S.card := by
  simp [Finset.sum_ite_mem]

lemma indicVec_le_iff {S : Finset (Fin m)} {e : Fin m →₀ ℕ} :
    indicVec S ≤ e ↔ S ⊆ e.support := by
  rw [Finsupp.le_def]
  constructor
  · intro h j hj
    have := h j
    rw [indicVec_apply, ite_eq_left hj] at this
    exact Finsupp.mem_support_iff.2 (by omega)
  · intro h j
    rw [indicVec_apply]
    split_ifs with hj
    · exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 (h hj))
    · exact Nat.zero_le _

/-- The support of an exponent vector has at most as many elements as its degree. -/
lemma card_support_le_sum (e : Fin m →₀ ℕ) : e.support.card ≤ ∑ j, e j := by
  calc e.support.card = ∑ _j ∈ e.support, 1 := by simp
    _ ≤ ∑ j ∈ e.support, e j :=
        Finset.sum_le_sum fun j hj => Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hj)
    _ ≤ ∑ j, e j := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-! ### The alternating sum of the coefficients -/

/-- For a nonzero exponent vector, the alternating sum over the subsets of variables
dividing it vanishes. -/
lemma sum_neg_one_pow_card_subsets {e : Fin m →₀ ℕ} {n : ℕ} (hsum : ∑ j, e j = n)
    (hn : 0 < n) :
    ∑ i ∈ Finset.range (n + 1), ∑ S ∈ Finset.powersetCard i (univ : Finset (Fin m)),
        (if indicVec S ≤ e then ((-1 : R)) ^ i else 0) = 0 := by
  classical
  have hne : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hem
    have : ∑ j, e j = 0 := Finset.sum_eq_zero fun j _ =>
      Finsupp.notMem_support_iff.1 (by simp [hem])
    omega
  have hcard : e.support.card ≤ n := hsum ▸ card_support_le_sum e
  rw [Finset.sum_sigma' (Finset.range (n + 1))
    (fun i => Finset.powersetCard i (univ : Finset (Fin m)))
    (fun i S => if indicVec S ≤ e then ((-1 : R)) ^ i else 0)]
  rw [← Finset.sum_filter]
  rw [show ∑ x ∈ ((Finset.range (n + 1)).sigma
        fun i => Finset.powersetCard i (univ : Finset (Fin m))).filter
          (fun x => indicVec x.2 ≤ e), ((-1 : R)) ^ x.1
      = ∑ S ∈ e.support.powerset, ((-1 : R)) ^ S.card from ?_]
  · have hZ : ∑ S ∈ e.support.powerset, ((-1 : ℤ)) ^ S.card = 0 :=
      Finset.sum_powerset_neg_one_pow_card_of_nonempty hne
    have := congrArg (fun z : ℤ => (z : R)) hZ
    push_cast at this
    exact this
  refine Finset.sum_nbij' (fun x => x.2) (fun S => ⟨S.card, S⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, S⟩ hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_powerset.2 (indicVec_le_iff.1 hx2)
  · intro S hS
    have hSsub : S ⊆ e.support := Finset.mem_powerset.1 hS
    refine Finset.mem_filter.2 ⟨Finset.mem_sigma.2 ⟨Finset.mem_range.2 ?_, ?_⟩,
      indicVec_le_iff.2 hSsub⟩
    · change S.card < n + 1
      have := Finset.card_le_card hSsub
      omega
    · exact Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩
  · rintro ⟨i, S⟩ hx
    obtain ⟨hx1, -⟩ := Finset.mem_filter.1 hx
    obtain ⟨-, hcardS⟩ := Finset.mem_powersetCard.1 (Finset.mem_sigma.1 hx1).2
    change (⟨S.card, S⟩ : (_ : ℕ) × Finset (Fin m)) = ⟨i, S⟩
    rw [hcardS]
  · intro S _
    rfl
  · rintro ⟨i, S⟩ hx
    obtain ⟨hx1, -⟩ := Finset.mem_filter.1 hx
    obtain ⟨-, hcardS⟩ := Finset.mem_powersetCard.1 (Finset.mem_sigma.1 hx1).2
    rw [hcardS]

/-! ### The product of an elementary and a complete homogeneous symmetric polynomial -/

/-- Expansion of `e_i` as a sum of squarefree monomials. -/
lemma esymm_eq_sum_indicVec (i : ℕ) :
    esymm (Fin m) R i
      = ∑ S ∈ Finset.powersetCard i (univ : Finset (Fin m)), monomial (indicVec S) (1 : R) :=
  esymm_eq_sum_monomial (Fin m) R i

/-- Expansion of `e_i * h_r` as a sum of monomials. -/
lemma esymm_mul_hsymm_eq_sum (i r : ℕ) :
    esymm (Fin m) R i * hsymm (Fin m) R r
      = ∑ S ∈ Finset.powersetCard i (univ : Finset (Fin m)),
          ∑ d ∈ Finset.finsuppAntidiag (univ : Finset (Fin m)) r,
            monomial (indicVec S + d) (1 : R) := by
  rw [esymm_eq_sum_indicVec, hsymm_eq_sum_monomial, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun d _ => by
    rw [monomial_mul, mul_one]

/-- Shifting the exponent vectors of degree `n - i` by a `0-1` vector of degree `i`. -/
lemma sum_monomial_shift {S : Finset (Fin m)} {i n : ℕ} (hS : S.card = i) (hi : i ≤ n) :
    ∑ d ∈ Finset.finsuppAntidiag (univ : Finset (Fin m)) (n - i),
        monomial (indicVec S + d) (1 : R)
      = ∑ e ∈ (Finset.finsuppAntidiag (univ : Finset (Fin m)) n).filter
          (fun e => indicVec S ≤ e), monomial e (1 : R) := by
  classical
  refine Finset.sum_nbij' (fun d => indicVec S + d) (fun e => e - indicVec S) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    obtain ⟨hd1, -⟩ := Finset.mem_finsuppAntidiag.1 hd
    refine Finset.mem_filter.2 ⟨Finset.mem_finsuppAntidiag.2 ⟨?_, by simp⟩, le_add_right le_rfl⟩
    change ∑ j, (indicVec S + d) j = n
    have : ∑ j, (indicVec S + d) j = ∑ j, indicVec S j + ∑ j, d j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => rfl
    rw [this, sum_indicVec, hS]
    have : ∑ j, d j = n - i := hd1
    omega
  · intro e he
    obtain ⟨he1, hle⟩ := Finset.mem_filter.1 he
    obtain ⟨he2, -⟩ := Finset.mem_finsuppAntidiag.1 he1
    refine Finset.mem_finsuppAntidiag.2 ⟨?_, by simp⟩
    change ∑ j, (e - indicVec S) j = n - i
    have hpt : ∀ j, (e - indicVec S) j + indicVec S j = e j := by
      intro j
      have := (Finsupp.le_def.1 hle) j
      simp only [Finsupp.tsub_apply]
      omega
    have hsum : ∑ j, (e - indicVec S) j + ∑ j, indicVec S j = ∑ j, e j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => hpt j
    rw [sum_indicVec, hS] at hsum
    have : ∑ j, e j = n := he2
    omega
  · intro d _
    simp
  · intro e he
    obtain ⟨-, hle⟩ := Finset.mem_filter.1 he
    exact add_tsub_cancel_of_le hle
  · intro d _
    rfl

/-! ### The relation -/

/-- **The fundamental relation between `e` and `h`**: for `n ≥ 1`,
`∑_{i=0}^n (-1)^i e_i h_{n-i} = 0`. -/
theorem sum_neg_one_pow_esymm_mul_hsymm (m : ℕ) (R : Type*) [CommRing R] {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range (n + 1),
        (-1 : MvPolynomial (Fin m) R) ^ i * (esymm (Fin m) R i * hsymm (Fin m) R (n - i))
      = 0 := by
  classical
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (-1 : MvPolynomial (Fin m) R) ^ i * (esymm (Fin m) R i * hsymm (Fin m) R (n - i))
        = ∑ S ∈ Finset.powersetCard i (univ : Finset (Fin m)),
            ∑ e ∈ Finset.finsuppAntidiag (univ : Finset (Fin m)) n,
              (if indicVec S ≤ e then
                (-1 : MvPolynomial (Fin m) R) ^ i * monomial e (1 : R) else 0) := by
    intro i hi
    have hile : i ≤ n := by simpa using Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [esymm_mul_hsymm_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    obtain ⟨-, hcardS⟩ := Finset.mem_powersetCard.1 hS
    rw [sum_monomial_shift hcardS hile, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range (n + 1)) =>
    Finset.sum_comm (s := Finset.powersetCard i (univ : Finset (Fin m)))
      (t := Finset.finsuppAntidiag (univ : Finset (Fin m)) n)
      (f := fun S e => if indicVec S ≤ e then
        (-1 : MvPolynomial (Fin m) R) ^ i * monomial e (1 : R) else 0)), Finset.sum_comm]
  refine Finset.sum_eq_zero fun e he => ?_
  obtain ⟨hesum, -⟩ := Finset.mem_finsuppAntidiag.1 he
  have hesum' : ∑ j, e j = n := hesum
  have hzero := sum_neg_one_pow_card_subsets (R := MvPolynomial (Fin m) R) hesum' hn
  calc ∑ i ∈ Finset.range (n + 1), ∑ S ∈ Finset.powersetCard i (univ : Finset (Fin m)),
        (if indicVec S ≤ e then
          (-1 : MvPolynomial (Fin m) R) ^ i * monomial e (1 : R) else 0)
      = (∑ i ∈ Finset.range (n + 1), ∑ S ∈ Finset.powersetCard i (univ : Finset (Fin m)),
            (if indicVec S ≤ e then ((-1 : MvPolynomial (Fin m) R)) ^ i else 0))
          * monomial e (1 : R) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun S _ => by split_ifs <;> simp
    _ = 0 := by rw [hzero, zero_mul]

end MvPolynomial
