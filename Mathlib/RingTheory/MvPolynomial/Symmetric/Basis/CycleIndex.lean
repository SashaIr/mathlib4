/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.GroupTheory.Perm.SymmetricGroup.CycleType
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Alternant.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.PowerSum
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.Tactic.FieldSimp

/-!
# The cycle index formula

Following `theories/MPoly/permcent.v` and `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove the expansion of the complete
homogeneous symmetric polynomial in the power sums,

`h_n = ∑_{μ ⊢ n} p_μ / z_μ`,

where `z_μ` is the integer of `Mathlib/GroupTheory/Perm/SymmetricGroup/CycleType.lean`,
that is, the order of the centralizer of a permutation of cycle type `μ`.  Equivalently, `n ! ·
h_n` is the sum over the permutations of `Fin n` of the power sums attached to their cycle types.

The proof goes through the recursion `n · h_n = ∑_{r = 1}^{n} p_r · h_{n - r}`, obtained by
comparing coefficients, and the matching recursion for `∑_μ p_μ / z_μ`, which comes
from the fact that removing one part `r` from `μ` divides `z_μ` by `r · m_r(μ)`.

## Main results

* `MvPolynomial.nsmul_hsymm_eq_sum_psum_mul_hsymm` : the recursion `n · h_n = ∑_r p_r · h_{n-r}`.
* `Young.zcard_dropPart` : `z_μ = r · m_r(μ) · z_{μ ∖ r}`.
* `MvPolynomial.cycleIndexSum` : the sum `∑_{μ ⊢ n} p_μ / z_μ`.
* `MvPolynomial.hsymm_eq_cycleIndexSum` : the cycle index formula `h_n = ∑_{μ ⊢ n} p_μ / z_μ`.
* `MvPolynomial.factorial_nsmul_hsymm_eq_sum_perm` : `n ! · h_n = ∑_{σ ∈ S_n} p_{cycleType σ}`.
* `MvPolynomial.nsmul_esymm_eq_sum_psum_mul_esymm` : Newton's identity in the recursive form
  `n · e_n = ∑_{r=1}^{n} (-1)^{r+1} p_r · e_{n-r}`, deduced from Mathlib's Newton identities.
* `MvPolynomial.esymm_eq_signedCycleIndexSum` : the signed cycle index formula
  `e_n = ∑_{μ ⊢ n} (-1)^{n - ℓ(μ)} p_μ / z_μ`.
* `MvPolynomial.sum_signed_inv_zcard` : `∑_{μ ⊢ n} (-1)^{n - ℓ(μ)} / z_μ = 0` for `n ≥ 2`.
-/

@[expose] public section

open List Young

namespace MvPolynomial

open MvPolynomial

/-! ### The coefficients of `h_n` and of `p_r · h_{n-r}` -/

variable {m : ℕ} {R : Type*} [CommRing R]

/-- The complete homogeneous symmetric polynomial is the sum of all monomials of the given
degree, each with coefficient one. -/
lemma coeff_hsymm (m n : ℕ) (R : Type*) [CommRing R] (d : Fin m →₀ ℕ) :
    coeff d (hsymm (Fin m) R n) = if ∑ i, d i = n then 1 else 0 := by
  classical
  rw [hsymm_eq_sum_monomial, coeff_sum,
    Finset.sum_congr rfl (fun e _ => coeff_monomial d e (1 : R)),
    Finset.sum_ite_eq' (Finset.finsuppAntidiag (Finset.univ : Finset (Fin m)) n) d
      (fun _ => (1 : R))]
  by_cases h : ∑ i, d i = n
  · rw [ite_eq_left h, ite_eq_left (Finset.mem_finsuppAntidiag.2 ⟨h, Finset.subset_univ _⟩)]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h (Finset.mem_finsuppAntidiag.1 hc).1)]

/-- The coefficients of `p_r · h_{n-r}`: the monomials of degree `n` occur with multiplicity
the number of variables whose exponent is at least `r`. -/
lemma coeff_psum_mul_hsymm (m n r : ℕ) (R : Type*) [CommRing R] (hr : r ≤ n)
    (d : Fin m →₀ ℕ) :
    coeff d (psum (Fin m) R r * hsymm (Fin m) R (n - r))
      = if ∑ i, d i = n then ((Finset.univ.filter fun i : Fin m => r ≤ d i).card : R) else 0 := by
  classical
  have hpsum : psum (Fin m) R r = ∑ i : Fin m, monomial (Finsupp.single i r) (1 : R) := by
    rw [psum]
    exact Finset.sum_congr rfl fun i _ => by rw [X_pow_eq_monomial]
  rw [hpsum, Finset.sum_mul, coeff_sum]
  have hterm : ∀ i : Fin m,
      coeff d (monomial (Finsupp.single i r) (1 : R) * hsymm (Fin m) R (n - r))
        = if r ≤ d i ∧ ∑ j, d j = n then 1 else 0 := by
    intro i
    rw [coeff_monomial_mul', one_mul]
    by_cases hi : r ≤ d i
    · rw [ite_eq_left (Finsupp.single_le_iff.2 hi), coeff_hsymm]
      have hsum : ∑ j, (d - Finsupp.single i r) j = (∑ j, d j) - r := by
        rw [← Finset.add_sum_erase _ (fun j => (d - Finsupp.single i r) j) (Finset.mem_univ i),
          ← Finset.add_sum_erase _ (fun j => d j) (Finset.mem_univ i)]
        have he : ∑ j ∈ Finset.univ.erase i, (d - Finsupp.single i r) j
            = ∑ j ∈ Finset.univ.erase i, d j :=
          Finset.sum_congr rfl fun j hj => by
            have hne : j ≠ i := (Finset.mem_erase.1 hj).1
            have hz : (Finsupp.single i r : Fin m →₀ ℕ) j = 0 := by
              rw [Finsupp.single_apply, ite_eq_right fun h : i = j => hne h.symm]
            simp [hz]
        have hpti : (d - Finsupp.single i r) i = d i - r := by simp
        rw [he, hpti]
        omega
      rw [hsum]
      have hri : r ≤ ∑ j, d j := le_trans hi (Finset.single_le_sum (f := fun j => d j)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
      by_cases hd : ∑ j, d j = n
      · rw [ite_eq_left (show ∑ j, d j - r = n - r by rw [hd]), ite_eq_left ⟨hi, hd⟩]
      · rw [ite_eq_right (show ¬ (∑ j, d j - r = n - r) by omega), ite_eq_right (fun hc => hd hc.2)]
    · rw [ite_eq_right (fun hc => hi (Finsupp.single_le_iff.1 hc)),
        ite_eq_right (fun hc => hi hc.1)]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  by_cases hd : ∑ j, d j = n
  · have hsimp : ∀ i : Fin m, (if r ≤ d i ∧ ∑ j, d j = n then (1 : R) else 0)
        = if r ≤ d i then (1 : R) else 0 := by
      intro i
      by_cases hi : r ≤ d i
      · rw [ite_eq_left ⟨hi, hd⟩, ite_eq_left hi]
      · rw [ite_eq_right (fun hc => hi hc.1), ite_eq_right hi]
    rw [ite_eq_left hd, Finset.sum_congr rfl fun i _ => hsimp i, Finset.sum_boole]
  · rw [ite_eq_right hd, Finset.sum_eq_zero fun i _ => ite_eq_right fun hc => hd hc.2]

/-- Counting, for each variable, the thresholds it exceeds. -/
lemma sum_card_le_eq_sum (m n : ℕ) {d : Fin m →₀ ℕ} (hd : ∑ i, d i = n) :
    ∑ r ∈ Finset.Icc 1 n, ((Finset.univ.filter fun i : Fin m => r ≤ d i).card : ℕ) = n := by
  classical
  have hle : ∀ i : Fin m, d i ≤ n := by
    intro i
    rw [← hd]
    exact Finset.single_le_sum (f := fun j => d j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hcard : ∀ r : ℕ, ((Finset.univ.filter fun i : Fin m => r ≤ d i).card : ℕ)
      = ∑ i : Fin m, if r ≤ d i then 1 else 0 := fun r => Finset.card_filter _ _
  rw [Finset.sum_congr rfl fun r _ => hcard r, Finset.sum_comm]
  have hinner : ∀ i : Fin m, (∑ r ∈ Finset.Icc 1 n, if r ≤ d i then 1 else 0) = d i := by
    intro i
    rw [← Finset.card_filter]
    have hfilter : (Finset.Icc 1 n).filter (fun r => r ≤ d i) = Finset.Icc 1 (d i) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_Icc]
      have := hle i
      omega
    rw [hfilter, Nat.card_Icc]
    omega
  rw [Finset.sum_congr rfl fun i _ => hinner i, hd]

/-- **The recursion for the complete homogeneous symmetric polynomials**:
`n · h_n = ∑_{r = 1}^{n} p_r · h_{n-r}`. -/
theorem nsmul_hsymm_eq_sum_psum_mul_hsymm (m n : ℕ) (R : Type*) [CommRing R] :
    (n : ℕ) • hsymm (Fin m) R n
      = ∑ r ∈ Finset.Icc 1 n, psum (Fin m) R r * hsymm (Fin m) R (n - r) := by
  classical
  ext d
  rw [coeff_smul, coeff_hsymm, coeff_sum,
    Finset.sum_congr rfl fun r hr => coeff_psum_mul_hsymm m n r R (Finset.mem_Icc.1 hr).2 d]
  by_cases hd : ∑ i, d i = n
  · rw [ite_eq_left hd, Finset.sum_congr rfl fun r _ => ite_eq_left hd, nsmul_eq_mul, mul_one,
      ← Nat.cast_sum, sum_card_le_eq_sum m n hd]
  · rw [ite_eq_right hd, Finset.sum_eq_zero fun r _ => ite_eq_right hd, smul_zero]

end MvPolynomial

namespace Young

/-! ### Removing one part from a partition -/

/-- `z_μ` may be computed over any finite set of values containing the parts. -/
lemma zcard_eq_prod_of_subset {l : List ℕ} {s : Finset ℕ} (h : l.toFinset ⊆ s) :
    zcard l = ∏ i ∈ s, i ^ l.count i * Nat.factorial (l.count i) := by
  classical
  rw [zcard]
  refine Finset.prod_subset h fun i _ hi => ?_
  have hc : l.count i = 0 := List.count_eq_zero.2 fun hmem => hi (List.mem_toFinset.2 hmem)
  rw [hc]
  simp

/-- The partition obtained by removing one part equal to `r` from `μ`. -/
noncomputable def dropPart (μ : List ℕ) (r : ℕ) : List ℕ := sortDesc ((μ : Multiset ℕ).erase r)

@[simp] lemma coe_dropPart (μ : List ℕ) (r : ℕ) :
    (dropPart μ r : Multiset ℕ) = (μ : Multiset ℕ).erase r := coe_sortDesc _

lemma isPart_dropPart {μ : List ℕ} (hμ : IsPart μ) (r : ℕ) : IsPart (dropPart μ r) := by
  refine isPart_sortDesc fun i hi => hμ.pos_of_mem ?_
  have := Multiset.mem_of_mem_erase hi
  simpa using this

lemma count_dropPart (μ : List ℕ) (r i : ℕ) :
    (dropPart μ r).count i = if i = r then μ.count i - 1 else μ.count i := by
  have h := congrArg (Multiset.count i) (coe_dropPart μ r)
  rw [Multiset.coe_count] at h
  rw [h]
  by_cases hi : i = r
  · subst hi
    rw [ite_eq_left rfl, Multiset.count_erase_self, Multiset.coe_count]
  · rw [ite_eq_right hi, Multiset.count_erase_of_ne hi, Multiset.coe_count]

lemma sum_dropPart {μ : List ℕ} {r : ℕ} (hr : r ∈ μ) : (dropPart μ r).sum + r = μ.sum := by
  have hmem : r ∈ (μ : Multiset ℕ) := by simpa using hr
  have h : (r ::ₘ ((μ : Multiset ℕ).erase r)) = (μ : Multiset ℕ) := Multiset.cons_erase hmem
  have hsum := congrArg Multiset.sum h
  rw [Multiset.sum_cons] at hsum
  have hd : (dropPart μ r).sum = ((μ : Multiset ℕ).erase r).sum := by
    rw [← Multiset.sum_coe, coe_dropPart]
  rw [hd, ← Multiset.sum_coe μ]
  omega

lemma toFinset_dropPart_subset (μ : List ℕ) (r : ℕ) :
    (dropPart μ r).toFinset ⊆ μ.toFinset := by
  intro i hi
  rw [List.mem_toFinset] at hi ⊢
  have hi' : i ∈ (dropPart μ r : Multiset ℕ) := by
    exact (Multiset.mem_coe).2 hi
  rw [coe_dropPart] at hi'
  exact (Multiset.mem_coe).1 (Multiset.mem_of_mem_erase hi')

/-- **Removing one part `r` divides `z_μ` by `r · m_r(μ)`.** -/
lemma zcard_dropPart {μ : List ℕ} {r : ℕ} (hr : r ∈ μ) :
    zcard μ = r * μ.count r * zcard (dropPart μ r) := by
  classical
  have hrs : r ∈ μ.toFinset := List.mem_toFinset.2 hr
  have h1 : zcard μ = ∏ i ∈ μ.toFinset, i ^ μ.count i * Nat.factorial (μ.count i) :=
    zcard_eq_prod_of_subset (Finset.Subset.refl _)
  have h2 : zcard (dropPart μ r)
      = ∏ i ∈ μ.toFinset,
          i ^ (dropPart μ r).count i * Nat.factorial ((dropPart μ r).count i) :=
    zcard_eq_prod_of_subset (toFinset_dropPart_subset μ r)
  have htail : ∏ i ∈ μ.toFinset.erase r,
        i ^ (dropPart μ r).count i * Nat.factorial ((dropPart μ r).count i)
      = ∏ i ∈ μ.toFinset.erase r, i ^ μ.count i * Nat.factorial (μ.count i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [count_dropPart, ite_eq_right (Finset.mem_erase.1 hi).1]
  have hc : μ.count r ≠ 0 := by
    rw [ne_eq, List.count_eq_zero, not_not]
    exact hr
  obtain ⟨k, hk⟩ : ∃ k, μ.count r = k + 1 := ⟨μ.count r - 1, by omega⟩
  rw [h1, h2, ← Finset.mul_prod_erase _ _ hrs, ← Finset.mul_prod_erase _ _ hrs, htail,
    count_dropPart, ite_eq_left rfl, hk]
  simp only [Nat.add_sub_cancel]
  rw [pow_succ, Nat.factorial_succ]
  ring

/-- The total size of a partition, counted by distinct parts. -/
lemma sum_count_mul_self (μ : List ℕ) : ∑ i ∈ μ.toFinset, μ.count i * i = μ.sum := by
  classical
  have h := Finset.sum_multiset_map_count (μ : Multiset ℕ) (fun i : ℕ => i)
  rw [Multiset.map_id'] at h
  rw [← Multiset.sum_coe μ, h]
  refine Finset.sum_congr ?_ fun i _ => ?_
  · simp
  · rw [smul_eq_mul, Multiset.coe_count]

/-- `z_μ` only depends on the multiset of parts. -/
lemma zcard_of_perm {l l' : List ℕ} (h : l.Perm l') : zcard l = zcard l' := by
  classical
  rw [zcard, zcard, List.toFinset_eq_of_perm l l' h]
  exact Finset.prod_congr rfl fun i _ => by rw [h.count_eq]

/-- Adding one part `r` to the partition `μ`. -/
noncomputable def insPart (μ : List ℕ) (r : ℕ) : List ℕ :=
  sortDesc (r ::ₘ (μ : Multiset ℕ))

@[simp] lemma coe_insPart (μ : List ℕ) (r : ℕ) :
    (insPart μ r : Multiset ℕ) = r ::ₘ (μ : Multiset ℕ) := coe_sortDesc _

lemma insPart_perm (μ : List ℕ) (r : ℕ) : (insPart μ r).Perm (r :: μ) :=
  Quotient.exact (coe_insPart μ r)

lemma isPart_insPart {μ : List ℕ} (hμ : IsPart μ) {r : ℕ} (hr : 0 < r) :
    IsPart (insPart μ r) := by
  refine isPart_sortDesc fun i hi => ?_
  rcases Multiset.mem_cons.1 hi with rfl | hi
  · exact hr
  · exact hμ.pos_of_mem (by simpa using hi)

@[simp] lemma sum_insPart (μ : List ℕ) (r : ℕ) : (insPart μ r).sum = r + μ.sum := by
  rw [insPart, sum_sortDesc, Multiset.sum_cons, Multiset.sum_coe]

lemma mem_insPart_self (μ : List ℕ) (r : ℕ) : r ∈ insPart μ r := by
  rw [insPart, mem_sortDesc]
  exact Multiset.mem_cons_self _ _

lemma dropPart_insPart {μ : List ℕ} (hμ : IsPart μ) (r : ℕ) :
    dropPart (insPart μ r) r = μ := by
  rw [dropPart, coe_insPart, Multiset.erase_cons_head, sortDesc_coe hμ]

lemma insPart_dropPart {μ : List ℕ} (hμ : IsPart μ) {r : ℕ} (hr : r ∈ μ) :
    insPart (dropPart μ r) r = μ := by
  rw [insPart, coe_dropPart, Multiset.cons_erase (by simpa using hr), sortDesc_coe hμ]
end Young

namespace MvPolynomial


/-! ### The product of power sums, and adding a part -/

lemma pProd_cons (m : ℕ) (R : Type*) [CommRing R] (r : ℕ) (μ : List ℕ) :
    pProd m R (r :: μ) = psum (Fin m) R r * pProd m R μ := by
  rw [pProd, pProd, List.map_cons, List.prod_cons]

lemma pProd_of_perm (m : ℕ) (R : Type*) [CommRing R] {l l' : List ℕ} (h : l.Perm l') :
    pProd m R l = pProd m R l' :=
  List.Perm.prod_eq (h.map _)

lemma pProd_insPart (m : ℕ) (R : Type*) [CommRing R] (μ : List ℕ) (r : ℕ) :
    pProd m R (insPart μ r) = psum (Fin m) R r * pProd m R μ := by
  rw [pProd_of_perm m R (insPart_perm μ r), pProd_cons]

/-! ### The cycle index formula -/

/-- The sum `∑_{μ ⊢ n} p_μ / z_μ`. -/
noncomputable def cycleIndexSum (m : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    MvPolynomial (Fin m) R :=
  ∑ μ ∈ partFinset n, ((zcard μ : ℚ))⁻¹ • pProd m R μ

end MvPolynomial

namespace Young

/-- The scalar identity behind the recursion: the reciprocals of the `z`'s of the partitions
obtained by removing one part sum up to `n / z_μ`. -/
lemma sum_inv_zcard_dropPart {μ : List ℕ} (hμ : IsPart μ) :
    ∑ r ∈ μ.toFinset, ((zcard (dropPart μ r) : ℚ))⁻¹
      = (μ.sum : ℚ) * ((zcard μ : ℚ))⁻¹ := by
  classical
  have hterm : ∀ r ∈ μ.toFinset,
      ((zcard (dropPart μ r) : ℚ))⁻¹ = (μ.count r * r : ℕ) * ((zcard μ : ℚ))⁻¹ := by
    intro r hr
    have hrm : r ∈ μ := List.mem_toFinset.1 hr
    have hd : (zcard μ : ℚ) = ((r * μ.count r : ℕ) : ℚ) * (zcard (dropPart μ r) : ℚ) := by
      rw [← Nat.cast_mul]
      exact_mod_cast congrArg (fun k : ℕ => (k : ℚ)) (zcard_dropPart hrm)
    have hdz : (zcard (dropPart μ r) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.2 (zcard_pos (isPart_dropPart hμ r)).ne'
    have hrz : ((r * μ.count r : ℕ) : ℚ) ≠ 0 := by
      have hpos : 0 < r := hμ.pos_of_mem hrm
      have hc : μ.count r ≠ 0 := by
        rw [ne_eq, List.count_eq_zero, not_not]; exact hrm
      exact Nat.cast_ne_zero.2 (by positivity)
    rw [hd, mul_inv]
    push_cast at hrz ⊢
    field_simp
    exact (div_self (by rw [mul_comm]; exact hrz)).symm
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Nat.cast_sum, sum_count_mul_self]

end Young

namespace MvPolynomial

/-- **The recursion for `∑_μ p_μ / z_μ`**. -/
lemma sum_psum_mul_cycleIndexSum (m : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    ∑ r ∈ Finset.Icc 1 n, psum (Fin m) R r * cycleIndexSum m R (n - r)
      = (n : ℚ) • cycleIndexSum m R n := by
  classical
  have hL : ∑ r ∈ Finset.Icc 1 n, psum (Fin m) R r * cycleIndexSum m R (n - r)
      = ∑ x ∈ (Finset.Icc 1 n).sigma (fun r => partFinset (n - r)),
          ((zcard x.2 : ℚ))⁻¹ • pProd m R (insPart x.2 x.1) := by
    rw [← Finset.sum_sigma' (Finset.Icc 1 n) (fun r => partFinset (n - r))
      (fun r ν => ((zcard ν : ℚ))⁻¹ • pProd m R (insPart ν r))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [cycleIndexSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by rw [pProd_insPart, mul_smul_comm]
  have hR : (n : ℚ) • cycleIndexSum m R n
      = ∑ y ∈ (partFinset n).sigma (fun μ => μ.toFinset),
          ((zcard (dropPart y.1 y.2) : ℚ))⁻¹ • pProd m R y.1 := by
    rw [← Finset.sum_sigma' (partFinset n) (fun μ => μ.toFinset)
      (fun μ r => ((zcard (dropPart μ r) : ℚ))⁻¹ • pProd m R μ),
      cycleIndexSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hμ
    rw [← Finset.sum_smul, sum_inv_zcard_dropPart hpart, hsum, smul_smul]
  rw [hL, hR]
  refine Finset.sum_nbij' (i := fun x => (⟨insPart x.2 x.1, x.1⟩ : (_ : List ℕ) × ℕ))
    (j := fun y => (⟨y.2, dropPart y.1 y.2⟩ : (_ : ℕ) × List ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨r, ν⟩ hx
    simp only [Finset.mem_sigma] at hx ⊢
    obtain ⟨hr, hν⟩ := hx
    obtain ⟨hνpart, hνsum⟩ := mem_partFinset.1 hν
    rw [Finset.mem_Icc] at hr
    refine ⟨mem_partFinset.2 ⟨isPart_insPart hνpart hr.1, ?_⟩, ?_⟩
    · rw [sum_insPart, hνsum]; omega
    · exact List.mem_toFinset.2 (mem_insPart_self ν r)
  · rintro ⟨μ, r⟩ hy
    simp only [Finset.mem_sigma] at hy ⊢
    obtain ⟨hμ, hr⟩ := hy
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hμ
    have hrm : r ∈ μ := List.mem_toFinset.1 hr
    have hpos : 0 < r := hpart.pos_of_mem hrm
    have hsd := sum_dropPart hrm
    refine ⟨Finset.mem_Icc.2 ⟨hpos, by omega⟩, mem_partFinset.2 ⟨isPart_dropPart hpart r, ?_⟩⟩
    omega
  · rintro ⟨r, ν⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hνpart, -⟩ := mem_partFinset.1 hx.2
    simp only [dropPart_insPart hνpart]
  · rintro ⟨μ, r⟩ hy
    rw [Finset.mem_sigma] at hy
    obtain ⟨hpart, -⟩ := mem_partFinset.1 hy.1
    have hrm : r ∈ μ := List.mem_toFinset.1 hy.2
    simp only [insPart_dropPart hpart hrm]
  · rintro ⟨r, ν⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hνpart, -⟩ := mem_partFinset.1 hx.2
    rw [dropPart_insPart hνpart]

/-- **The cycle index formula** : `h_n = ∑_{μ ⊢ n} p_μ / z_μ`. -/
theorem hsymm_eq_cycleIndexSum (m : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    hsymm (Fin m) R n = cycleIndexSum m R n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [cycleIndexSum, partFinset_zero, Finset.sum_singleton, pProd_nil, hsymm_zero]
      norm_num [zcard]
    · have hrec := nsmul_hsymm_eq_sum_psum_mul_hsymm m n R
      have hterm : ∀ r ∈ Finset.Icc 1 n,
          psum (Fin m) R r * hsymm (Fin m) R (n - r)
            = psum (Fin m) R r * cycleIndexSum m R (n - r) := by
        intro r hr
        rw [Finset.mem_Icc] at hr
        rw [ih (n - r) (by omega)]
      rw [Finset.sum_congr rfl hterm, sum_psum_mul_cycleIndexSum] at hrec
      have hq : (n : ℚ) • hsymm (Fin m) R n = (n : ℚ) • cycleIndexSum m R n := by
        rw [← hrec, ← Nat.cast_smul_eq_nsmul ℚ]
      exact smul_right_injective _ (Nat.cast_ne_zero.2 hn.ne' : (n : ℚ) ≠ 0) hq

/-- **The cycle index of the symmetric group**: `n ! · h_n` is the sum, over all the
permutations of `Fin n`, of the power sum products attached to their cycle types. -/
theorem factorial_nsmul_hsymm_eq_sum_perm (m n : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] :
    Nat.factorial n • hsymm (Fin m) R n
      = ∑ σ : Equiv.Perm (Fin n), pProd m R (Equiv.Perm.cycleTypeList σ) := by
  classical
  have hfib : ∑ σ : Equiv.Perm (Fin n), pProd m R (Equiv.Perm.cycleTypeList σ)
      = ∑ μ ∈ partFinset n,
          (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
            Equiv.Perm.cycleTypeList σ = μ).card • pProd m R μ := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun σ _ => Equiv.Perm.cycleTypeList_mem_partFinset σ)
      (fun σ => pProd m R (Equiv.Perm.cycleTypeList σ))]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_congr rfl fun σ hσ => by
      rw [(Finset.mem_filter.1 hσ).2], Finset.sum_const]
  rw [hfib, hsymm_eq_cycleIndexSum, cycleIndexSum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hμ
  have hz : (zcard μ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (zcard_pos hpart).ne'
  have hcard : ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
      Equiv.Perm.cycleTypeList σ = μ).card : ℚ)
      = (Nat.factorial n : ℚ) * ((zcard μ : ℚ))⁻¹ := by
    field_simp
    exact_mod_cast Equiv.Perm.card_cycleTypeList_mul_zcard hpart hsum
  rw [smul_comm, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, hcard, smul_smul,
    mul_comm]

/-! ### The signed cycle index formula for the elementary symmetric polynomials -/

/-- **Newton's identity**, in the recursive form
`n · e_n = ∑_{r = 1}^{n} (-1)^{r+1} p_r · e_{n-r}`. -/
theorem nsmul_esymm_eq_sum_psum_mul_esymm (m n : ℕ) (R : Type*) [CommRing R] :
    (n : ℕ) • esymm (Fin m) R n
      = ∑ r ∈ Finset.Icc 1 n,
          (-1 : MvPolynomial (Fin m) R) ^ (r + 1)
            * (psum (Fin m) R r * esymm (Fin m) R (n - r)) := by
  classical
  have h := MvPolynomial.mul_esymm_eq_sum (Fin m) R n
  rw [nsmul_eq_mul, h, Finset.mul_sum]
  refine Finset.sum_nbij' (i := fun a : ℕ × ℕ => a.2) (j := fun r : ℕ => (n - r, r)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ ha
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha
    simp only [Finset.mem_Icc]
    omega
  · intro r hr
    simp only [Finset.mem_Icc] at hr
    simp only [Finset.mem_filter, Finset.mem_antidiagonal]
    omega
  · rintro ⟨a, b⟩ ha
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha
    have hb : n - b = a := by omega
    simp [hb]
  · intro r _
    simp
  · rintro ⟨a, b⟩ ha
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha
    have hb : n - b = a := by omega
    have hsign : (-1 : MvPolynomial (Fin m) R) ^ (n + 1) * (-1) ^ a = (-1) ^ (b + 1) := by
      rw [← pow_add, neg_one_pow_eq_pow_mod_two]
      have hmod : (n + 1 + a) % 2 = (b + 1) % 2 := by omega
      rw [hmod, ← neg_one_pow_eq_pow_mod_two]
    rw [hb, ← mul_assoc, ← mul_assoc, hsign, mul_assoc, mul_comm (esymm (Fin m) R a)]

/-- Multiplying by the rational sign is the same as multiplying by the sign in the ring. -/
lemma rat_neg_one_pow_smul (m k : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R]
    (x : MvPolynomial (Fin m) R) :
    ((-1 : ℚ) ^ k) • x = (-1 : MvPolynomial (Fin m) R) ^ k * x := by
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow, h.neg_one_pow, one_smul, one_mul]
  · rw [h.neg_one_pow, h.neg_one_pow, neg_one_smul, neg_one_mul]

/-- The signed sum `∑_{μ ⊢ n} (-1)^{n - ℓ(μ)} p_μ / z_μ`.  The sign is written as
`(-1)^{n + ℓ(μ)}`, which avoids a truncated subtraction and has the same parity. -/
noncomputable def signedCycleIndexSum (m : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    MvPolynomial (Fin m) R :=
  ∑ μ ∈ partFinset n, (((-1 : ℚ) ^ (n + μ.length)) * ((zcard μ : ℚ))⁻¹) • pProd m R μ

/-- **The recursion for `∑_μ ± p_μ / z_μ`**. -/
lemma sum_psum_mul_signedCycleIndexSum (m : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    ∑ r ∈ Finset.Icc 1 n,
        ((-1 : ℚ) ^ (r + 1)) • (psum (Fin m) R r * signedCycleIndexSum m R (n - r))
      = (n : ℚ) • signedCycleIndexSum m R n := by
  classical
  have hL : ∑ r ∈ Finset.Icc 1 n,
        ((-1 : ℚ) ^ (r + 1)) • (psum (Fin m) R r * signedCycleIndexSum m R (n - r))
      = ∑ x ∈ (Finset.Icc 1 n).sigma (fun r => partFinset (n - r)),
          (((-1 : ℚ) ^ (x.1 + 1)) * (((-1 : ℚ) ^ ((n - x.1) + x.2.length))
            * ((zcard x.2 : ℚ))⁻¹)) • pProd m R (insPart x.2 x.1) := by
    rw [← Finset.sum_sigma' (Finset.Icc 1 n) (fun r => partFinset (n - r))
      (fun r ν => (((-1 : ℚ) ^ (r + 1)) * (((-1 : ℚ) ^ ((n - r) + ν.length))
        * ((zcard ν : ℚ))⁻¹)) • pProd m R (insPart ν r))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [signedCycleIndexSum, Finset.mul_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun ν _ => by
      rw [pProd_insPart, mul_smul_comm, smul_smul]
  have hR : (n : ℚ) • signedCycleIndexSum m R n
      = ∑ y ∈ (partFinset n).sigma (fun μ => μ.toFinset),
          (((-1 : ℚ) ^ (n + y.1.length)) * ((zcard (dropPart y.1 y.2) : ℚ))⁻¹)
            • pProd m R y.1 := by
    rw [← Finset.sum_sigma' (partFinset n) (fun μ => μ.toFinset)
      (fun μ r => (((-1 : ℚ) ^ (n + μ.length)) * ((zcard (dropPart μ r) : ℚ))⁻¹)
        • pProd m R μ),
      signedCycleIndexSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hμ
    rw [← Finset.sum_smul, ← Finset.mul_sum, sum_inv_zcard_dropPart hpart, hsum, smul_smul]
    ring_nf
  rw [hL, hR]
  refine Finset.sum_nbij' (i := fun x => (⟨insPart x.2 x.1, x.1⟩ : (_ : List ℕ) × ℕ))
    (j := fun y => (⟨y.2, dropPart y.1 y.2⟩ : (_ : ℕ) × List ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨r, ν⟩ hx
    simp only [Finset.mem_sigma] at hx ⊢
    obtain ⟨hr, hν⟩ := hx
    obtain ⟨hνpart, hνsum⟩ := mem_partFinset.1 hν
    rw [Finset.mem_Icc] at hr
    refine ⟨mem_partFinset.2 ⟨isPart_insPart hνpart hr.1, ?_⟩, ?_⟩
    · rw [sum_insPart, hνsum]; omega
    · exact List.mem_toFinset.2 (mem_insPart_self ν r)
  · rintro ⟨μ, r⟩ hy
    simp only [Finset.mem_sigma] at hy ⊢
    obtain ⟨hμ, hr⟩ := hy
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hμ
    have hrm : r ∈ μ := List.mem_toFinset.1 hr
    have hpos : 0 < r := hpart.pos_of_mem hrm
    have hsd := sum_dropPart hrm
    refine ⟨Finset.mem_Icc.2 ⟨hpos, by omega⟩, mem_partFinset.2 ⟨isPart_dropPart hpart r, ?_⟩⟩
    omega
  · rintro ⟨r, ν⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hνpart, -⟩ := mem_partFinset.1 hx.2
    simp only [dropPart_insPart hνpart]
  · rintro ⟨μ, r⟩ hy
    rw [Finset.mem_sigma] at hy
    obtain ⟨hpart, -⟩ := mem_partFinset.1 hy.1
    have hrm : r ∈ μ := List.mem_toFinset.1 hy.2
    simp only [insPart_dropPart hpart hrm]
  · rintro ⟨r, ν⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx
    obtain ⟨hr, hν⟩ := hx
    obtain ⟨hνpart, -⟩ := mem_partFinset.1 hν
    have hlen : (insPart ν r).length = ν.length + 1 := by
      have hcard : ((insPart ν r : List ℕ) : Multiset ℕ).card = (insPart ν r).length :=
        Multiset.coe_card _
      rw [coe_insPart, Multiset.card_cons] at hcard
      simp only [Multiset.coe_card] at hcard
      omega
    have hsign : ((-1 : ℚ) ^ (r + 1)) * ((-1 : ℚ) ^ ((n - r) + ν.length))
        = (-1 : ℚ) ^ (n + (insPart ν r).length) := by
      rw [← pow_add, hlen, neg_one_pow_eq_pow_mod_two]
      have hmod : (r + 1 + (n - r + ν.length)) % 2 = (n + (ν.length + 1)) % 2 := by omega
      rw [hmod, ← neg_one_pow_eq_pow_mod_two]
    rw [dropPart_insPart hνpart, ← mul_assoc, hsign]

/-- **The signed cycle index formula** : `e_n = ∑_{μ ⊢ n} (-1)^{n - ℓ(μ)} p_μ / z_μ`. -/
theorem esymm_eq_signedCycleIndexSum (m : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    esymm (Fin m) R n = signedCycleIndexSum m R n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [signedCycleIndexSum, partFinset_zero, Finset.sum_singleton, pProd_nil, esymm_zero]
      norm_num [zcard]
    · have hrec := nsmul_esymm_eq_sum_psum_mul_esymm m n R
      have hterm : ∀ r ∈ Finset.Icc 1 n,
          (-1 : MvPolynomial (Fin m) R) ^ (r + 1) * (psum (Fin m) R r * esymm (Fin m) R (n - r))
            = ((-1 : ℚ) ^ (r + 1)) • (psum (Fin m) R r * signedCycleIndexSum m R (n - r)) := by
        intro r hr
        rw [Finset.mem_Icc] at hr
        rw [ih (n - r) (by omega), rat_neg_one_pow_smul]
      rw [Finset.sum_congr rfl hterm, sum_psum_mul_signedCycleIndexSum] at hrec
      have hq : (n : ℚ) • esymm (Fin m) R n = (n : ℚ) • signedCycleIndexSum m R n := by
        rw [← hrec, ← Nat.cast_smul_eq_nsmul ℚ]
      exact smul_right_injective _ (Nat.cast_ne_zero.2 hn.ne' : (n : ℚ) ≠ 0) hq

/-! ### A numerical consequence: the signed sum of the `1 / z_μ` -/

lemma psum_one_var (R : Type*) [CommRing R] (r : ℕ) : psum (Fin 1) R r = X 0 ^ r := by
  simp [psum]

lemma pProd_one_var (R : Type*) [CommRing R] (μ : List ℕ) :
    pProd 1 R μ = X 0 ^ μ.sum := by
  induction μ with
  | nil => simp
  | cons r t ih => rw [pProd_cons, ih, psum_one_var, List.sum_cons, pow_add]

lemma esymm_fin_one_eq_zero (R : Type*) [CommRing R] {n : ℕ} (hn : 1 < n) :
    esymm (Fin 1) R n = 0 := by
  rw [esymm, Finset.powersetCard_eq_empty.2 (by simpa using hn), Finset.sum_empty]

/-- The signed version of `∑_{μ ⊢ n} 1 / z_μ = 1`: for `n ≥ 2` the partitions of `n`
with an even number of parts and those with an odd number of parts balance out. -/
theorem sum_signed_inv_zcard {n : ℕ} (hn : 1 < n) :
    ∑ μ ∈ partFinset n, ((-1 : ℚ) ^ (n + μ.length)) * ((zcard μ : ℚ))⁻¹ = 0 := by
  have hzero : signedCycleIndexSum 1 ℚ n = 0 :=
    (esymm_eq_signedCycleIndexSum 1 ℚ n).symm.trans (esymm_fin_one_eq_zero ℚ hn)
  have hs : signedCycleIndexSum 1 ℚ n
      = (∑ μ ∈ partFinset n, ((-1 : ℚ) ^ (n + μ.length)) * ((zcard μ : ℚ))⁻¹)
        • (X 0 ^ n : MvPolynomial (Fin 1) ℚ) := by
    rw [signedCycleIndexSum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    obtain ⟨-, hsum⟩ := mem_partFinset.1 hμ
    rw [pProd_one_var, hsum]
  rw [hs] at hzero
  have hcoeff := congrArg (coeff (Finsupp.single (0 : Fin 1) n)) hzero
  simpa [X_pow_eq_monomial, coeff_monomial, smul_eq_mul] using hcoeff

end MvPolynomial
