/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic.FieldSimp
import Mathlib.RingTheory.MvPolynomial.Symmetric.Alternant.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.PowerSum
import Mathlib.GroupTheory.Perm.SymmetricGroup.CycleType

/-!
# The cycle index formula

Following `theories/MPoly/permcent.v` and `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove the expansion of the complete
homogeneous symmetric polynomial in the power sums,

`h_n = ∑_{lam ⊢ n} p_lam / z_lam`,

where `z_lam` is the integer of `Mathlib/GroupTheory/Perm/SymmetricGroup/CycleType.lean`,
that is, the order of the centralizer of a permutation of cycle type `lam`.  Equivalently, `n ! ·
h_n` is the sum over the permutations of `Fin n` of the power sums attached to their cycle types.

The proof goes through the recursion `n · h_n = ∑_{r = 1}^{n} p_r · h_{n - r}`, obtained by
comparing coefficients, and the matching recursion for `∑_lam p_lam / z_lam`, which comes
from the fact that removing one part `r` from `lam` divides `z_lam` by `r · m_r(lam)`.

## Main results

* `MvPolynomial.nsmul_hsymm_eq_sum_psum_mul_hsymm` : the recursion `n · h_n = ∑_r p_r · h_{n-r}`.
* `List.zcard_dropPart` : `z_lam = r · m_r(lam) · z_{lam ∖ r}`.
* `MvPolynomial.cycleIndexSum` : the sum `∑_{lam ⊢ n} p_lam / z_lam`.
* `MvPolynomial.hsymm_eq_cycleIndexSum` : the cycle index formula `h_n = ∑_{lam ⊢ n} p_lam / z_lam`.
* `MvPolynomial.factorial_nsmul_hsymm_eq_sum_perm` : `n ! · h_n = ∑_{σ ∈ S_n} p_{cycleType σ}`.
* `MvPolynomial.nsmul_esymm_eq_sum_psum_mul_esymm` : Newton's identity in the recursive form
  `n · e_n = ∑_{r=1}^{n} (-1)^{r+1} p_r · e_{n-r}`, deduced from Mathlib's Newton identities.
* `MvPolynomial.esymm_eq_signedCycleIndexSum` : the signed cycle index formula
  `e_n = ∑_{lam ⊢ n} (-1)^{n - ℓ(lam)} p_lam / z_lam`.
* `MvPolynomial.sum_signed_inv_zcard` : `∑_{lam ⊢ n} (-1)^{n - ℓ(lam)} / z_lam = 0` for `n ≥ 2`.
-/

open List

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
  · rw [if_pos h, if_pos (Finset.mem_finsuppAntidiag.2 ⟨h, Finset.subset_univ _⟩)]
  · rw [if_neg h, if_neg (fun hc => h (Finset.mem_finsuppAntidiag.1 hc).1)]

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
    · rw [if_pos (Finsupp.single_le_iff.2 hi), coeff_hsymm]
      have hsum : ∑ j, (d - Finsupp.single i r) j = (∑ j, d j) - r := by
        rw [← Finset.add_sum_erase _ (fun j => (d - Finsupp.single i r) j) (Finset.mem_univ i),
          ← Finset.add_sum_erase _ (fun j => d j) (Finset.mem_univ i)]
        have he : ∑ j ∈ Finset.univ.erase i, (d - Finsupp.single i r) j
            = ∑ j ∈ Finset.univ.erase i, d j :=
          Finset.sum_congr rfl fun j hj => by
            have hne : j ≠ i := (Finset.mem_erase.1 hj).1
            have hz : (Finsupp.single i r : Fin m →₀ ℕ) j = 0 := by
              rw [Finsupp.single_apply, if_neg fun h : i = j => hne h.symm]
            simp [hz]
        have hpti : (d - Finsupp.single i r) i = d i - r := by simp
        rw [he, hpti]
        omega
      rw [hsum]
      have hri : r ≤ ∑ j, d j := le_trans hi (Finset.single_le_sum (f := fun j => d j)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
      by_cases hd : ∑ j, d j = n
      · rw [if_pos (show ∑ j, d j - r = n - r by rw [hd]), if_pos ⟨hi, hd⟩]
      · rw [if_neg (show ¬ (∑ j, d j - r = n - r) by omega), if_neg (fun hc => hd hc.2)]
    · rw [if_neg (fun hc => hi (Finsupp.single_le_iff.1 hc)), if_neg (fun hc => hi hc.1)]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  by_cases hd : ∑ j, d j = n
  · have hsimp : ∀ i : Fin m, (if r ≤ d i ∧ ∑ j, d j = n then (1 : R) else 0)
        = if r ≤ d i then (1 : R) else 0 := by
      intro i
      by_cases hi : r ≤ d i
      · rw [if_pos ⟨hi, hd⟩, if_pos hi]
      · rw [if_neg (fun hc => hi hc.1), if_neg hi]
    rw [if_pos hd, Finset.sum_congr rfl fun i _ => hsimp i, Finset.sum_boole]
  · rw [if_neg hd, Finset.sum_eq_zero fun i _ => if_neg fun hc => hd hc.2]

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
  · rw [if_pos hd, Finset.sum_congr rfl fun r _ => if_pos hd, nsmul_eq_mul, mul_one,
      ← Nat.cast_sum, sum_card_le_eq_sum m n hd]
  · rw [if_neg hd, Finset.sum_eq_zero fun r _ => if_neg hd, smul_zero]

end MvPolynomial

namespace List

/-! ### Removing one part from a partition -/

/-- `z_lam` may be computed over any finite set of values containing the parts. -/
lemma zcard_eq_prod_of_subset {l : List ℕ} {s : Finset ℕ} (h : l.toFinset ⊆ s) :
    zcard l = ∏ i ∈ s, i ^ l.count i * Nat.factorial (l.count i) := by
  classical
  rw [zcard]
  refine Finset.prod_subset h fun i _ hi => ?_
  have hc : l.count i = 0 := List.count_eq_zero.2 fun hmem => hi (List.mem_toFinset.2 hmem)
  rw [hc]
  simp

/-- The partition obtained by removing one part equal to `r` from `lam`. -/
noncomputable def dropPart (lam : List ℕ) (r : ℕ) : List ℕ := sortDesc ((lam : Multiset ℕ).erase r)

@[simp] lemma coe_dropPart (lam : List ℕ) (r : ℕ) :
    (dropPart lam r : Multiset ℕ) = (lam : Multiset ℕ).erase r := coe_sortDesc _

lemma isPart_dropPart {lam : List ℕ} (hlam : IsPart lam) (r : ℕ) : IsPart (dropPart lam r) := by
  refine isPart_sortDesc fun i hi => hlam.pos_of_mem ?_
  have := Multiset.mem_of_mem_erase hi
  simpa using this

lemma count_dropPart (lam : List ℕ) (r i : ℕ) :
    (dropPart lam r).count i = if i = r then lam.count i - 1 else lam.count i := by
  have h := congrArg (Multiset.count i) (coe_dropPart lam r)
  rw [Multiset.coe_count] at h
  rw [h]
  by_cases hi : i = r
  · subst hi
    rw [if_pos rfl, Multiset.count_erase_self, Multiset.coe_count]
  · rw [if_neg hi, Multiset.count_erase_of_ne hi, Multiset.coe_count]

lemma sum_dropPart {lam : List ℕ} {r : ℕ} (hr : r ∈ lam) : (dropPart lam r).sum + r = lam.sum := by
  have hmem : r ∈ (lam : Multiset ℕ) := by simpa using hr
  have h : (r ::ₘ ((lam : Multiset ℕ).erase r)) = (lam : Multiset ℕ) := Multiset.cons_erase hmem
  have hsum := congrArg Multiset.sum h
  rw [Multiset.sum_cons] at hsum
  have hd : (dropPart lam r).sum = ((lam : Multiset ℕ).erase r).sum := by
    rw [← Multiset.sum_coe, coe_dropPart]
  rw [hd, ← Multiset.sum_coe lam]
  omega

lemma toFinset_dropPart_subset (lam : List ℕ) (r : ℕ) :
    (dropPart lam r).toFinset ⊆ lam.toFinset := by
  intro i hi
  rw [List.mem_toFinset] at hi ⊢
  have hi' : i ∈ (dropPart lam r : Multiset ℕ) := by
    exact (Multiset.mem_coe).2 hi
  rw [coe_dropPart] at hi'
  exact (Multiset.mem_coe).1 (Multiset.mem_of_mem_erase hi')

/-- **Removing one part `r` divides `z_lam` by `r · m_r(lam)`.** -/
lemma zcard_dropPart {lam : List ℕ} {r : ℕ} (hr : r ∈ lam) :
    zcard lam = r * lam.count r * zcard (dropPart lam r) := by
  classical
  have hrs : r ∈ lam.toFinset := List.mem_toFinset.2 hr
  have h1 : zcard lam = ∏ i ∈ lam.toFinset, i ^ lam.count i * Nat.factorial (lam.count i) :=
    zcard_eq_prod_of_subset (Finset.Subset.refl _)
  have h2 : zcard (dropPart lam r)
      = ∏ i ∈ lam.toFinset,
          i ^ (dropPart lam r).count i * Nat.factorial ((dropPart lam r).count i) :=
    zcard_eq_prod_of_subset (toFinset_dropPart_subset lam r)
  have htail : ∏ i ∈ lam.toFinset.erase r,
        i ^ (dropPart lam r).count i * Nat.factorial ((dropPart lam r).count i)
      = ∏ i ∈ lam.toFinset.erase r, i ^ lam.count i * Nat.factorial (lam.count i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [count_dropPart, if_neg (Finset.mem_erase.1 hi).1]
  have hc : lam.count r ≠ 0 := by
    rw [ne_eq, List.count_eq_zero, not_not]
    exact hr
  obtain ⟨k, hk⟩ : ∃ k, lam.count r = k + 1 := ⟨lam.count r - 1, by omega⟩
  rw [h1, h2, ← Finset.mul_prod_erase _ _ hrs, ← Finset.mul_prod_erase _ _ hrs, htail,
    count_dropPart, if_pos rfl, hk]
  simp only [Nat.add_sub_cancel]
  rw [pow_succ, Nat.factorial_succ]
  ring

/-- The total size of a partition, counted by distinct parts. -/
lemma sum_count_mul_self (lam : List ℕ) : ∑ i ∈ lam.toFinset, lam.count i * i = lam.sum := by
  classical
  have h := Finset.sum_multiset_map_count (lam : Multiset ℕ) (fun i : ℕ => i)
  rw [Multiset.map_id'] at h
  rw [← Multiset.sum_coe lam, h]
  refine Finset.sum_congr ?_ fun i _ => ?_
  · simp
  · rw [smul_eq_mul, Multiset.coe_count]

/-- `z_lam` only depends on the multiset of parts. -/
lemma zcard_of_perm {l l' : List ℕ} (h : l.Perm l') : zcard l = zcard l' := by
  classical
  rw [zcard, zcard, List.toFinset_eq_of_perm l l' h]
  exact Finset.prod_congr rfl fun i _ => by rw [h.count_eq]

/-- Adding one part `r` to the partition `lam`. -/
noncomputable def insPart (lam : List ℕ) (r : ℕ) : List ℕ :=
  sortDesc (r ::ₘ (lam : Multiset ℕ))

@[simp] lemma coe_insPart (lam : List ℕ) (r : ℕ) :
    (insPart lam r : Multiset ℕ) = r ::ₘ (lam : Multiset ℕ) := coe_sortDesc _

lemma insPart_perm (lam : List ℕ) (r : ℕ) : (insPart lam r).Perm (r :: lam) :=
  Quotient.exact (coe_insPart lam r)

lemma isPart_insPart {lam : List ℕ} (hlam : IsPart lam) {r : ℕ} (hr : 0 < r) :
    IsPart (insPart lam r) := by
  refine isPart_sortDesc fun i hi => ?_
  rcases Multiset.mem_cons.1 hi with rfl | hi
  · exact hr
  · exact hlam.pos_of_mem (by simpa using hi)

@[simp] lemma sum_insPart (lam : List ℕ) (r : ℕ) : (insPart lam r).sum = r + lam.sum := by
  rw [insPart, sum_sortDesc, Multiset.sum_cons, Multiset.sum_coe]

lemma mem_insPart_self (lam : List ℕ) (r : ℕ) : r ∈ insPart lam r := by
  rw [insPart, mem_sortDesc]
  exact Multiset.mem_cons_self _ _

lemma dropPart_insPart {lam : List ℕ} (hlam : IsPart lam) (r : ℕ) :
    dropPart (insPart lam r) r = lam := by
  rw [dropPart, coe_insPart, Multiset.erase_cons_head, sortDesc_coe hlam]

lemma insPart_dropPart {lam : List ℕ} (hlam : IsPart lam) {r : ℕ} (hr : r ∈ lam) :
    insPart (dropPart lam r) r = lam := by
  rw [insPart, coe_dropPart, Multiset.cons_erase (by simpa using hr), sortDesc_coe hlam]
end List

namespace MvPolynomial


/-! ### The product of power sums, and adding a part -/

lemma pProd_cons (m : ℕ) (R : Type*) [CommRing R] (r : ℕ) (lam : List ℕ) :
    pProd m R (r :: lam) = psum (Fin m) R r * pProd m R lam := by
  rw [pProd, pProd, List.map_cons, List.prod_cons]

lemma pProd_of_perm (m : ℕ) (R : Type*) [CommRing R] {l l' : List ℕ} (h : l.Perm l') :
    pProd m R l = pProd m R l' :=
  List.Perm.prod_eq (h.map _)

lemma pProd_insPart (m : ℕ) (R : Type*) [CommRing R] (lam : List ℕ) (r : ℕ) :
    pProd m R (insPart lam r) = psum (Fin m) R r * pProd m R lam := by
  rw [pProd_of_perm m R (insPart_perm lam r), pProd_cons]

/-! ### The cycle index formula -/

/-- The sum `∑_{lam ⊢ n} p_lam / z_lam`. -/
noncomputable def cycleIndexSum (m : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    MvPolynomial (Fin m) R :=
  ∑ lam ∈ partFinset n, ((zcard lam : ℚ))⁻¹ • pProd m R lam

end MvPolynomial

namespace List

/-- The scalar identity behind the recursion: the reciprocals of the `z`'s of the partitions
obtained by removing one part sum up to `n / z_lam`. -/
lemma sum_inv_zcard_dropPart {lam : List ℕ} (hlam : IsPart lam) :
    ∑ r ∈ lam.toFinset, ((zcard (dropPart lam r) : ℚ))⁻¹
      = (lam.sum : ℚ) * ((zcard lam : ℚ))⁻¹ := by
  classical
  have hterm : ∀ r ∈ lam.toFinset,
      ((zcard (dropPart lam r) : ℚ))⁻¹ = (lam.count r * r : ℕ) * ((zcard lam : ℚ))⁻¹ := by
    intro r hr
    have hrm : r ∈ lam := List.mem_toFinset.1 hr
    have hd : (zcard lam : ℚ) = ((r * lam.count r : ℕ) : ℚ) * (zcard (dropPart lam r) : ℚ) := by
      rw [← Nat.cast_mul]
      exact_mod_cast congrArg (fun k : ℕ => (k : ℚ)) (zcard_dropPart hrm)
    have hdz : (zcard (dropPart lam r) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.2 (zcard_pos (isPart_dropPart hlam r)).ne'
    have hrz : ((r * lam.count r : ℕ) : ℚ) ≠ 0 := by
      have hpos : 0 < r := hlam.pos_of_mem hrm
      have hc : lam.count r ≠ 0 := by
        rw [ne_eq, List.count_eq_zero, not_not]; exact hrm
      exact Nat.cast_ne_zero.2 (by positivity)
    rw [hd, mul_inv]
    push_cast at hrz ⊢
    field_simp
    exact (div_self (by rw [mul_comm]; exact hrz)).symm
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Nat.cast_sum, sum_count_mul_self]

end List

namespace MvPolynomial

/-- **The recursion for `∑_lam p_lam / z_lam`**. -/
lemma sum_psum_mul_cycleIndexSum (m : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    ∑ r ∈ Finset.Icc 1 n, psum (Fin m) R r * cycleIndexSum m R (n - r)
      = (n : ℚ) • cycleIndexSum m R n := by
  classical
  have hL : ∑ r ∈ Finset.Icc 1 n, psum (Fin m) R r * cycleIndexSum m R (n - r)
      = ∑ x ∈ (Finset.Icc 1 n).sigma (fun r => partFinset (n - r)),
          ((zcard x.2 : ℚ))⁻¹ • pProd m R (insPart x.2 x.1) := by
    rw [← Finset.sum_sigma' (Finset.Icc 1 n) (fun r => partFinset (n - r))
      (fun r mu => ((zcard mu : ℚ))⁻¹ • pProd m R (insPart mu r))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [cycleIndexSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun mu _ => by rw [pProd_insPart, mul_smul_comm]
  have hR : (n : ℚ) • cycleIndexSum m R n
      = ∑ y ∈ (partFinset n).sigma (fun lam => lam.toFinset),
          ((zcard (dropPart y.1 y.2) : ℚ))⁻¹ • pProd m R y.1 := by
    rw [← Finset.sum_sigma' (partFinset n) (fun lam => lam.toFinset)
      (fun lam r => ((zcard (dropPart lam r) : ℚ))⁻¹ • pProd m R lam),
      cycleIndexSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun lam hlam => ?_
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hlam
    rw [← Finset.sum_smul, sum_inv_zcard_dropPart hpart, hsum, smul_smul]
  rw [hL, hR]
  refine Finset.sum_nbij' (i := fun x => (⟨insPart x.2 x.1, x.1⟩ : (_ : List ℕ) × ℕ))
    (j := fun y => (⟨y.2, dropPart y.1 y.2⟩ : (_ : ℕ) × List ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨r, mu⟩ hx
    simp only [Finset.mem_sigma] at hx ⊢
    obtain ⟨hr, hmu⟩ := hx
    obtain ⟨hmupart, hmusum⟩ := mem_partFinset.1 hmu
    rw [Finset.mem_Icc] at hr
    refine ⟨mem_partFinset.2 ⟨isPart_insPart hmupart hr.1, ?_⟩, ?_⟩
    · rw [sum_insPart, hmusum]; omega
    · exact List.mem_toFinset.2 (mem_insPart_self mu r)
  · rintro ⟨lam, r⟩ hy
    simp only [Finset.mem_sigma] at hy ⊢
    obtain ⟨hlam, hr⟩ := hy
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hlam
    have hrm : r ∈ lam := List.mem_toFinset.1 hr
    have hpos : 0 < r := hpart.pos_of_mem hrm
    have hsd := sum_dropPart hrm
    refine ⟨Finset.mem_Icc.2 ⟨hpos, by omega⟩, mem_partFinset.2 ⟨isPart_dropPart hpart r, ?_⟩⟩
    omega
  · rintro ⟨r, mu⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hmupart, -⟩ := mem_partFinset.1 hx.2
    simp only [dropPart_insPart hmupart]
  · rintro ⟨lam, r⟩ hy
    rw [Finset.mem_sigma] at hy
    obtain ⟨hpart, -⟩ := mem_partFinset.1 hy.1
    have hrm : r ∈ lam := List.mem_toFinset.1 hy.2
    simp only [insPart_dropPart hpart hrm]
  · rintro ⟨r, mu⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hmupart, -⟩ := mem_partFinset.1 hx.2
    rw [dropPart_insPart hmupart]

/-- **The cycle index formula** : `h_n = ∑_{lam ⊢ n} p_lam / z_lam`. -/
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
      = ∑ sigma : Equiv.Perm (Fin n), pProd m R (Equiv.Perm.cycleTypeList sigma) := by
  classical
  have hfib : ∑ sigma : Equiv.Perm (Fin n), pProd m R (Equiv.Perm.cycleTypeList sigma)
      = ∑ lam ∈ partFinset n,
          (Finset.univ.filter fun sigma : Equiv.Perm (Fin n) =>
            Equiv.Perm.cycleTypeList sigma = lam).card • pProd m R lam := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun sigma _ => Equiv.Perm.cycleTypeList_mem_partFinset sigma)
      (fun sigma => pProd m R (Equiv.Perm.cycleTypeList sigma))]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [Finset.sum_congr rfl fun sigma hsigma => by
      rw [(Finset.mem_filter.1 hsigma).2], Finset.sum_const]
  rw [hfib, hsymm_eq_cycleIndexSum, cycleIndexSum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun lam hlam => ?_
  obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hlam
  have hz : (zcard lam : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (zcard_pos hpart).ne'
  have hcard : ((Finset.univ.filter fun sigma : Equiv.Perm (Fin n) =>
      Equiv.Perm.cycleTypeList sigma = lam).card : ℚ)
      = (Nat.factorial n : ℚ) * ((zcard lam : ℚ))⁻¹ := by
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

/-- The signed sum `∑_{lam ⊢ n} (-1)^{n - ℓ(lam)} p_lam / z_lam`.  The sign is written as
`(-1)^{n + ℓ(lam)}`, which avoids a truncated subtraction and has the same parity. -/
noncomputable def signedCycleIndexSum (m : ℕ) (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) :
    MvPolynomial (Fin m) R :=
  ∑ lam ∈ partFinset n, (((-1 : ℚ) ^ (n + lam.length)) * ((zcard lam : ℚ))⁻¹) • pProd m R lam

/-- **The recursion for `∑_lam ± p_lam / z_lam`**. -/
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
      (fun r mu => (((-1 : ℚ) ^ (r + 1)) * (((-1 : ℚ) ^ ((n - r) + mu.length))
        * ((zcard mu : ℚ))⁻¹)) • pProd m R (insPart mu r))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [signedCycleIndexSum, Finset.mul_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun mu _ => by
      rw [pProd_insPart, mul_smul_comm, smul_smul]
  have hR : (n : ℚ) • signedCycleIndexSum m R n
      = ∑ y ∈ (partFinset n).sigma (fun lam => lam.toFinset),
          (((-1 : ℚ) ^ (n + y.1.length)) * ((zcard (dropPart y.1 y.2) : ℚ))⁻¹)
            • pProd m R y.1 := by
    rw [← Finset.sum_sigma' (partFinset n) (fun lam => lam.toFinset)
      (fun lam r => (((-1 : ℚ) ^ (n + lam.length)) * ((zcard (dropPart lam r) : ℚ))⁻¹)
        • pProd m R lam),
      signedCycleIndexSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun lam hlam => ?_
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hlam
    rw [← Finset.sum_smul, ← Finset.mul_sum, sum_inv_zcard_dropPart hpart, hsum, smul_smul]
    ring_nf
  rw [hL, hR]
  refine Finset.sum_nbij' (i := fun x => (⟨insPart x.2 x.1, x.1⟩ : (_ : List ℕ) × ℕ))
    (j := fun y => (⟨y.2, dropPart y.1 y.2⟩ : (_ : ℕ) × List ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨r, mu⟩ hx
    simp only [Finset.mem_sigma] at hx ⊢
    obtain ⟨hr, hmu⟩ := hx
    obtain ⟨hmupart, hmusum⟩ := mem_partFinset.1 hmu
    rw [Finset.mem_Icc] at hr
    refine ⟨mem_partFinset.2 ⟨isPart_insPart hmupart hr.1, ?_⟩, ?_⟩
    · rw [sum_insPart, hmusum]; omega
    · exact List.mem_toFinset.2 (mem_insPart_self mu r)
  · rintro ⟨lam, r⟩ hy
    simp only [Finset.mem_sigma] at hy ⊢
    obtain ⟨hlam, hr⟩ := hy
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hlam
    have hrm : r ∈ lam := List.mem_toFinset.1 hr
    have hpos : 0 < r := hpart.pos_of_mem hrm
    have hsd := sum_dropPart hrm
    refine ⟨Finset.mem_Icc.2 ⟨hpos, by omega⟩, mem_partFinset.2 ⟨isPart_dropPart hpart r, ?_⟩⟩
    omega
  · rintro ⟨r, mu⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hmupart, -⟩ := mem_partFinset.1 hx.2
    simp only [dropPart_insPart hmupart]
  · rintro ⟨lam, r⟩ hy
    rw [Finset.mem_sigma] at hy
    obtain ⟨hpart, -⟩ := mem_partFinset.1 hy.1
    have hrm : r ∈ lam := List.mem_toFinset.1 hy.2
    simp only [insPart_dropPart hpart hrm]
  · rintro ⟨r, mu⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx
    obtain ⟨hr, hmu⟩ := hx
    obtain ⟨hmupart, -⟩ := mem_partFinset.1 hmu
    have hlen : (insPart mu r).length = mu.length + 1 := by
      have hcard : ((insPart mu r : List ℕ) : Multiset ℕ).card = (insPart mu r).length :=
        Multiset.coe_card _
      rw [coe_insPart, Multiset.card_cons] at hcard
      simp only [Multiset.coe_card] at hcard
      omega
    have hsign : ((-1 : ℚ) ^ (r + 1)) * ((-1 : ℚ) ^ ((n - r) + mu.length))
        = (-1 : ℚ) ^ (n + (insPart mu r).length) := by
      rw [← pow_add, hlen, neg_one_pow_eq_pow_mod_two]
      have hmod : (r + 1 + (n - r + mu.length)) % 2 = (n + (mu.length + 1)) % 2 := by omega
      rw [hmod, ← neg_one_pow_eq_pow_mod_two]
    rw [dropPart_insPart hmupart, ← mul_assoc, hsign]

/-- **The signed cycle index formula** : `e_n = ∑_{lam ⊢ n} (-1)^{n - ℓ(lam)} p_lam / z_lam`. -/
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

/-! ### A numerical consequence: the signed sum of the `1 / z_lam` -/

lemma psum_one_var (R : Type*) [CommRing R] (r : ℕ) : psum (Fin 1) R r = X 0 ^ r := by
  simp [psum]

lemma pProd_one_var (R : Type*) [CommRing R] (lam : List ℕ) :
    pProd 1 R lam = X 0 ^ lam.sum := by
  induction lam with
  | nil => simp
  | cons r t ih => rw [pProd_cons, ih, psum_one_var, List.sum_cons, pow_add]

lemma esymm_fin_one_eq_zero (R : Type*) [CommRing R] {n : ℕ} (hn : 1 < n) :
    esymm (Fin 1) R n = 0 := by
  rw [esymm, Finset.powersetCard_eq_empty.2 (by simpa using hn), Finset.sum_empty]

/-- The signed version of `∑_{lam ⊢ n} 1 / z_lam = 1`: for `n ≥ 2` the partitions of `n`
with an even number of parts and those with an odd number of parts balance out. -/
theorem sum_signed_inv_zcard {n : ℕ} (hn : 1 < n) :
    ∑ lam ∈ partFinset n, ((-1 : ℚ) ^ (n + lam.length)) * ((zcard lam : ℚ))⁻¹ = 0 := by
  have hzero : signedCycleIndexSum 1 ℚ n = 0 :=
    (esymm_eq_signedCycleIndexSum 1 ℚ n).symm.trans (esymm_fin_one_eq_zero ℚ hn)
  have hs : signedCycleIndexSum 1 ℚ n
      = (∑ lam ∈ partFinset n, ((-1 : ℚ) ^ (n + lam.length)) * ((zcard lam : ℚ))⁻¹)
        • (X 0 ^ n : MvPolynomial (Fin 1) ℚ) := by
    rw [signedCycleIndexSum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun lam hlam => ?_
    obtain ⟨-, hsum⟩ := mem_partFinset.1 hlam
    rw [pProd_one_var, hsum]
  rw [hs] at hzero
  have hcoeff := congrArg (coeff (Finsupp.single (0 : Fin 1) n)) hzero
  simpa [X_pow_eq_monomial, coeff_monomial, smul_eq_mul] using hcoeff

end MvPolynomial
