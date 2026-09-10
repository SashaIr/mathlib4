/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Basis

/-!
# Products of power sums and their expansion in the monomial symmetric polynomials

Following `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we study the products

`p_lam = p_{lam_1} * ... * p_{lam_k}`

of the power sums `p_r = ∑_i X_i ^ r` of Mathlib.  Expanding the product, `p_lam` is the
sum of the monomials attached to the assignments of the parts of `lam` to the variables;
the coefficient of a monomial therefore counts such assignments.  Grouping the parts can
only make the shape of the exponent vector bigger for the dominance order, so

`p_lam = c_lam * m_lam + (terms m_mu with lam ⊴ mu, lam ≠ mu)`,

where the leading coefficient `c_lam` is a nonzero natural number (it is the product of
the factorials of the multiplicities of the parts of `lam`, but only its nonvanishing is
proved here).

## Main definitions and results

* `MvPolynomial.pProd` : the product `p_lam` of power sums.
* `MvPolynomial.partWeight` : the exponent vector of an assignment of the parts to the variables.
* `MvPolynomial.pProd_eq_sum_monomialSym` : the expansion of `p_lam` in the monomial symmetric
  polynomials.
* `MvPolynomial.partdom_of_pCoeff_ne_zero` : the expansion is triangular for the dominance order.
* `MvPolynomial.pCoeff_self_ne_zero` : the leading coefficient does not vanish.
-/

@[expose] public section

open Young

open List

namespace MvPolynomial

open MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### A general expansion of a symmetric homogeneous polynomial -/

/-- A symmetric homogeneous polynomial of degree `n` is a combination of the monomial
symmetric polynomials of the partitions of `n` with at most `m` parts. -/
theorem eq_sum_monomialSym_partsFinset {n : ℕ} {p : MvPolynomial (Fin m) R}
    (hsym : p.IsSymmetric) (hhom : p.IsHomogeneous n) :
    p = ∑ mu ∈ partsFinset n m, coeff (shapeContent m mu) p • monomialSym m R mu := by
  classical
  have hsub : p.support.image degShape ⊆ partsFinset n m := by
    intro nu hnu
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hnu
    refine mem_partsFinset.2 ⟨isPart_degShape d, ?_, length_degShape_le d⟩
    rw [sum_degShape d]
    exact sum_eq_of_isHomogeneous hhom hd
  have hzero : ∀ mu ∈ partsFinset n m, mu ∉ p.support.image degShape →
      coeff (shapeContent m mu) p • monomialSym m R mu = 0 := by
    intro mu hmu hnotin
    have hc : coeff (shapeContent m mu) p = 0 := by
      by_contra hne
      exact hnotin (Finset.mem_image.2 ⟨shapeContent m mu, mem_support_iff.2 hne,
        degShape_shapeContent (mem_partsFinset.1 hmu).1 (mem_partsFinset.1 hmu).2.2⟩)
    rw [hc, zero_smul]
  calc p = ∑ mu ∈ p.support.image degShape, coeff (shapeContent m mu) p • monomialSym m R mu :=
        eq_sum_monomialSym hsym
    _ = ∑ mu ∈ partsFinset n m, coeff (shapeContent m mu) p • monomialSym m R mu :=
        Finset.sum_subset hsub hzero

/-! ### The exponent vector of an assignment of the parts to the variables -/

/-- The exponent vector attached to an assignment `f` of the parts of `lam` to the
variables: the exponent of the variable `j` is the sum of the parts sent to `j`. -/
noncomputable def partWeight (m : ℕ) (lam : List ℕ) (f : Fin lam.length → Fin m) :
    Fin m →₀ ℕ := ∑ i : Fin lam.length, Finsupp.single (f i) (lam.get i)

lemma partWeight_apply (lam : List ℕ) (f : Fin lam.length → Fin m) (j : Fin m) :
    partWeight m lam f j = ∑ i ∈ Finset.univ.filter fun i => f i = j, lam.get i := by
  classical
  rw [partWeight, Finsupp.finsetSum_apply, Finset.sum_filter]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Finsupp.single_apply]

lemma sum_partWeight (lam : List ℕ) (f : Fin lam.length → Fin m) :
    ∑ j, partWeight m lam f j = lam.sum := by
  classical
  have h1 : ∑ j, partWeight m lam f j
      = ∑ j, ∑ i : Fin lam.length, (Finsupp.single (f i) (lam.get i) : Fin m →₀ ℕ) j :=
    Finset.sum_congr rfl fun j _ => by rw [partWeight, Finsupp.finsetSum_apply]
  rw [h1, Finset.sum_comm]
  have h2 : ∀ i : Fin lam.length,
      ∑ j, (Finsupp.single (f i) (lam.get i) : Fin m →₀ ℕ) j = lam.get i := by
    intro i
    simp
  rw [Finset.sum_congr rfl fun i _ => h2 i]
  conv_rhs => rw [← List.ofFn_get lam]
  rw [List.sum_ofFn]

/-! ### The product of power sums -/

/-- The product `p_lam = p_{lam_1} * ... * p_{lam_k}` of power sums attached to a list
`lam`. -/
noncomputable def pProd (m : ℕ) (R : Type*) [CommRing R] (lam : List ℕ) :
    MvPolynomial (Fin m) R := (lam.map (psum (Fin m) R)).prod

@[simp] lemma pProd_nil (m : ℕ) (R : Type*) [CommRing R] : pProd m R [] = 1 := rfl

lemma prod_X_pow_eq_monomial_sum_single {ι : Type*} (s : Finset ι) (a : ι → Fin m) (e : ι → ℕ) :
    ∏ i ∈ s, (X (a i) : MvPolynomial (Fin m) R) ^ (e i)
      = monomial (∑ i ∈ s, Finsupp.single (a i) (e i)) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, X_pow_eq_monomial,
      monomial_mul_monomial, one_mul]

/-- Expanding the product of power sums: `p_lam` is the sum of the monomials attached to
the assignments of the parts of `lam` to the variables. -/
theorem pProd_eq_sum_monomial (lam : List ℕ) :
    pProd m R lam = ∑ f : Fin lam.length → Fin m, monomial (partWeight m lam f) (1 : R) := by
  classical
  have hlist : lam.map (psum (Fin m) R)
      = List.ofFn (fun i : Fin lam.length => psum (Fin m) R (lam.get i)) := by
    conv_lhs => rw [← List.ofFn_get lam]
    rw [List.map_ofFn]
    rfl
  have h1 : pProd m R lam = ∏ i : Fin lam.length, psum (Fin m) R (lam.get i) := by
    rw [pProd, hlist, List.prod_ofFn]
  rw [h1]
  simp only [psum]
  rw [Finset.prod_univ_sum (fun _ : Fin lam.length => (Finset.univ : Finset (Fin m)))
    (fun (i : Fin lam.length) (j : Fin m) => (X j : MvPolynomial (Fin m) R) ^ (lam.get i))]
  rw [Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun f _ => prod_X_pow_eq_monomial_sum_single _ _ _

/-- The coefficient of a monomial in `p_lam` counts the assignments of the parts to the
variables with the given exponent vector. -/
theorem coeff_pProd (lam : List ℕ) (d : Fin m →₀ ℕ) :
    coeff d (pProd m R lam)
      = ((Finset.univ.filter fun f : Fin lam.length → Fin m => partWeight m lam f = d).card
          : R) := by
  classical
  rw [pProd_eq_sum_monomial, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_boole]

/-- `p_lam` is a symmetric polynomial. -/
theorem pProd_isSymmetric (lam : List ℕ) : (pProd m R lam).IsSymmetric := by
  induction lam with
  | nil => simp [pProd, MvPolynomial.IsSymmetric.one]
  | cons a l ih =>
    rw [pProd, List.map_cons, List.prod_cons]
    exact (psum_isSymmetric (Fin m) R a).mul ih

/-- `p_lam` is homogeneous of degree the size of `lam`. -/
theorem isHomogeneous_pProd (lam : List ℕ) : (pProd m R lam).IsHomogeneous lam.sum := by
  classical
  rw [pProd_eq_sum_monomial]
  refine IsHomogeneous.sum _ _ _ fun f _ => isHomogeneous_monomial 1 ?_
  rw [Finsupp.degree_eq_sum, sum_partWeight lam f]

/-! ### The expansion in the monomial symmetric polynomials -/

/-- The coefficient of `m_mu` in the expansion of `p_lam`: the number of assignments of
the parts of `lam` to the variables whose exponent vector is `mu`. -/
noncomputable def pCoeff (m : ℕ) (lam mu : List ℕ) : ℕ :=
  (Finset.univ.filter fun f : Fin lam.length → Fin m =>
    partWeight m lam f = shapeContent m mu).card

/-- **The expansion of `p_lam` in the monomial symmetric polynomials**. -/
theorem pProd_eq_sum_monomialSym (lam : List ℕ) :
    pProd m R lam
      = ∑ mu ∈ partsFinset lam.sum m, (pCoeff m lam mu : R) • monomialSym m R mu := by
  rw [eq_sum_monomialSym_partsFinset (pProd_isSymmetric lam) (isHomogeneous_pProd lam)]
  exact Finset.sum_congr rfl fun mu _ => by rw [coeff_pProd, pCoeff]

/-! ### Triangularity for the dominance order -/

/-- Truncation at `k` is subadditive. -/
lemma min_sum_le_sum_min (k : ℕ) {ι : Type*} (s : Finset ι) (a : ι → ℕ) :
    min (∑ i ∈ s, a i) k ≤ ∑ i ∈ s, min (a i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    omega

/-- A criterion for dominance, through the conjugate partitions: `s` is dominated by `t`
as soon as all the truncated sums of `t` are at most those of `s`. -/
lemma partdom_of_sum_map_min_le {s t : List ℕ} (hs : IsPart s) (ht : IsPart t)
    (hsum : s.sum = t.sum)
    (h : ∀ k, (t.map fun x => min x k).sum ≤ (s.map fun x => min x k).sum) : Partdom s t := by
  rw [← partdom_conjPart_iff hs ht hsum]
  intro k
  rw [← sum_map_min t k, ← sum_map_min s k]
  exact h k

lemma sum_map_min_eq_sum_univ {l : List ℕ} (hlen : l.length ≤ m) (k : ℕ) :
    (l.map fun x => min x k).sum = ∑ j : Fin m, min (shapeContent m l j) k := by
  rw [sum_map_eq_sum_range (by simp) l hlen,
    ← Fin.sum_univ_eq_sum_range (fun i => min (l.getD i 0) k) m]
  exact Finset.sum_congr rfl fun j _ => by rw [shapeContent_apply]

lemma sum_map_min_eq_sum_get (l : List ℕ) (k : ℕ) :
    (l.map fun x => min x k).sum = ∑ i : Fin l.length, min (l.get i) k := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-- **The expansion of `p_lam` is triangular for the dominance order**: only the shapes
`mu` dominating `lam` occur. -/
theorem partdom_of_pCoeff_ne_zero {lam mu : List ℕ} (hlam : IsPart lam) (hmu : IsPart mu)
    (hmulen : mu.length ≤ m) (hsum : lam.sum = mu.sum) (h : pCoeff m lam mu ≠ 0) :
    Partdom lam mu := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : Fin lam.length → Fin m, partWeight m lam f = shapeContent m mu := by
    rw [pCoeff, Finset.card_ne_zero] at h
    obtain ⟨f, hfmem⟩ := h
    exact ⟨f, (Finset.mem_filter.1 hfmem).2⟩
  refine partdom_of_sum_map_min_le hlam hmu hsum fun k => ?_
  rw [sum_map_min_eq_sum_univ hmulen k, ← hf, sum_map_min_eq_sum_get lam k]
  calc ∑ j, min (partWeight m lam f j) k
      ≤ ∑ j : Fin m, ∑ i ∈ Finset.univ.filter fun i => f i = j, min (lam.get i) k := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [partWeight_apply]
        exact min_sum_le_sum_min k _ _
    _ = ∑ i : Fin lam.length, min (lam.get i) k :=
        Finset.sum_fiberwise Finset.univ f fun i => min (lam.get i) k

/-- **The leading coefficient of the expansion of `p_lam` does not vanish**: the identity
assignment sends the parts of `lam` to the exponent vector `lam`. -/
theorem pCoeff_self_ne_zero {lam : List ℕ} (hlen : lam.length ≤ m) : pCoeff m lam lam ≠ 0 := by
  classical
  have hf : partWeight m lam (fun i => (⟨i, lt_of_lt_of_le i.2 hlen⟩ : Fin m))
      = shapeContent m lam := by
    ext j
    rw [partWeight_apply, shapeContent_apply]
    by_cases hj : (j : ℕ) < lam.length
    · have hfil : (Finset.univ.filter fun i : Fin lam.length =>
          (⟨i, lt_of_lt_of_le i.2 hlen⟩ : Fin m) = j) = {(⟨(j : ℕ), hj⟩ : Fin lam.length)} := by
        ext i
        simp [Fin.ext_iff]
      rw [hfil, Finset.sum_singleton, List.getD_eq_getElem _ _ hj]
      rfl
    · have hfil : (Finset.univ.filter fun i : Fin lam.length =>
          (⟨i, lt_of_lt_of_le i.2 hlen⟩ : Fin m) = j) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          Fin.ext_iff]
        have := i.2
        omega
      rw [hfil, Finset.sum_empty, List.getD_eq_default _ _ (by omega)]
  rw [pCoeff, Finset.card_ne_zero]
  exact ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hf⟩⟩

end MvPolynomial
