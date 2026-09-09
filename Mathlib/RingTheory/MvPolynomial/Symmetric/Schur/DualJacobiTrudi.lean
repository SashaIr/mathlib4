/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.OmegaMul
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.JacobiTrudi

/-!
# The dual Jacobi-Trudi (Nägelsbach-Kostka) formula

Following `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we deduce from the Jacobi-Trudi
formula (`MvPolynomial.schurPoly_eq_det_jtMatrix`) and from the involution `omega`
(`MvPolynomial.omegaSym`) the dual Jacobi-Trudi formula

`s_lam = det (e_{lam'_i - i + j})`,

where `lam'` is the conjugate partition and `e` denotes the elementary symmetric
polynomials.

The proof expands the Jacobi-Trudi determinant by the Leibniz formula: each term is, up to
a sign, a product `h_mu` of complete homogeneous symmetric polynomials indexed by a
partition `mu` of `n = |lam|`, and `omega h_mu = e_mu`.  Applying `omega`, which sends
`s_lam` to `s_{lam'}`, therefore turns the Jacobi-Trudi determinant of `lam` into the
determinant of the matrix of the elementary symmetric polynomials.  As `omega` is only
available in degree `n` for `n ≤ m` variables, the statement carries the hypothesis
`|lam| ≤ m`.

## Main definitions and results

* `MvPolynomial.esymmInt m R n` : the elementary symmetric polynomial indexed by an integer,
  zero for a negative index.
* `MvPolynomial.partOfList c` : the partition obtained by sorting the nonzero entries of a list.
* `MvPolynomial.dualJtMatrix m R lam` : the matrix `(e_{lam'_i - i + j})`.
* `MvPolynomial.schurPoly_eq_det_dualJtMatrix` : **the dual Jacobi-Trudi formula**.
-/

@[expose] public section

open List

namespace MvPolynomial

open MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### Elementary symmetric polynomials with an integer index -/

/-- The elementary symmetric polynomial indexed by an integer: it is zero for a negative
index. -/
noncomputable def esymmInt (m : ℕ) (R : Type*) [CommRing R] (n : ℤ) :
    MvPolynomial (Fin m) R :=
  if 0 ≤ n then esymm (Fin m) R n.toNat else 0

@[simp]
lemma esymmInt_natCast (n : ℕ) : esymmInt m R (n : ℤ) = esymm (Fin m) R n := by
  simp [esymmInt]

lemma esymmInt_of_neg {n : ℤ} (hn : n < 0) : esymmInt m R n = 0 := by
  simp [esymmInt, not_le.2 hn]

/-! ### The partition attached to a list of natural numbers -/

/-- The partition obtained from a list of natural numbers by removing its zero entries and
sorting the remaining ones in decreasing order. -/
noncomputable def partOfList (c : List ℕ) : List ℕ :=
  sortDesc ((c : Multiset ℕ).filter (· ≠ 0))

lemma coe_partOfList (c : List ℕ) :
    ((partOfList c : List ℕ) : Multiset ℕ) = ((c : Multiset ℕ).filter (· ≠ 0)) := by
  rw [partOfList, coe_sortDesc]

lemma isPart_partOfList (c : List ℕ) : IsPart (partOfList c) := by
  refine isPart_sortDesc fun i hi => ?_
  exact Nat.pos_of_ne_zero (by simpa using (Multiset.mem_filter.1 hi).2)

/-- Removing the zero entries of a multiset does not change its sum. -/
lemma sum_multiset_filter_ne_zero (s : Multiset ℕ) : (s.filter (· ≠ 0)).sum = s.sum := by
  classical
  conv_rhs => rw [← Multiset.filter_add_not (· ≠ 0) s]
  rw [Multiset.sum_add]
  have hz : (Multiset.filter (fun x : ℕ => ¬ x ≠ 0) s).sum = 0 := by
    refine Multiset.sum_eq_zero fun x hx => ?_
    simpa using (Multiset.mem_filter.1 hx).2
  rw [hz, add_zero]

/-- Removing the zero entries of a multiset does not change the product of the values of a
function taking the value `1` at `0`. -/
lemma prod_map_filter_ne_zero {M : Type*} [CommMonoid M] (f : ℕ → M) (hf : f 0 = 1)
    (s : Multiset ℕ) : ((s.filter (· ≠ 0)).map f).prod = (s.map f).prod := by
  classical
  conv_rhs => rw [← Multiset.filter_add_not (· ≠ 0) s]
  rw [Multiset.map_add, Multiset.prod_add]
  have hz : ((Multiset.filter (fun x : ℕ => ¬ x ≠ 0) s).map f).prod = 1 := by
    refine Multiset.prod_eq_one fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
    have hy0 : y = 0 := by simpa using (Multiset.mem_filter.1 hy).2
    rw [hy0, hf]
  rw [hz, mul_one]

@[simp]
lemma sum_partOfList (c : List ℕ) : (partOfList c).sum = c.sum := by
  have h : ((partOfList c : List ℕ) : Multiset ℕ).sum = ((c : List ℕ) : Multiset ℕ).sum := by
    rw [coe_partOfList, sum_multiset_filter_ne_zero]
  rwa [Multiset.sum_coe, Multiset.sum_coe] at h

lemma length_partOfList_le (c : List ℕ) : (partOfList c).length ≤ c.length := by
  have h : Multiset.card ((partOfList c : List ℕ) : Multiset ℕ)
      ≤ Multiset.card ((c : List ℕ) : Multiset ℕ) := by
    rw [coe_partOfList]
    exact Multiset.card_le_card (Multiset.filter_le _ _)
  rwa [Multiset.coe_card, Multiset.coe_card] at h

lemma hProd_partOfList (m : ℕ) (R : Type*) [CommRing R] (c : List ℕ) :
    hProd m R (partOfList c) = hProd m R c := by
  have h := prod_map_filter_ne_zero (hsymm (Fin m) R) (hsymm_zero (Fin m) R)
    ((c : List ℕ) : Multiset ℕ)
  rw [← coe_partOfList, Multiset.map_coe, Multiset.map_coe, Multiset.prod_coe,
    Multiset.prod_coe] at h
  rw [hProd, hProd]
  exact h

lemma eProd_partOfList (m : ℕ) (R : Type*) [CommRing R] (c : List ℕ) :
    eProd m R (partOfList c) = eProd m R c := by
  have h := prod_map_filter_ne_zero (esymm (Fin m) R) (esymm_zero (Fin m) R)
    ((c : List ℕ) : Multiset ℕ)
  rw [← coe_partOfList, Multiset.map_coe, Multiset.map_coe, Multiset.prod_coe,
    Multiset.prod_coe] at h
  rw [eProd, eProd]
  exact h

/-! ### The terms of the Leibniz expansion -/

/-- The exponent `lam_{sigma i} + i - sigma i` appearing in the `sigma`-term of the
Leibniz expansion of the Jacobi-Trudi determinant. -/
def jtArg (lam : List ℕ) (sigma : Equiv.Perm (Fin m)) (i : Fin m) : ℤ :=
  (lam.getD (sigma i) 0 : ℤ) + (i : ℕ) - ((sigma i : Fin m) : ℕ)

/-- The list of the exponents of the `sigma`-term, when they are all nonnegative. -/
def jtArgList (lam : List ℕ) (sigma : Equiv.Perm (Fin m)) : List ℕ :=
  List.ofFn fun i => (jtArg lam sigma i).toNat

lemma sum_jtArg {lam : List ℕ} (hlen : lam.length ≤ m) (sigma : Equiv.Perm (Fin m)) :
    ∑ i, jtArg lam sigma i = (lam.sum : ℤ) := by
  have hsplit : ∑ i, jtArg lam sigma i
      = ((∑ i : Fin m, (lam.getD (sigma i) 0 : ℤ)) + ∑ i : Fin m, ((i : ℕ) : ℤ))
        - ∑ i : Fin m, (((sigma i : Fin m) : ℕ) : ℤ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    rfl
  have hperm : ∑ i : Fin m, (((sigma i : Fin m) : ℕ) : ℤ) = ∑ i : Fin m, ((i : ℕ) : ℤ) :=
    Equiv.sum_comp sigma fun j : Fin m => ((j : ℕ) : ℤ)
  have hlam : ∑ i : Fin m, (lam.getD (sigma i) 0 : ℤ) = (lam.sum : ℤ) := by
    rw [Equiv.sum_comp sigma fun j : Fin m => (lam.getD (j : ℕ) 0 : ℤ), ← Nat.cast_sum]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun i => lam.getD i 0) m,
      ← sum_eq_sum_range_getD lam hlen]
  rw [hsplit, hperm, hlam]
  ring

lemma sum_jtArgList {lam : List ℕ} (hlen : lam.length ≤ m) {sigma : Equiv.Perm (Fin m)}
    (hnn : ∀ i, 0 ≤ jtArg lam sigma i) : (jtArgList lam sigma).sum = lam.sum := by
  have hcast : (((jtArgList lam sigma).sum : ℕ) : ℤ) = (lam.sum : ℤ) := by
    rw [jtArgList, List.sum_ofFn, Nat.cast_sum, ← sum_jtArg hlen sigma]
    exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hnn i)
  exact_mod_cast hcast

@[simp]
lemma length_jtArgList (lam : List ℕ) (sigma : Equiv.Perm (Fin m)) :
    (jtArgList lam sigma).length = m := by
  simp [jtArgList]

lemma prod_hsymmInt_eq_hProd {lam : List ℕ} {sigma : Equiv.Perm (Fin m)}
    (hnn : ∀ i, 0 ≤ jtArg lam sigma i) :
    ∏ i, hsymmInt m R (jtArg lam sigma i) = hProd m R (jtArgList lam sigma) := by
  rw [hProd, jtArgList, List.map_ofFn, List.prod_ofFn]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [hsymmInt, hnn i]

lemma prod_esymmInt_eq_eProd {lam : List ℕ} {sigma : Equiv.Perm (Fin m)}
    (hnn : ∀ i, 0 ≤ jtArg lam sigma i) :
    ∏ i, esymmInt m R (jtArg lam sigma i) = eProd m R (jtArgList lam sigma) := by
  rw [eProd, jtArgList, List.map_ofFn, List.prod_ofFn]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [esymmInt, hnn i]

lemma prod_hsymmInt_eq_zero {lam : List ℕ} {sigma : Equiv.Perm (Fin m)}
    (hnn : ¬ ∀ i, 0 ≤ jtArg lam sigma i) :
    ∏ i, hsymmInt m R (jtArg lam sigma i) = 0 := by
  obtain ⟨i, hi⟩ := not_forall.1 hnn
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hsymmInt_of_neg (not_le.1 hi))

lemma prod_esymmInt_eq_zero {lam : List ℕ} {sigma : Equiv.Perm (Fin m)}
    (hnn : ¬ ∀ i, 0 ≤ jtArg lam sigma i) :
    ∏ i, esymmInt m R (jtArg lam sigma i) = 0 := by
  obtain ⟨i, hi⟩ := not_forall.1 hnn
  exact Finset.prod_eq_zero (Finset.mem_univ i) (esymmInt_of_neg (not_le.1 hi))

/-- The `sigma`-term of the Leibniz expansion is a symmetric homogeneous polynomial of
degree `|lam|`. -/
lemma prod_hsymmInt_mem {lam : List ℕ} (hlen : lam.length ≤ m) (sigma : Equiv.Perm (Fin m)) :
    (∏ i, hsymmInt m R (jtArg lam sigma i)) ∈ symHomogeneousSubmodule m lam.sum R := by
  by_cases hnn : ∀ i, 0 ≤ jtArg lam sigma i
  · rw [prod_hsymmInt_eq_hProd hnn]
    have h := hProd_mem_symHomogeneousSubmodule' (m := m) (R := R) (jtArgList lam sigma)
    rwa [sum_jtArgList hlen hnn] at h
  · rw [prod_hsymmInt_eq_zero hnn]
    exact Submodule.zero_mem _

/-- The `sigma`-term of the Leibniz expansion of the Jacobi-Trudi determinant, as an
element of the module of symmetric homogeneous polynomials of degree `|lam|`. -/
noncomputable def jtTermSub (m : ℕ) (R : Type*) [CommRing R] {lam : List ℕ}
    (hlen : lam.length ≤ m) (sigma : Equiv.Perm (Fin m)) :
    symHomogeneousSubmodule m lam.sum R :=
  ⟨∏ i, hsymmInt m R (jtArg lam sigma i), prod_hsymmInt_mem hlen sigma⟩

/-- The involution `omega` sends the `sigma`-term of the Leibniz expansion of the
Jacobi-Trudi determinant to the corresponding term with the elementary symmetric
polynomials. -/
lemma omegaSym_jtTermSub {lam : List ℕ} (hnm : lam.sum ≤ m) (hlen : lam.length ≤ m)
    (sigma : Equiv.Perm (Fin m)) :
    (omegaSym m lam.sum R hnm (jtTermSub m R hlen sigma) : MvPolynomial (Fin m) R)
      = ∏ i, esymmInt m R (jtArg lam sigma i) := by
  by_cases hnn : ∀ i, 0 ≤ jtArg lam sigma i
  · have hlenmu : (partOfList (jtArgList lam sigma)).length ≤ m := by
      refine le_trans (length_partOfList_le _) ?_
      simp
    let mu : PartIdx lam.sum m :=
      ⟨partOfList (jtArgList lam sigma), isPart_partOfList _, by
        rw [sum_partOfList, sum_jtArgList hlen hnn], hlenmu⟩
    have hA : jtTermSub m R hlen sigma = hSub m lam.sum R mu := by
      apply Subtype.ext
      change (∏ i, hsymmInt m R (jtArg lam sigma i)) = hProd m R (partOfList (jtArgList lam sigma))
      rw [prod_hsymmInt_eq_hProd hnn, hProd_partOfList]
    rw [hA, omegaSym_hSub hnm mu, coe_eSubOfPart, prod_esymmInt_eq_eProd hnn]
    exact eProd_partOfList m R _
  · have hzero : jtTermSub m R hlen sigma = 0 := Subtype.ext (prod_hsymmInt_eq_zero hnn)
    rw [hzero, map_zero, prod_esymmInt_eq_zero hnn]
    rfl

/-! ### The dual Jacobi-Trudi formula -/

/-- The matrix `(e_{lam'_i - i + j})` of the dual Jacobi-Trudi formula. -/
noncomputable def dualJtMatrix (m : ℕ) (R : Type*) [CommRing R] (lam : List ℕ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin m) R) :=
  Matrix.of fun i k => esymmInt m R (((conjPart lam).getD i 0 : ℤ) + (k : ℕ) - (i : ℕ))

/-- The determinant of the matrix of the elementary symmetric polynomials attached to
`lam` is the Schur polynomial of the conjugate partition. -/
theorem schurPoly_conjPart_eq_det {lam : List ℕ} (hlam : IsPart lam) (hnm : lam.sum ≤ m) :
    schurPoly (Fin m) R (conjPart lam)
      = (Matrix.of fun i k : Fin m =>
          esymmInt m R ((lam.getD i 0 : ℤ) + (k : ℕ) - (i : ℕ))).det := by
  have hlen : lam.length ≤ m := le_trans hlam.length_le_sum hnm
  let lamIdx : PartIdx lam.sum m := ⟨lam, hlam, rfl, hlen⟩
  have hX : schurSub m lam.sum R lamIdx
      = ∑ sigma : Equiv.Perm (Fin m),
          (Equiv.Perm.sign sigma : ℤ) • jtTermSub m R hlen sigma := by
    apply Subtype.ext
    have hcoe : ((∑ sigma : Equiv.Perm (Fin m),
          (Equiv.Perm.sign sigma : ℤ) • jtTermSub m R hlen sigma :
            symHomogeneousSubmodule m lam.sum R) : MvPolynomial (Fin m) R)
        = ∑ sigma : Equiv.Perm (Fin m),
            (Equiv.Perm.sign sigma : ℤ) • ∏ i, hsymmInt m R (jtArg lam sigma i) := by
      simp [jtTermSub]
    rw [hcoe, coe_schurSub]
    change schurPoly (Fin m) R lam = _
    rw [schurPoly_eq_det_jtMatrix hlam hlen, Matrix.det_apply]
    refine Finset.sum_congr rfl fun sigma _ => ?_
    rw [Units.smul_def]
    rfl
  have hL : (omegaSym m lam.sum R hnm (schurSub m lam.sum R lamIdx) : MvPolynomial (Fin m) R)
      = schurPoly (Fin m) R (conjPart lam) := by
    rw [omegaSym_schurSub, coe_schurSub, conjIdx_val]
  have hR : (omegaSym m lam.sum R hnm (∑ sigma : Equiv.Perm (Fin m),
        (Equiv.Perm.sign sigma : ℤ) • jtTermSub m R hlen sigma) : MvPolynomial (Fin m) R)
      = ∑ sigma : Equiv.Perm (Fin m),
          (Equiv.Perm.sign sigma : ℤ) • ∏ i, esymmInt m R (jtArg lam sigma i) := by
    rw [map_sum]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun sigma _ => ?_
    rw [map_zsmul, AddSubgroupClass.coe_zsmul, omegaSym_jtTermSub hnm hlen sigma]
  rw [← hL, hX, hR, Matrix.det_apply]
  refine Finset.sum_congr rfl fun sigma _ => ?_
  rw [Units.smul_def]
  rfl

/-- **The dual Jacobi-Trudi formula** (Nägelsbach-Kostka): the Schur polynomial of a
partition `lam` of `n ≤ m` is the determinant of the matrix `(e_{lam'_i - i + j})` of
elementary symmetric polynomials in `m` variables, where `lam'` is the conjugate of
`lam`. -/
theorem schurPoly_eq_det_dualJtMatrix {lam : List ℕ} (hlam : IsPart lam) (hnm : lam.sum ≤ m) :
    schurPoly (Fin m) R lam = (dualJtMatrix m R lam).det := by
  have h := schurPoly_conjPart_eq_det (R := R) (m := m) (isPart_conjPart hlam)
    (by rw [sum_conjPart]; exact hnm)
  rw [conjPart_conjPart hlam] at h
  rw [h, dualJtMatrix]

end MvPolynomial
