/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Alternant.Pieri
import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.CompleteHomogeneous

/-!
# The bialternant formula for Schur polynomials

Following `theories/MPoly/Schur_altdef.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove Jacobi's bialternant
definition of the Schur polynomials:

`a_{lam + delta} = s_lam * a_delta`,

where `delta = (m-1, m-2, ..., 1, 0)` is the staircase vector and `a_b` is the alternant
attached to the exponent vector `b`.

The proof combines the Pieri rule for alternants (`MvPolynomial.hsymm_mul_alt_strip`) with the
Pieri rule for Schur polynomials (`MvPolynomial.schurPoly_mul_hsymm`): both families satisfy the
same recursion, hence both expand along the Kostka numbers, and the unitriangularity of
the Kostka matrix lets us identify them.

## Main definitions and results

* `MvPolynomial.partVec m lam` : the exponent vector `lam + delta` of a partition `lam`.
* `MvPolynomial.altPart m R lam` : the alternant `a_{lam + delta}`, set to `0` when `lam` has
  more than `m` parts.
* `MvPolynomial.altPart_mul_hsymm` : the Pieri rule satisfied by the alternants `a_{lam+delta}`.
* `MvPolynomial.alt_partVec_eq_schurPoly_mul` : the bialternant formula.
-/

namespace MvPolynomial

open List MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### The staircase shift -/

/-- The exponent vector `lam + delta` attached to a partition `lam`, where
`delta i = m - 1 - i` is the staircase vector. -/
def partVec (m : ℕ) (lam : List ℕ) : Fin m → ℕ := fun i => lam.getD i 0 + (m - 1 - (i : ℕ))

@[simp] lemma partVec_apply (lam : List ℕ) (i : Fin m) :
    partVec m lam i = lam.getD i 0 + (m - 1 - (i : ℕ)) := rfl

lemma le_partVec (lam : List ℕ) (i : Fin m) : m - 1 - (i : ℕ) ≤ partVec m lam i :=
  Nat.le_add_left _ _

/-- The staircase shift of a partition is strictly decreasing, hence antitone. -/
lemma partVec_antitone {lam : List ℕ} (hlam : IsPart lam) : Antitone (partVec m lam) := by
  intro i j hij
  have hle : (i : ℕ) ≤ (j : ℕ) := hij
  have h1 : lam.getD (j : ℕ) 0 ≤ lam.getD (i : ℕ) 0 := hlam.getD_antitone hle
  have h2 : m - 1 - (j : ℕ) ≤ m - 1 - (i : ℕ) := by omega
  simp only [partVec_apply]
  omega

lemma sum_partVec {lam : List ℕ} (hlen : lam.length ≤ m) :
    ∑ i, partVec m lam i = lam.sum + ∑ i ∈ Finset.range m, (m - 1 - i) := by
  rw [sum_eq_sum_range_getD lam hlen, ← Finset.sum_add_distrib]
  exact Fintype.sum_equiv (finCongr rfl) _ _ (fun i => rfl) |>.trans
    (Finset.sum_range fun i => lam.getD i 0 + (m - 1 - i)).symm

/-- The partition attached to an exponent vector, by subtracting the staircase. -/
def vecPart (m : ℕ) (c : Fin m → ℕ) : List ℕ :=
  shapeOfFn m (fun i => (if h : i < m then c ⟨i, h⟩ else 0) - (m - 1 - i))

lemma getD_vecPart (c : Fin m → ℕ) (i : Fin m) :
    (vecPart m c).getD (i : ℕ) 0 = c i - (m - 1 - (i : ℕ)) := by
  rw [vecPart, getD_shapeOfFn, ite_eq_left i.isLt, dite_eq_left i.isLt]

lemma getD_vecPart_of_le {c : Fin m → ℕ} {i : ℕ} (hi : m ≤ i) :
    (vecPart m c).getD i 0 = 0 :=
  List.getD_eq_default _ _ (le_trans (length_shapeOfFn_le _ _) hi)

lemma length_vecPart_le (c : Fin m → ℕ) : (vecPart m c).length ≤ m :=
  length_shapeOfFn_le _ _

lemma vecPart_partVec {lam : List ℕ} (hlam : IsPart lam) (hlen : lam.length ≤ m) :
    vecPart m (partVec m lam) = lam := by
  rw [vecPart]
  rw [show (fun i => (if h : i < m then partVec m lam ⟨i, h⟩ else 0) - (m - 1 - i))
      = fun i => lam.getD i 0 from ?_]
  · exact shapeOfFn_getD hlam hlen
  · funext i
    by_cases hi : i < m
    · simp [hi]
    · rw [dite_eq_right hi, List.getD_eq_default _ _ (by omega)]
      simp

lemma partVec_vecPart {c : Fin m → ℕ} (hc : ∀ i : Fin m, m - 1 - (i : ℕ) ≤ c i) :
    partVec m (vecPart m c) = c := by
  funext i
  rw [partVec_apply, getD_vecPart]
  have := hc i
  omega

/-! ### Horizontal strips -/

/-- Under the staircase shift, horizontal strips of partitions correspond to the
horizontal strips of exponent vectors of `MvPolynomial.IsAltStrip`. -/
lemma isAltStrip_partVec_of_horizStrip {mu lam : List ℕ} (h : HorizStrip lam mu) :
    IsAltStrip (partVec m mu) (partVec m lam) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · have := h.getD_le (i : ℕ)
    simp only [partVec_apply]
    omega
  · have h1 : lam.getD (j : ℕ) 0 ≤ mu.getD (i : ℕ) 0 := by
      rw [hij]; exact h.getD_succ_le (i : ℕ)
    have h2 : (j : ℕ) < m := j.isLt
    simp only [partVec_apply]
    omega

lemma horizStrip_of_isAltStrip {mu : List ℕ} (hmu : IsPart mu) (hmulen : mu.length ≤ m)
    {c : Fin m → ℕ} (h : IsAltStrip (partVec m mu) c) :
    HorizStrip (vecPart m c) mu := by
  obtain ⟨hone, htwo⟩ := h
  have h : IsAltStrip (partVec m mu) c := ⟨hone, htwo⟩
  have hge : ∀ i : Fin m, m - 1 - (i : ℕ) ≤ c i := fun i =>
    le_trans (le_partVec mu i) (h.1 i)
  refine ⟨(hmu.included_iff_getD).2 fun i => ?_, fun i => ?_⟩
  · by_cases hi : i < m
    · have := hone ⟨i, hi⟩
      rw [getD_vecPart c ⟨i, hi⟩]
      simp only [partVec_apply] at this ⊢
      omega
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Nat.zero_le _
  · by_cases hi : i + 1 < m
    · have hi' : i < m := by omega
      have := htwo ⟨i, hi'⟩ ⟨i + 1, hi⟩ rfl
      rw [getD_vecPart c ⟨i + 1, hi⟩]
      simp only [partVec_apply] at this ⊢
      have hge' := hge ⟨i + 1, hi⟩
      simp only at hge'
      omega
    · rw [getD_vecPart_of_le (by omega)]
      exact Nat.zero_le _

lemma isPart_vecPart {mu : List ℕ} {c : Fin m → ℕ} (h : IsAltStrip (partVec m mu) c) :
    IsPart (vecPart m c) := by
  obtain ⟨hone, htwo⟩ := h
  rw [vecPart]
  refine isPart_shapeOfFn fun i => ?_
  by_cases hi : i + 1 < m
  · have hi' : i < m := by omega
    have h1 := htwo ⟨i, hi'⟩ ⟨i + 1, hi⟩ rfl
    have h2 := hone ⟨i, hi'⟩
    simp only [partVec_apply] at h1 h2
    rw [dite_eq_left hi, dite_eq_left hi']
    omega
  · simp [dite_eq_right hi]

/-- The size of the partition attached to a horizontal strip of exponent vectors. -/
lemma sum_vecPart {mu : List ℕ} (hmulen : mu.length ≤ m) {r : ℕ}
    {d : Fin m →₀ ℕ} (hd : ∑ i, d i = r) :
    (vecPart m (partVec m mu + ⇑d)).sum = mu.sum + r := by
  set c : Fin m → ℕ := partVec m mu + ⇑d with hc
  have hge : ∀ i : Fin m, m - 1 - (i : ℕ) ≤ c i := fun i =>
    le_trans (le_partVec mu i) (Nat.le_add_right _ _)
  have hpt : ∀ i : Fin m, c i = (vecPart m c).getD (i : ℕ) 0 + (m - 1 - (i : ℕ)) := by
    intro i
    rw [getD_vecPart c i]
    have := hge i
    omega
  have hL : ∑ i : Fin m, c i = (mu.sum + ∑ i ∈ Finset.range m, (m - 1 - i)) + r := by
    have : ∑ i : Fin m, c i = ∑ i : Fin m, partVec m mu i + ∑ i : Fin m, d i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => rfl
    rw [this, sum_partVec hmulen, hd]
  have hR : ∑ i : Fin m, c i = (vecPart m c).sum + ∑ i ∈ Finset.range m, (m - 1 - i) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hpt i, Finset.sum_add_distrib,
      Fin.sum_univ_eq_sum_range (fun i => (vecPart m c).getD i 0) m,
      Fin.sum_univ_eq_sum_range (fun i => m - 1 - i) m,
      ← sum_eq_sum_range_getD _ (length_vecPart_le c)]
  omega

/-! ### The Pieri rule for the shifted alternants -/

/-- The alternant attached to a partition `lam` with at most `m` parts, that is the
alternant of the exponent vector `lam + delta`. -/
noncomputable def altPart (m : ℕ) (R : Type*) [CommRing R] (lam : List ℕ) :
    MvPolynomial (Fin m) R :=
  if lam.length ≤ m then alt m R (partVec m lam) else 0

lemma altPart_of_le {lam : List ℕ} (h : lam.length ≤ m) :
    altPart m R lam = alt m R (partVec m lam) := ite_eq_left h

lemma altPart_of_lt {lam : List ℕ} (h : m < lam.length) : altPart m R lam = 0 :=
  ite_eq_right (by omega)

/-- The exponent vector of a horizontal strip, as a finitely supported function. -/
noncomputable def stripFinsupp (m : ℕ) (mu lam : List ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => partVec m lam k - partVec m mu k)

lemma coe_stripFinsupp (mu lam : List ℕ) :
    ⇑(stripFinsupp m mu lam) = fun k => partVec m lam k - partVec m mu k := rfl

lemma add_stripFinsupp {mu lam : List ℕ} (h : Included mu lam) :
    partVec m mu + ⇑(stripFinsupp m mu lam) = partVec m lam := by
  funext k
  have := h.getD_le (k : ℕ)
  simp only [Pi.add_apply, coe_stripFinsupp, partVec_apply]
  omega

lemma sum_stripFinsupp {mu lam : List ℕ} (h : Included mu lam) (hmulen : mu.length ≤ m)
    (hlamlen : lam.length ≤ m) :
    ∑ k, (stripFinsupp m mu lam) k = lam.sum - mu.sum := by
  have hkey : ∑ k, (stripFinsupp m mu lam) k + ∑ k, partVec m mu k = ∑ k, partVec m lam k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := h.getD_le (k : ℕ)
    simp only [coe_stripFinsupp, partVec_apply]
    omega
  rw [sum_partVec hmulen, sum_partVec hlamlen] at hkey
  have : mu.sum ≤ lam.sum := h.sum_le
  omega

/-- **The Pieri rule for alternants**, in terms of partitions. -/
theorem altPart_mul_hsymm {mu : List ℕ} (hmu : IsPart mu) (r : ℕ) :
    altPart m R mu * hsymm (Fin m) R r
      = ∑ lam ∈ partFinset (mu.sum + r), if HorizStrip lam mu then altPart m R lam else 0 := by
  classical
  by_cases hmulen : mu.length ≤ m
  swap
  · rw [altPart_of_lt (by omega), zero_mul]
    refine (Finset.sum_eq_zero fun lam _ => ?_).symm
    split_ifs with hstrip
    · exact altPart_of_lt (lt_of_lt_of_le (by omega) hstrip.included.length_le)
    · rfl
  rw [altPart_of_le hmulen, mul_comm, hsymm_mul_alt_strip (partVec_antitone hmu) r,
    ← Finset.sum_filter]
  -- discard the shapes with more than `m` rows
  have hsub : ∑ lam ∈ ((partFinset (mu.sum + r)).filter fun lam => HorizStrip lam mu).filter
        (fun lam => lam.length ≤ m), altPart m R lam
      = ∑ lam ∈ (partFinset (mu.sum + r)).filter fun lam => HorizStrip lam mu,
          altPart m R lam := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun lam hlam hnot => ?_
    exact altPart_of_lt (by
      by_contra hle
      exact hnot (Finset.mem_filter.2 ⟨hlam, by omega⟩))
  rw [← hsub]
  refine Finset.sum_nbij' (fun d => vecPart m (partVec m mu + ⇑d)) (stripFinsupp m mu)
    ?_ ?_ ?_ ?_ ?_
  · -- the image of a strip vector is a shape
    intro d hd
    obtain ⟨hmem, hstrip⟩ := Finset.mem_filter.1 hd
    have hdsum : ∑ i, d i = r := (Finset.mem_finsuppAntidiag.1 hmem).1
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨mem_partFinset.2 ⟨isPart_vecPart hstrip, ?_⟩,
      horizStrip_of_isAltStrip hmu hmulen hstrip⟩, length_vecPart_le _⟩
    exact sum_vecPart hmulen hdsum
  · -- the strip vector of a shape is a strip vector
    intro lam hlam
    obtain ⟨hlam', hlen⟩ := Finset.mem_filter.1 hlam
    obtain ⟨hlam'', hstrip⟩ := Finset.mem_filter.1 hlam'
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hlam''
    have hadd : partVec m mu + ⇑(stripFinsupp m mu lam) = partVec m lam :=
      add_stripFinsupp hstrip.included
    refine Finset.mem_filter.2 ⟨Finset.mem_finsuppAntidiag.2 ⟨?_, by simp⟩, ?_⟩
    · change ∑ k, (stripFinsupp m mu lam) k = r
      rw [sum_stripFinsupp hstrip.included hmulen hlen, hsum]
      omega
    · rw [hadd]
      exact isAltStrip_partVec_of_horizStrip hstrip
  · -- left inverse
    intro d hd
    obtain ⟨-, hstrip⟩ := Finset.mem_filter.1 hd
    have hge : ∀ i : Fin m, m - 1 - (i : ℕ) ≤ (partVec m mu + ⇑d) i := fun i =>
      le_trans (le_partVec mu i) (hstrip.1 i)
    have hpv : partVec m (vecPart m (partVec m mu + ⇑d)) = partVec m mu + ⇑d :=
      partVec_vecPart hge
    refine Finsupp.ext fun k => ?_
    have := congrFun hpv k
    simp only [coe_stripFinsupp, Pi.add_apply] at this ⊢
    omega
  · -- right inverse
    intro lam hlam
    obtain ⟨hlam', hlen⟩ := Finset.mem_filter.1 hlam
    obtain ⟨hlam'', hstrip⟩ := Finset.mem_filter.1 hlam'
    obtain ⟨hpart, -⟩ := mem_partFinset.1 hlam''
    change vecPart m (partVec m mu + ⇑(stripFinsupp m mu lam)) = lam
    rw [add_stripFinsupp hstrip.included, vecPart_partVec hpart hlen]
  · -- the summands agree
    intro d hd
    obtain ⟨-, hstrip⟩ := Finset.mem_filter.1 hd
    have hge : ∀ i : Fin m, m - 1 - (i : ℕ) ≤ (partVec m mu + ⇑d) i := fun i =>
      le_trans (le_partVec mu i) (hstrip.1 i)
    rw [altPart_of_le (length_vecPart_le _), partVec_vecPart hge]

/-! ### The bialternant formula -/

/-- The expansion of the products `h_lam * a_delta` along the shifted alternants. -/
theorem hProd_mul_altPart_nil (lam : List ℕ) :
    hProd m R lam * altPart m R []
      = ∑ mu ∈ partFinset lam.sum,
          (kostkaNum lam.length mu (contentOf lam) : R) • altPart m R mu :=
  hProd_mul_eq_sum_kostkaNum m (altPart m R) (fun _ hmu r => altPart_mul_hsymm hmu r) lam

/-- **The bialternant formula**, in the form `a_{lam+delta} = s_lam * a_delta`, for all
partitions at once. -/
theorem altPart_eq_schurPoly_mul {lam : List ℕ} (hlam : IsPart lam) :
    altPart m R lam = schurPoly (Fin m) R lam * altPart m R [] := by
  classical
  suffices H : ∀ k n : ℕ, ∀ nu : List ℕ, IsPart nu → nu.sum = n →
      (n + 1) * n - domWeight n nu ≤ k →
      altPart m R nu = schurPoly (Fin m) R nu * altPart m R [] by
    exact H _ lam.sum lam hlam rfl le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n nu hnu hnusum hk
    have hE1 : hProd m R nu * altPart m R []
        = ∑ mu ∈ partFinset n, (kostka mu nu : R) • altPart m R mu := by
      rw [hProd_mul_altPart_nil nu, hnusum]
      exact Finset.sum_congr rfl fun mu _ => by rw [kostkaNum_eq_kostka hnu mu]
    have hE2 : hProd m R nu
        = ∑ mu ∈ partFinset n, (kostka mu nu : R) • schurPoly (Fin m) R mu := by
      rw [hProd_eq_sum_kostka m hnu, hnusum]
    have hkey : ∑ mu ∈ partFinset n, (kostka mu nu : R) • altPart m R mu
        = ∑ mu ∈ partFinset n,
            (kostka mu nu : R) • (schurPoly (Fin m) R mu * altPart m R []) := by
      rw [← hE1, hE2, Finset.sum_mul]
      exact Finset.sum_congr rfl fun mu _ => by rw [smul_mul_assoc]
    have hmem : nu ∈ partFinset n := mem_partFinset.2 ⟨hnu, hnusum⟩
    have hrest : ∀ mu ∈ (partFinset n).erase nu,
        (kostka mu nu : R) • altPart m R mu
          = (kostka mu nu : R) • (schurPoly (Fin m) R mu * altPart m R []) := by
      intro mu hmu
      have hmune : mu ≠ nu := Finset.ne_of_mem_erase hmu
      obtain ⟨hmupart, hmusum⟩ := mem_partFinset.1 (Finset.mem_of_mem_erase hmu)
      by_cases hk0 : kostka mu nu = 0
      · rw [hk0, Nat.cast_zero, zero_smul, zero_smul]
      · have hdom : Partdom nu mu := partdom_of_kostka_ne_zero hk0
        have hlt : domWeight n nu < domWeight n mu := by
          rcases lt_or_eq_of_le (domWeight_le_domWeight (n := n) hdom) with h | h
          · exact h
          · exact absurd (eq_of_partdom_of_domWeight_eq hnu hmupart hnusum hmusum hdom
              (le_of_eq h.symm)).symm hmune
        have hbd : domWeight n mu ≤ (n + 1) * n := by
          rw [domWeight]
          calc ∑ j ∈ Finset.range (n + 1), (mu.take j).sum
              ≤ ∑ _j ∈ Finset.range (n + 1), n :=
                Finset.sum_le_sum fun j _ => hmusum ▸ sum_take_le_sum mu j
            _ = (n + 1) * n := by simp [mul_comm]
        rw [ih ((n + 1) * n - domWeight n mu) (by omega) n mu hmupart hmusum le_rfl]
    have hsplit1 := Finset.add_sum_erase (partFinset n)
      (fun mu => (kostka mu nu : R) • altPart m R mu) hmem
    have hsplit2 := Finset.add_sum_erase (partFinset n)
      (fun mu => (kostka mu nu : R) • (schurPoly (Fin m) R mu * altPart m R [])) hmem
    rw [← hsplit1, ← hsplit2, Finset.sum_congr rfl hrest] at hkey
    simp only [kostka_self hnu, Nat.cast_one, one_smul] at hkey
    exact add_right_cancel hkey

/-- **Jacobi's bialternant formula**: the alternant of the exponent vector `lam + delta`
is the product of the Schur polynomial of shape `lam` by the Vandermonde alternant of the
staircase `delta`. -/
theorem alt_partVec_eq_schurPoly_mul {lam : List ℕ} (hlam : IsPart lam)
    (hlen : lam.length ≤ m) :
    alt m R (partVec m lam) = schurPoly (Fin m) R lam * alt m R (partVec m []) := by
  rw [← altPart_of_le hlen, ← altPart_of_le (m := m) (R := R) (lam := ([] : List ℕ)) (by simp)]
  exact altPart_eq_schurPoly_mul hlam

end MvPolynomial
