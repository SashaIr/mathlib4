/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Alternant.Pieri
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.CompleteHomogeneous

/-!
# The bialternant formula for Schur polynomials

Following `theories/MPoly/Schur_altdef.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove Jacobi's bialternant
definition of the Schur polynomials:

`a_{μ + delta} = s_μ * a_delta`,

where `delta = (m-1, m-2, ..., 1, 0)` is the staircase vector and `a_b` is the alternant
attached to the exponent vector `b`.

The proof combines the Pieri rule for alternants (`MvPolynomial.hsymm_mul_alt_strip`) with the
Pieri rule for Schur polynomials (`MvPolynomial.schurPoly_mul_hsymm`): both families satisfy the
same recursion, hence both expand along the Kostka numbers, and the unitriangularity of
the Kostka matrix lets us identify them.

## Main definitions and results

* `MvPolynomial.partVec m μ` : the exponent vector `μ + delta` of a partition `μ`.
* `MvPolynomial.altPart m R μ` : the alternant `a_{μ + delta}`, set to `0` when `μ` has
  more than `m` parts.
* `MvPolynomial.altPart_mul_hsymm` : the Pieri rule satisfied by the alternants `a_{μ+delta}`.
* `MvPolynomial.alt_partVec_eq_schurPoly_mul` : the bialternant formula.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### The staircase shift -/

/-- The exponent vector `μ + delta` attached to a partition `μ`, where
`delta i = m - 1 - i` is the staircase vector. -/
def partVec (m : ℕ) (μ : List ℕ) : Fin m → ℕ := fun i => μ.getD i 0 + (m - 1 - (i : ℕ))

@[simp] lemma partVec_apply (μ : List ℕ) (i : Fin m) :
    partVec m μ i = μ.getD i 0 + (m - 1 - (i : ℕ)) := rfl

lemma le_partVec (μ : List ℕ) (i : Fin m) : m - 1 - (i : ℕ) ≤ partVec m μ i :=
  Nat.le_add_left _ _

/-- The staircase shift of a partition is strictly decreasing, hence antitone. -/
lemma partVec_antitone {μ : List ℕ} (hμ : IsPart μ) : Antitone (partVec m μ) := by
  intro i j hij
  have hle : (i : ℕ) ≤ (j : ℕ) := hij
  have h1 : μ.getD (j : ℕ) 0 ≤ μ.getD (i : ℕ) 0 := hμ.getD_antitone hle
  have h2 : m - 1 - (j : ℕ) ≤ m - 1 - (i : ℕ) := by omega
  simp only [partVec_apply]
  omega

lemma sum_partVec {μ : List ℕ} (hlen : μ.length ≤ m) :
    ∑ i, partVec m μ i = μ.sum + ∑ i ∈ Finset.range m, (m - 1 - i) := by
  rw [sum_eq_sum_range_getD μ hlen, ← Finset.sum_add_distrib]
  exact Fintype.sum_equiv (finCongr rfl) _ _ (fun i => rfl) |>.trans
    (Finset.sum_range fun i => μ.getD i 0 + (m - 1 - i)).symm

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

lemma vecPart_partVec {μ : List ℕ} (hμ : IsPart μ) (hlen : μ.length ≤ m) :
    vecPart m (partVec m μ) = μ := by
  rw [vecPart]
  rw [show (fun i => (if h : i < m then partVec m μ ⟨i, h⟩ else 0) - (m - 1 - i))
      = fun i => μ.getD i 0 from ?_]
  · exact shapeOfFn_getD hμ hlen
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
lemma isAltStrip_partVec_of_horizStrip {ν μ : List ℕ} (h : HorizStrip μ ν) :
    IsAltStrip (partVec m ν) (partVec m μ) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · have := h.getD_le (i : ℕ)
    simp only [partVec_apply]
    omega
  · have h1 : μ.getD (j : ℕ) 0 ≤ ν.getD (i : ℕ) 0 := by
      rw [hij]; exact h.getD_succ_le (i : ℕ)
    have h2 : (j : ℕ) < m := j.isLt
    simp only [partVec_apply]
    omega

lemma horizStrip_of_isAltStrip {μ : List ℕ} (hμ : IsPart μ) (hμlen : μ.length ≤ m)
    {c : Fin m → ℕ} (h : IsAltStrip (partVec m μ) c) :
    HorizStrip (vecPart m c) μ := by
  obtain ⟨hone, htwo⟩ := h
  have h : IsAltStrip (partVec m μ) c := ⟨hone, htwo⟩
  have hge : ∀ i : Fin m, m - 1 - (i : ℕ) ≤ c i := fun i =>
    le_trans (le_partVec μ i) (h.1 i)
  refine ⟨(hμ.included_iff_getD).2 fun i => ?_, fun i => ?_⟩
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

lemma isPart_vecPart {μ : List ℕ} {c : Fin m → ℕ} (h : IsAltStrip (partVec m μ) c) :
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
lemma sum_vecPart {μ : List ℕ} (hμlen : μ.length ≤ m) {r : ℕ}
    {d : Fin m →₀ ℕ} (hd : ∑ i, d i = r) :
    (vecPart m (partVec m μ + ⇑d)).sum = μ.sum + r := by
  set c : Fin m → ℕ := partVec m μ + ⇑d with hc
  have hge : ∀ i : Fin m, m - 1 - (i : ℕ) ≤ c i := fun i =>
    le_trans (le_partVec μ i) (Nat.le_add_right _ _)
  have hpt : ∀ i : Fin m, c i = (vecPart m c).getD (i : ℕ) 0 + (m - 1 - (i : ℕ)) := by
    intro i
    rw [getD_vecPart c i]
    have := hge i
    omega
  have hL : ∑ i : Fin m, c i = (μ.sum + ∑ i ∈ Finset.range m, (m - 1 - i)) + r := by
    have : ∑ i : Fin m, c i = ∑ i : Fin m, partVec m μ i + ∑ i : Fin m, d i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => rfl
    rw [this, sum_partVec hμlen, hd]
  have hR : ∑ i : Fin m, c i = (vecPart m c).sum + ∑ i ∈ Finset.range m, (m - 1 - i) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hpt i, Finset.sum_add_distrib,
      Fin.sum_univ_eq_sum_range (fun i => (vecPart m c).getD i 0) m,
      Fin.sum_univ_eq_sum_range (fun i => m - 1 - i) m,
      ← sum_eq_sum_range_getD _ (length_vecPart_le c)]
  omega

/-! ### The Pieri rule for the shifted alternants -/

/-- The alternant attached to a partition `μ` with at most `m` parts, that is the
alternant of the exponent vector `μ + delta`. -/
noncomputable def altPart (m : ℕ) (R : Type*) [CommRing R] (μ : List ℕ) :
    MvPolynomial (Fin m) R :=
  if μ.length ≤ m then alt m R (partVec m μ) else 0

lemma altPart_of_le {μ : List ℕ} (h : μ.length ≤ m) :
    altPart m R μ = alt m R (partVec m μ) := ite_eq_left h

lemma altPart_of_lt {μ : List ℕ} (h : m < μ.length) : altPart m R μ = 0 :=
  ite_eq_right (by omega)

/-- The exponent vector of a horizontal strip, as a finitely supported function. -/
noncomputable def stripFinsupp (m : ℕ) (ν μ : List ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => partVec m μ k - partVec m ν k)

lemma coe_stripFinsupp (ν μ : List ℕ) :
    ⇑(stripFinsupp m ν μ) = fun k => partVec m μ k - partVec m ν k := rfl

lemma add_stripFinsupp {ν μ : List ℕ} (h : Included ν μ) :
    partVec m ν + ⇑(stripFinsupp m ν μ) = partVec m μ := by
  funext k
  have := h.getD_le (k : ℕ)
  simp only [Pi.add_apply, coe_stripFinsupp, partVec_apply]
  omega

lemma sum_stripFinsupp {ν μ : List ℕ} (h : Included ν μ) (hνlen : ν.length ≤ m)
    (hμlen : μ.length ≤ m) :
    ∑ k, (stripFinsupp m ν μ) k = μ.sum - ν.sum := by
  have hkey : ∑ k, (stripFinsupp m ν μ) k + ∑ k, partVec m ν k = ∑ k, partVec m μ k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := h.getD_le (k : ℕ)
    simp only [coe_stripFinsupp, partVec_apply]
    omega
  rw [sum_partVec hνlen, sum_partVec hμlen] at hkey
  have : ν.sum ≤ μ.sum := h.sum_le
  omega

/-- **The Pieri rule for alternants**, in terms of partitions. -/
theorem altPart_mul_hsymm {ν : List ℕ} (hν : IsPart ν) (r : ℕ) :
    altPart m R ν * hsymm (Fin m) R r
      = ∑ μ ∈ partFinset (ν.sum + r), if HorizStrip μ ν then altPart m R μ else 0 := by
  classical
  by_cases hνlen : ν.length ≤ m
  swap
  · rw [altPart_of_lt (by omega), zero_mul]
    refine (Finset.sum_eq_zero fun μ _ => ?_).symm
    split_ifs with hstrip
    · exact altPart_of_lt (lt_of_lt_of_le (by omega) hstrip.included.length_le)
    · rfl
  rw [altPart_of_le hνlen, mul_comm, hsymm_mul_alt_strip (partVec_antitone hν) r,
    ← Finset.sum_filter]
  -- discard the shapes with more than `m` rows
  have hsub : ∑ μ ∈ ((partFinset (ν.sum + r)).filter fun μ => HorizStrip μ ν).filter
        (fun μ => μ.length ≤ m), altPart m R μ
      = ∑ μ ∈ (partFinset (ν.sum + r)).filter fun μ => HorizStrip μ ν,
          altPart m R μ := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun μ hμ hnot => ?_
    exact altPart_of_lt (by
      by_contra hle
      exact hnot (Finset.mem_filter.2 ⟨hμ, by omega⟩))
  rw [← hsub]
  refine Finset.sum_nbij' (fun d => vecPart m (partVec m ν + ⇑d)) (stripFinsupp m ν)
    ?_ ?_ ?_ ?_ ?_
  · -- the image of a strip vector is a shape
    intro d hd
    obtain ⟨hmem, hstrip⟩ := Finset.mem_filter.1 hd
    have hdsum : ∑ i, d i = r := (Finset.mem_finsuppAntidiag.1 hmem).1
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨mem_partFinset.2 ⟨isPart_vecPart hstrip, ?_⟩,
      horizStrip_of_isAltStrip hν hνlen hstrip⟩, length_vecPart_le _⟩
    exact sum_vecPart hνlen hdsum
  · -- the strip vector of a shape is a strip vector
    intro μ hμ
    obtain ⟨hμ', hlen⟩ := Finset.mem_filter.1 hμ
    obtain ⟨hμ'', hstrip⟩ := Finset.mem_filter.1 hμ'
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hμ''
    have hadd : partVec m ν + ⇑(stripFinsupp m ν μ) = partVec m μ :=
      add_stripFinsupp hstrip.included
    refine Finset.mem_filter.2 ⟨Finset.mem_finsuppAntidiag.2 ⟨?_, by simp⟩, ?_⟩
    · change ∑ k, (stripFinsupp m ν μ) k = r
      rw [sum_stripFinsupp hstrip.included hνlen hlen, hsum]
      omega
    · rw [hadd]
      exact isAltStrip_partVec_of_horizStrip hstrip
  · -- left inverse
    intro d hd
    obtain ⟨-, hstrip⟩ := Finset.mem_filter.1 hd
    have hge : ∀ i : Fin m, m - 1 - (i : ℕ) ≤ (partVec m ν + ⇑d) i := fun i =>
      le_trans (le_partVec ν i) (hstrip.1 i)
    have hpv : partVec m (vecPart m (partVec m ν + ⇑d)) = partVec m ν + ⇑d :=
      partVec_vecPart hge
    refine Finsupp.ext fun k => ?_
    have := congrFun hpv k
    simp only [coe_stripFinsupp, Pi.add_apply] at this ⊢
    omega
  · -- right inverse
    intro μ hμ
    obtain ⟨hμ', hlen⟩ := Finset.mem_filter.1 hμ
    obtain ⟨hμ'', hstrip⟩ := Finset.mem_filter.1 hμ'
    obtain ⟨hpart, -⟩ := mem_partFinset.1 hμ''
    rw [add_stripFinsupp hstrip.included, vecPart_partVec hpart hlen]
  · -- the summands agree
    intro d hd
    obtain ⟨-, hstrip⟩ := Finset.mem_filter.1 hd
    have hge : ∀ i : Fin m, m - 1 - (i : ℕ) ≤ (partVec m ν + ⇑d) i := fun i =>
      le_trans (le_partVec ν i) (hstrip.1 i)
    rw [altPart_of_le (length_vecPart_le _), partVec_vecPart hge]

/-! ### The bialternant formula -/

/-- The expansion of the products `h_μ * a_delta` along the shifted alternants. -/
theorem hProd_mul_altPart_nil (μ : List ℕ) :
    hProd m R μ * altPart m R []
      = ∑ ν ∈ partFinset μ.sum,
          (kostkaNum μ.length ν (contentOf μ) : R) • altPart m R ν :=
  hProd_mul_eq_sum_kostkaNum m (altPart m R) (fun _ hν r => altPart_mul_hsymm hν r) μ

/-- **The bialternant formula**, in the form `a_{μ+delta} = s_μ * a_delta`, for all
partitions at once. -/
theorem altPart_eq_schurPoly_mul {μ : List ℕ} (hμ : IsPart μ) :
    altPart m R μ = schurPoly (Fin m) R μ * altPart m R [] := by
  classical
  suffices H : ∀ k n : ℕ, ∀ ρ : List ℕ, IsPart ρ → ρ.sum = n →
      (n + 1) * n - domWeight n ρ ≤ k →
      altPart m R ρ = schurPoly (Fin m) R ρ * altPart m R [] by
    exact H _ μ.sum μ hμ rfl le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n ρ hρ hρsum hk
    have hE1 : hProd m R ρ * altPart m R []
        = ∑ ν ∈ partFinset n, (kostka ν ρ : R) • altPart m R ν := by
      rw [hProd_mul_altPart_nil ρ, hρsum]
      exact Finset.sum_congr rfl fun ν _ => by rw [kostkaNum_eq_kostka hρ ν]
    have hE2 : hProd m R ρ
        = ∑ ν ∈ partFinset n, (kostka ν ρ : R) • schurPoly (Fin m) R ν := by
      rw [hProd_eq_sum_kostka m hρ, hρsum]
    have hkey : ∑ ν ∈ partFinset n, (kostka ν ρ : R) • altPart m R ν
        = ∑ ν ∈ partFinset n,
            (kostka ν ρ : R) • (schurPoly (Fin m) R ν * altPart m R []) := by
      rw [← hE1, hE2, Finset.sum_mul]
      exact Finset.sum_congr rfl fun ν _ => by rw [smul_mul_assoc]
    have hmem : ρ ∈ partFinset n := mem_partFinset.2 ⟨hρ, hρsum⟩
    have hrest : ∀ ν ∈ (partFinset n).erase ρ,
        (kostka ν ρ : R) • altPart m R ν
          = (kostka ν ρ : R) • (schurPoly (Fin m) R ν * altPart m R []) := by
      intro ν hν
      have hνne : ν ≠ ρ := Finset.ne_of_mem_erase hν
      obtain ⟨hνpart, hνsum⟩ := mem_partFinset.1 (Finset.mem_of_mem_erase hν)
      by_cases hk0 : kostka ν ρ = 0
      · rw [hk0, Nat.cast_zero, zero_smul, zero_smul]
      · have hdom : Partdom ρ ν := partdom_of_kostka_ne_zero hk0
        have hlt : domWeight n ρ < domWeight n ν := by
          rcases lt_or_eq_of_le (domWeight_le_domWeight (n := n) hdom) with h | h
          · exact h
          · exact absurd (eq_of_partdom_of_domWeight_eq hρ hνpart hρsum hνsum hdom
              (le_of_eq h.symm)).symm hνne
        have hbd : domWeight n ν ≤ (n + 1) * n := by
          rw [domWeight]
          calc ∑ j ∈ Finset.range (n + 1), (ν.take j).sum
              ≤ ∑ _j ∈ Finset.range (n + 1), n :=
                Finset.sum_le_sum fun j _ => hνsum ▸ sum_take_le_sum ν j
            _ = (n + 1) * n := by simp [mul_comm]
        rw [ih ((n + 1) * n - domWeight n ν) (by omega) n ν hνpart hνsum le_rfl]
    have hsplit1 := Finset.add_sum_erase (partFinset n)
      (fun ν => (kostka ν ρ : R) • altPart m R ν) hmem
    have hsplit2 := Finset.add_sum_erase (partFinset n)
      (fun ν => (kostka ν ρ : R) • (schurPoly (Fin m) R ν * altPart m R [])) hmem
    rw [← hsplit1, ← hsplit2, Finset.sum_congr rfl hrest] at hkey
    simp only [kostka_self hρ, Nat.cast_one, one_smul] at hkey
    exact add_right_cancel hkey

/-- **Jacobi's bialternant formula**: the alternant of the exponent vector `μ + delta`
is the product of the Schur polynomial of shape `μ` by the Vandermonde alternant of the
staircase `delta`. -/
theorem alt_partVec_eq_schurPoly_mul {μ : List ℕ} (hμ : IsPart μ)
    (hlen : μ.length ≤ m) :
    alt m R (partVec m μ) = schurPoly (Fin m) R μ * alt m R (partVec m []) := by
  rw [← altPart_of_le hlen, ← altPart_of_le (m := m) (R := R) (μ := ([] : List ℕ)) (by simp)]
  exact altPart_eq_schurPoly_mul hμ

end MvPolynomial
