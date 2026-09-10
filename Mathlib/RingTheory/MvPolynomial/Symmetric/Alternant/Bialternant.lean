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

`a_{η + delta} = s_η * a_delta`,

where `delta = (m-1, m-2, ..., 1, 0)` is the staircase vector and `a_b` is the alternant
attached to the exponent vector `b`.

The proof combines the Pieri rule for alternants (`MvPolynomial.hsymm_mul_alt_strip`) with the
Pieri rule for Schur polynomials (`MvPolynomial.schurPoly_mul_hsymm`): both families satisfy the
same recursion, hence both expand along the Kostka numbers, and the unitriangularity of
the Kostka matrix lets us identify them.

## Main definitions and results

* `MvPolynomial.partVec m η` : the exponent vector `η + delta` of a partition `η`.
* `MvPolynomial.altPart m R η` : the alternant `a_{η + delta}`, set to `0` when `η` has
  more than `m` parts.
* `MvPolynomial.altPart_mul_hsymm` : the Pieri rule satisfied by the alternants `a_{η+delta}`.
* `MvPolynomial.alt_partVec_eq_schurPoly_mul` : the bialternant formula.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### The staircase shift -/

/-- The exponent vector `η + delta` attached to a partition `η`, where
`delta i = m - 1 - i` is the staircase vector. -/
def partVec (m : ℕ) (η : List ℕ) : Fin m → ℕ := fun i => η.getD i 0 + (m - 1 - (i : ℕ))

@[simp] lemma partVec_apply (η : List ℕ) (i : Fin m) :
    partVec m η i = η.getD i 0 + (m - 1 - (i : ℕ)) := rfl

lemma le_partVec (η : List ℕ) (i : Fin m) : m - 1 - (i : ℕ) ≤ partVec m η i :=
  Nat.le_add_left _ _

/-- The staircase shift of a partition is strictly decreasing, hence antitone. -/
lemma partVec_antitone {η : List ℕ} (hη : IsPart η) : Antitone (partVec m η) := by
  intro i j hij
  have hle : (i : ℕ) ≤ (j : ℕ) := hij
  have h1 : η.getD (j : ℕ) 0 ≤ η.getD (i : ℕ) 0 := hη.getD_antitone hle
  have h2 : m - 1 - (j : ℕ) ≤ m - 1 - (i : ℕ) := by omega
  simp only [partVec_apply]
  omega

lemma sum_partVec {η : List ℕ} (hlen : η.length ≤ m) :
    ∑ i, partVec m η i = η.sum + ∑ i ∈ Finset.range m, (m - 1 - i) := by
  rw [sum_eq_sum_range_getD η hlen, ← Finset.sum_add_distrib]
  exact Fintype.sum_equiv (finCongr rfl) _ _ (fun i => rfl) |>.trans
    (Finset.sum_range fun i => η.getD i 0 + (m - 1 - i)).symm

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

lemma vecPart_partVec {η : List ℕ} (hη : IsPart η) (hlen : η.length ≤ m) :
    vecPart m (partVec m η) = η := by
  rw [vecPart]
  rw [show (fun i => (if h : i < m then partVec m η ⟨i, h⟩ else 0) - (m - 1 - i))
      = fun i => η.getD i 0 from ?_]
  · exact shapeOfFn_getD hη hlen
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
lemma isAltStrip_partVec_of_horizStrip {μ η : List ℕ} (h : HorizStrip η μ) :
    IsAltStrip (partVec m μ) (partVec m η) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · have := h.getD_le (i : ℕ)
    simp only [partVec_apply]
    omega
  · have h1 : η.getD (j : ℕ) 0 ≤ μ.getD (i : ℕ) 0 := by
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

/-- The alternant attached to a partition `η` with at most `m` parts, that is the
alternant of the exponent vector `η + delta`. -/
noncomputable def altPart (m : ℕ) (R : Type*) [CommRing R] (η : List ℕ) :
    MvPolynomial (Fin m) R :=
  if η.length ≤ m then alt m R (partVec m η) else 0

lemma altPart_of_le {η : List ℕ} (h : η.length ≤ m) :
    altPart m R η = alt m R (partVec m η) := ite_eq_left h

lemma altPart_of_lt {η : List ℕ} (h : m < η.length) : altPart m R η = 0 :=
  ite_eq_right (by omega)

/-- The exponent vector of a horizontal strip, as a finitely supported function. -/
noncomputable def stripFinsupp (m : ℕ) (μ η : List ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => partVec m η k - partVec m μ k)

lemma coe_stripFinsupp (μ η : List ℕ) :
    ⇑(stripFinsupp m μ η) = fun k => partVec m η k - partVec m μ k := rfl

lemma add_stripFinsupp {μ η : List ℕ} (h : Included μ η) :
    partVec m μ + ⇑(stripFinsupp m μ η) = partVec m η := by
  funext k
  have := h.getD_le (k : ℕ)
  simp only [Pi.add_apply, coe_stripFinsupp, partVec_apply]
  omega

lemma sum_stripFinsupp {μ η : List ℕ} (h : Included μ η) (hμlen : μ.length ≤ m)
    (hηlen : η.length ≤ m) :
    ∑ k, (stripFinsupp m μ η) k = η.sum - μ.sum := by
  have hkey : ∑ k, (stripFinsupp m μ η) k + ∑ k, partVec m μ k = ∑ k, partVec m η k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := h.getD_le (k : ℕ)
    simp only [coe_stripFinsupp, partVec_apply]
    omega
  rw [sum_partVec hμlen, sum_partVec hηlen] at hkey
  have : μ.sum ≤ η.sum := h.sum_le
  omega

/-- **The Pieri rule for alternants**, in terms of partitions. -/
theorem altPart_mul_hsymm {μ : List ℕ} (hμ : IsPart μ) (r : ℕ) :
    altPart m R μ * hsymm (Fin m) R r
      = ∑ η ∈ partFinset (μ.sum + r), if HorizStrip η μ then altPart m R η else 0 := by
  classical
  by_cases hμlen : μ.length ≤ m
  swap
  · rw [altPart_of_lt (by omega), zero_mul]
    refine (Finset.sum_eq_zero fun η _ => ?_).symm
    split_ifs with hstrip
    · exact altPart_of_lt (lt_of_lt_of_le (by omega) hstrip.included.length_le)
    · rfl
  rw [altPart_of_le hμlen, mul_comm, hsymm_mul_alt_strip (partVec_antitone hμ) r,
    ← Finset.sum_filter]
  -- discard the shapes with more than `m` rows
  have hsub : ∑ η ∈ ((partFinset (μ.sum + r)).filter fun η => HorizStrip η μ).filter
        (fun η => η.length ≤ m), altPart m R η
      = ∑ η ∈ (partFinset (μ.sum + r)).filter fun η => HorizStrip η μ,
          altPart m R η := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun η hη hnot => ?_
    exact altPart_of_lt (by
      by_contra hle
      exact hnot (Finset.mem_filter.2 ⟨hη, by omega⟩))
  rw [← hsub]
  refine Finset.sum_nbij' (fun d => vecPart m (partVec m μ + ⇑d)) (stripFinsupp m μ)
    ?_ ?_ ?_ ?_ ?_
  · -- the image of a strip vector is a shape
    intro d hd
    obtain ⟨hmem, hstrip⟩ := Finset.mem_filter.1 hd
    have hdsum : ∑ i, d i = r := (Finset.mem_finsuppAntidiag.1 hmem).1
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨mem_partFinset.2 ⟨isPart_vecPart hstrip, ?_⟩,
      horizStrip_of_isAltStrip hμ hμlen hstrip⟩, length_vecPart_le _⟩
    exact sum_vecPart hμlen hdsum
  · -- the strip vector of a shape is a strip vector
    intro η hη
    obtain ⟨hη', hlen⟩ := Finset.mem_filter.1 hη
    obtain ⟨hη'', hstrip⟩ := Finset.mem_filter.1 hη'
    obtain ⟨hpart, hsum⟩ := mem_partFinset.1 hη''
    have hadd : partVec m μ + ⇑(stripFinsupp m μ η) = partVec m η :=
      add_stripFinsupp hstrip.included
    refine Finset.mem_filter.2 ⟨Finset.mem_finsuppAntidiag.2 ⟨?_, by simp⟩, ?_⟩
    · change ∑ k, (stripFinsupp m μ η) k = r
      rw [sum_stripFinsupp hstrip.included hμlen hlen, hsum]
      omega
    · rw [hadd]
      exact isAltStrip_partVec_of_horizStrip hstrip
  · -- left inverse
    intro d hd
    obtain ⟨-, hstrip⟩ := Finset.mem_filter.1 hd
    have hge : ∀ i : Fin m, m - 1 - (i : ℕ) ≤ (partVec m μ + ⇑d) i := fun i =>
      le_trans (le_partVec μ i) (hstrip.1 i)
    have hpv : partVec m (vecPart m (partVec m μ + ⇑d)) = partVec m μ + ⇑d :=
      partVec_vecPart hge
    refine Finsupp.ext fun k => ?_
    have := congrFun hpv k
    simp only [coe_stripFinsupp, Pi.add_apply] at this ⊢
    omega
  · -- right inverse
    intro η hη
    obtain ⟨hη', hlen⟩ := Finset.mem_filter.1 hη
    obtain ⟨hη'', hstrip⟩ := Finset.mem_filter.1 hη'
    obtain ⟨hpart, -⟩ := mem_partFinset.1 hη''
    rw [add_stripFinsupp hstrip.included, vecPart_partVec hpart hlen]
  · -- the summands agree
    intro d hd
    obtain ⟨-, hstrip⟩ := Finset.mem_filter.1 hd
    have hge : ∀ i : Fin m, m - 1 - (i : ℕ) ≤ (partVec m μ + ⇑d) i := fun i =>
      le_trans (le_partVec μ i) (hstrip.1 i)
    rw [altPart_of_le (length_vecPart_le _), partVec_vecPart hge]

/-! ### The bialternant formula -/

/-- The expansion of the products `h_η * a_delta` along the shifted alternants. -/
theorem hProd_mul_altPart_nil (η : List ℕ) :
    hProd m R η * altPart m R []
      = ∑ μ ∈ partFinset η.sum,
          (kostkaNum η.length μ (contentOf η) : R) • altPart m R μ :=
  hProd_mul_eq_sum_kostkaNum m (altPart m R) (fun _ hμ r => altPart_mul_hsymm hμ r) η

/-- **The bialternant formula**, in the form `a_{η+delta} = s_η * a_delta`, for all
partitions at once. -/
theorem altPart_eq_schurPoly_mul {η : List ℕ} (hη : IsPart η) :
    altPart m R η = schurPoly (Fin m) R η * altPart m R [] := by
  classical
  suffices H : ∀ k n : ℕ, ∀ ν : List ℕ, IsPart ν → ν.sum = n →
      (n + 1) * n - domWeight n ν ≤ k →
      altPart m R ν = schurPoly (Fin m) R ν * altPart m R [] by
    exact H _ η.sum η hη rfl le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n ν hν hνsum hk
    have hE1 : hProd m R ν * altPart m R []
        = ∑ μ ∈ partFinset n, (kostka μ ν : R) • altPart m R μ := by
      rw [hProd_mul_altPart_nil ν, hνsum]
      exact Finset.sum_congr rfl fun μ _ => by rw [kostkaNum_eq_kostka hν μ]
    have hE2 : hProd m R ν
        = ∑ μ ∈ partFinset n, (kostka μ ν : R) • schurPoly (Fin m) R μ := by
      rw [hProd_eq_sum_kostka m hν, hνsum]
    have hkey : ∑ μ ∈ partFinset n, (kostka μ ν : R) • altPart m R μ
        = ∑ μ ∈ partFinset n,
            (kostka μ ν : R) • (schurPoly (Fin m) R μ * altPart m R []) := by
      rw [← hE1, hE2, Finset.sum_mul]
      exact Finset.sum_congr rfl fun μ _ => by rw [smul_mul_assoc]
    have hmem : ν ∈ partFinset n := mem_partFinset.2 ⟨hν, hνsum⟩
    have hrest : ∀ μ ∈ (partFinset n).erase ν,
        (kostka μ ν : R) • altPart m R μ
          = (kostka μ ν : R) • (schurPoly (Fin m) R μ * altPart m R []) := by
      intro μ hμ
      have hμne : μ ≠ ν := Finset.ne_of_mem_erase hμ
      obtain ⟨hμpart, hμsum⟩ := mem_partFinset.1 (Finset.mem_of_mem_erase hμ)
      by_cases hk0 : kostka μ ν = 0
      · rw [hk0, Nat.cast_zero, zero_smul, zero_smul]
      · have hdom : Partdom ν μ := partdom_of_kostka_ne_zero hk0
        have hlt : domWeight n ν < domWeight n μ := by
          rcases lt_or_eq_of_le (domWeight_le_domWeight (n := n) hdom) with h | h
          · exact h
          · exact absurd (eq_of_partdom_of_domWeight_eq hν hμpart hνsum hμsum hdom
              (le_of_eq h.symm)).symm hμne
        have hbd : domWeight n μ ≤ (n + 1) * n := by
          rw [domWeight]
          calc ∑ j ∈ Finset.range (n + 1), (μ.take j).sum
              ≤ ∑ _j ∈ Finset.range (n + 1), n :=
                Finset.sum_le_sum fun j _ => hμsum ▸ sum_take_le_sum μ j
            _ = (n + 1) * n := by simp [mul_comm]
        rw [ih ((n + 1) * n - domWeight n μ) (by omega) n μ hμpart hμsum le_rfl]
    have hsplit1 := Finset.add_sum_erase (partFinset n)
      (fun μ => (kostka μ ν : R) • altPart m R μ) hmem
    have hsplit2 := Finset.add_sum_erase (partFinset n)
      (fun μ => (kostka μ ν : R) • (schurPoly (Fin m) R μ * altPart m R [])) hmem
    rw [← hsplit1, ← hsplit2, Finset.sum_congr rfl hrest] at hkey
    simp only [kostka_self hν, Nat.cast_one, one_smul] at hkey
    exact add_right_cancel hkey

/-- **Jacobi's bialternant formula**: the alternant of the exponent vector `η + delta`
is the product of the Schur polynomial of shape `η` by the Vandermonde alternant of the
staircase `delta`. -/
theorem alt_partVec_eq_schurPoly_mul {η : List ℕ} (hη : IsPart η)
    (hlen : η.length ≤ m) :
    alt m R (partVec m η) = schurPoly (Fin m) R η * alt m R (partVec m []) := by
  rw [← altPart_of_le hlen, ← altPart_of_le (m := m) (R := R) (η := ([] : List ℕ)) (by simp)]
  exact altPart_eq_schurPoly_mul hη

end MvPolynomial
