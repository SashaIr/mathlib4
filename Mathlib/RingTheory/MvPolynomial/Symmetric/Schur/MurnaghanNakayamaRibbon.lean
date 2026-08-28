/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Shape.Ribbon
import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.MurnaghanNakayama

/-!
# The shapes of the Murnaghan-Nakayama rule are ribbons

The Murnaghan-Nakayama rule of
`Mathlib/RingTheory/MvPolynomial/Symmetric/Schur/MurnaghanNakayama.lean` is stated in the
language of the bialternant formula: the shape `mnShape lam r k` is obtained by adding `r` to the
entry of row `k` of the staircase shift of `lam` and sorting the result.  Here we check that this is
the same thing as adding a *ribbon* (a border strip) of `r` boxes to `lam`, in the combinatorial
sense of `Mathlib/Combinatorics/Young/Shape/Ribbon.lean` (Coq `ribbon_on`), and that the sign
`(-1)^(mnHeight lam r k)` of the rule is `(-1)` to the number of rows of the ribbon minus one.

## Main results

* `MvPolynomial.ribbonOn_mnShape` : the skew shape `mnShape lam r k / lam` is a ribbon occupying
  the rows `mnPos lam r k, …, k`.
* `MvPolynomial.ribbonHeight_mnShape` : its height is `mnHeight lam r k + 1`.
* `MvPolynomial.psum_mul_schurPoly_ribbonHeight` : the Murnaghan-Nakayama rule with the sign
  written in terms of the number of rows of the ribbon.
* `MvPolynomial.mnShape_of_ribbonOn` : conversely, every ribbon of `r` boxes added to `lam` is
  obtained from the rule, in the row where the ribbon stops.
* `MvPolynomial.psum_mul_schurPoly_sum_ribbon` : the Murnaghan-Nakayama rule as a sum over the
  shapes `mu` such that `mu / lam` is a ribbon.
-/

open List

namespace MvPolynomial

open MvPolynomial

variable {m : ℕ} {R : Type*} [CommRing R] {lam : List ℕ} {r k : ℕ}

/-- **The shapes of the Murnaghan-Nakayama rule are ribbons**: the skew shape
`mnShape lam r k / lam` is a ribbon occupying the rows `mnPos lam r k, …, k`. -/
theorem ribbonOn_mnShape (hlam : IsPart lam) (hr : 0 < r) (hadd : MNAddable lam r k) :
    RibbonOn (mnPos lam r k) k lam (mnShape lam r k) := by
  have hjk : mnPos lam r k ≤ k := mnPos_le (r := r) hlam k
  refine ⟨fun i hi => ?_, fun i h1 h2 => ?_, ?_, fun i hi => ?_⟩
  · rw [getD_mnShape hlam, mnFn_of_gt hlam hi]
  · rw [getD_mnShape hlam, mnFn_of_mid (by omega) (by omega)]
    simp
  · rw [getD_mnShape hlam, mnFn_mnPos]
    rcases Nat.eq_or_lt_of_le hjk with hjk' | hjk'
    · rw [hjk']
      omega
    · have hnot : ¬ (lam.getD k 0 + r + mnPos lam r k < lam.getD (mnPos lam r k) 0 + k) :=
        fun hcon => absurd ((lt_mnPos_iff (r := r) hlam hjk).2 hcon) (lt_irrefl _)
      have hne := hadd (mnPos lam r k) hjk'
      omega
  · rw [getD_mnShape hlam, mnFn_of_lt hi]

/-- The number of rows of the ribbon added by the Murnaghan-Nakayama rule is
`mnHeight lam r k + 1`. -/
theorem ribbonHeight_mnShape (hlam : IsPart lam) (hr : 0 < r) (hadd : MNAddable lam r k) :
    ribbonHeight lam (mnShape lam r k) = mnHeight lam r k + 1 :=
  RibbonOn.ribbonHeight_eq hlam (ribbonOn_mnShape hlam hr hadd)

/-! ### Every ribbon comes from the rule -/

/-- **The converse**: if the skew shape `mu / lam` is a ribbon of `r` boxes occupying the
rows `s, …, k`, then the ribbon can be added in row `k` in the sense of the
Murnaghan-Nakayama rule, it starts in row `s`, and the resulting shape is `mu`. -/
theorem mnShape_of_ribbonOn (hlam : IsPart lam) {mu : List ℕ} (hmu : IsPart mu) {s k : ℕ}
    (hrib : RibbonOn s k lam mu) (hr : 0 < r) (hsum : mu.sum = lam.sum + r) :
    mnPos lam r k = s ∧ MNAddable lam r k ∧ mnShape lam r k = mu := by
  have hsk : s ≤ k := hrib.start_le_stop
  have hkey : mu.getD s 0 + (k - s) = lam.getD k 0 + r := by
    have := hrib.sum_add
    omega
  have hA : ∀ i, i < s → lam.getD k 0 + r + i < lam.getD i 0 + k := by
    intro i hi
    have h1 : mu.getD i 0 = lam.getD i 0 := hrib.getD_eq_of_lt hi
    have h2 : mu.getD s 0 ≤ mu.getD i 0 := hmu.getD_antitone (le_of_lt hi)
    omega
  have hB : ∀ i, s ≤ i → i ≤ k → lam.getD i 0 + k < lam.getD k 0 + r + i := by
    intro i h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · have := hrib.getD_start_lt
      omega
    · have hstep : mu.getD i 0 = lam.getD (i - 1) 0 + 1 := by
        have := hrib.getD_succ (i := i - 1) (by omega) (by omega)
        rwa [show i - 1 + 1 = i by omega] at this
      have hanti : lam.getD i 0 ≤ lam.getD (i - 1) 0 := hlam.getD_antitone (by omega)
      have hmuanti : mu.getD i 0 ≤ mu.getD s 0 := hmu.getD_antitone (le_of_lt hlt)
      omega
  have hpos : mnPos lam r k = s := by
    have hle : mnPos lam r k ≤ s := by
      by_contra hcon
      exact absurd ((lt_mnPos_iff (r := r) hlam hsk).1 (by omega)) (by
        have := hB s (le_refl s) hsk
        omega)
    have hge : s ≤ mnPos lam r k := by
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · exact Nat.zero_le _
      · have := (lt_mnPos_iff (r := r) hlam (show s - 1 ≤ k by omega)).2
          (hA (s - 1) (by omega))
        omega
    omega
  have hadd : MNAddable lam r k := by
    intro i hi
    rcases Nat.lt_or_ge i s with h | h
    · have := hA i h
      omega
    · have := hB i h (le_of_lt hi)
      omega
  refine ⟨hpos, hadd, IsPart.ext_getD (isPart_mnShape hlam hr hadd) hmu fun i => ?_⟩
  rw [getD_mnShape hlam]
  rcases Nat.lt_or_ge i s with hi | hi
  · rw [mnFn_of_lt (by omega), (hrib.getD_eq_of_lt hi).symm]
  rcases Nat.eq_or_lt_of_le hi with rfl | hi'
  · rw [mnFn, if_neg (by omega), if_pos hpos.symm, hpos]
    omega
  rcases Nat.lt_or_ge k i with hik | hik
  · rw [mnFn_of_gt hlam hik, (hrib.getD_eq_of_gt hik).symm]
  · rw [mnFn_of_mid (by omega) hik]
    have := hrib.getD_succ (i := i - 1) (by omega) (by omega)
    rw [show i - 1 + 1 = i by omega] at this
    omega

/-- **The Murnaghan-Nakayama rule**, with the sign expressed by the number of rows of the
ribbon: the sign attached to a ribbon is `(-1)` to its number of rows minus one. -/
theorem psum_mul_schurPoly_ribbonHeight (hlam : IsPart lam) (hlen : lam.length ≤ m)
    (hr : 0 < r) :
    psum (Fin m) R r * schurPoly (Fin m) R lam
      = ∑ k : Fin m, if MNAddable lam r (k : ℕ) then
          ((-1 : ℤ) ^ (ribbonHeight lam (mnShape lam r (k : ℕ)) - 1))
            • schurPoly (Fin m) R (mnShape lam r (k : ℕ))
        else 0 := by
  rw [psum_mul_schurPoly hlam hlen hr]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hadd : MNAddable lam r (k : ℕ)
  · rw [if_pos hadd, if_pos hadd, ribbonHeight_mnShape hlam hr hadd, Nat.add_sub_cancel]
  · rw [if_neg hadd, if_neg hadd]

/-- A row where a ribbon grows is a row of the outer shape. -/
lemma lt_length_of_ribbonOn {mu : List ℕ} {s k : ℕ} (hlam : IsPart lam)
    (hrib : RibbonOn s k lam mu) : k < mu.length := by
  have hgt : lam.getD k 0 < mu.getD k 0 :=
    RibbonOn.getD_lt hlam hrib hrib.start_le_stop (le_refl k)
  by_contra hcon
  rw [List.getD_eq_default mu 0 (by omega)] at hgt
  omega

open scoped Classical in
/-- **The Murnaghan-Nakayama rule as a sum over shapes**: the product of a Schur polynomial
`s_lam` by the power sum `p_r` is the sum, over the partitions `mu` of `|lam| + r` such
that the skew shape `mu / lam` is a ribbon, of `(-1)` to the number of rows of the ribbon
minus one, times `s_mu`. -/
theorem psum_mul_schurPoly_sum_ribbon (hlam : IsPart lam) (hlen : lam.length ≤ m)
    (hr : 0 < r) :
    psum (Fin m) R r * schurPoly (Fin m) R lam
      = ∑ mu : PartIdx (lam.sum + r) m,
          if ∃ s k, RibbonOn s k lam mu.1 then
            ((-1 : ℤ) ^ (ribbonHeight lam mu.1 - 1)) • schurPoly (Fin m) R mu.1
          else 0 := by
  classical
  rw [psum_mul_schurPoly_ribbonHeight hlam hlen hr, ← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij
    (fun (k : Fin m) (hk : k ∈ Finset.univ.filter fun k : Fin m => MNAddable lam r (k : ℕ)) =>
      (⟨mnShape lam r (k : ℕ), isPart_mnShape hlam hr (Finset.mem_filter.1 hk).2,
        sum_mnShape hlam hr,
        (length_mnShape_le _ _ _).trans (max_le k.isLt hlen)⟩ : PartIdx (lam.sum + r) m))
    (fun k hk => ?_) (fun k1 hk1 k2 hk2 heq => ?_) (fun mu hmu => ?_) (fun k hk => rfl)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      mnPos lam r (k : ℕ), (k : ℕ),
      ribbonOn_mnShape hlam hr (Finset.mem_filter.1 hk).2⟩
  · have h1 := ribbonOn_mnShape hlam hr (Finset.mem_filter.1 hk1).2
    have h2 := ribbonOn_mnShape hlam hr (Finset.mem_filter.1 hk2).2
    have hs : mnShape lam r (k1 : ℕ) = mnShape lam r (k2 : ℕ) := congrArg Subtype.val heq
    rw [hs] at h1
    exact Fin.ext (RibbonOn.unique hlam h1 h2).2
  · obtain ⟨s, k, hrib⟩ := (Finset.mem_filter.1 hmu).2
    obtain ⟨-, hadd, hshape⟩ := mnShape_of_ribbonOn hlam mu.2.1 hrib hr mu.2.2.1
    have hk : k < m := lt_of_lt_of_le (lt_length_of_ribbonOn hlam hrib) mu.2.2.2
    exact ⟨⟨k, hk⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hadd⟩, Subtype.ext hshape⟩

end MvPolynomial
