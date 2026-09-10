/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Shape.Ribbon.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.MurnaghanNakayama

/-!
# The shapes of the Murnaghan-Nakayama rule are ribbons

The Murnaghan-Nakayama rule of
`Mathlib/RingTheory/MvPolynomial/Symmetric/Schur/MurnaghanNakayama.lean` is stated in the
language of the bialternant formula: the shape `mnShape η r k` is obtained by adding `r` to the
entry of row `k` of the staircase shift of `η` and sorting the result.  Here we check that this is
the same thing as adding a *ribbon* (a border strip) of `r` boxes to `η`, in the combinatorial
sense of `Mathlib/Combinatorics/Young/Shape/Ribbon/Defs.lean` (Coq `ribbon_on`), and that the sign
`(-1)^(mnHeight η r k)` of the rule is `(-1)` to the number of rows of the ribbon minus one.

## Main results

* `MvPolynomial.ribbonOn_mnShape` : the skew shape `mnShape η r k / η` is a ribbon occupying
  the rows `mnPos η r k, …, k`.
* `MvPolynomial.ribbonHeight_mnShape` : its height is `mnHeight η r k + 1`.
* `MvPolynomial.psum_mul_schurPoly_ribbonHeight` : the Murnaghan-Nakayama rule with the sign
  written in terms of the number of rows of the ribbon.
* `MvPolynomial.mnShape_of_ribbonOn` : conversely, every ribbon of `r` boxes added to `η` is
  obtained from the rule, in the row where the ribbon stops.
* `MvPolynomial.psum_mul_schurPoly_sum_ribbon` : the Murnaghan-Nakayama rule as a sum over the
  shapes `μ` such that `μ / η` is a ribbon.
-/

@[expose] public section

open Young

open List

namespace MvPolynomial

open MvPolynomial

variable {m : ℕ} {R : Type*} [CommRing R] {η : List ℕ} {r k : ℕ}

/-- **The shapes of the Murnaghan-Nakayama rule are ribbons**: the skew shape
`mnShape η r k / η` is a ribbon occupying the rows `mnPos η r k, …, k`. -/
theorem ribbonOn_mnShape (hη : IsPart η) (hr : 0 < r) (hadd : MNAddable η r k) :
    RibbonOn (mnPos η r k) k η (mnShape η r k) := by
  have hjk : mnPos η r k ≤ k := mnPos_le (r := r) hη k
  refine ⟨fun i hi => ?_, fun i h1 h2 => ?_, ?_, fun i hi => ?_⟩
  · rw [getD_mnShape hη, mnFn_of_gt hη hi]
  · rw [getD_mnShape hη, mnFn_of_mid (by omega) (by omega)]
    simp
  · rw [getD_mnShape hη, mnFn_mnPos]
    rcases Nat.eq_or_lt_of_le hjk with hjk' | hjk'
    · rw [hjk']
      omega
    · have hnot : ¬ (η.getD k 0 + r + mnPos η r k < η.getD (mnPos η r k) 0 + k) :=
        fun hcon => absurd ((lt_mnPos_iff (r := r) hη hjk).2 hcon) (lt_irrefl _)
      have hne := hadd (mnPos η r k) hjk'
      omega
  · rw [getD_mnShape hη, mnFn_of_lt hi]

/-- The number of rows of the ribbon added by the Murnaghan-Nakayama rule is
`mnHeight η r k + 1`. -/
theorem ribbonHeight_mnShape (hη : IsPart η) (hr : 0 < r) (hadd : MNAddable η r k) :
    ribbonHeight η (mnShape η r k) = mnHeight η r k + 1 :=
  RibbonOn.ribbonHeight_eq hη (ribbonOn_mnShape hη hr hadd)

/-! ### Every ribbon comes from the rule -/

/-- **The converse**: if the skew shape `μ / η` is a ribbon of `r` boxes occupying the
rows `s, …, k`, then the ribbon can be added in row `k` in the sense of the
Murnaghan-Nakayama rule, it starts in row `s`, and the resulting shape is `μ`. -/
theorem mnShape_of_ribbonOn (hη : IsPart η) {μ : List ℕ} (hμ : IsPart μ) {s k : ℕ}
    (hrib : RibbonOn s k η μ) (hr : 0 < r) (hsum : μ.sum = η.sum + r) :
    mnPos η r k = s ∧ MNAddable η r k ∧ mnShape η r k = μ := by
  have hsk : s ≤ k := hrib.start_le_stop
  have hkey : μ.getD s 0 + (k - s) = η.getD k 0 + r := by
    have := hrib.sum_add
    omega
  have hA : ∀ i, i < s → η.getD k 0 + r + i < η.getD i 0 + k := by
    intro i hi
    have h1 : μ.getD i 0 = η.getD i 0 := hrib.getD_eq_of_lt hi
    have h2 : μ.getD s 0 ≤ μ.getD i 0 := hμ.getD_antitone (le_of_lt hi)
    omega
  have hB : ∀ i, s ≤ i → i ≤ k → η.getD i 0 + k < η.getD k 0 + r + i := by
    intro i h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · have := hrib.getD_start_lt
      omega
    · have hstep : μ.getD i 0 = η.getD (i - 1) 0 + 1 := by
        have := hrib.getD_succ (i := i - 1) (by omega) (by omega)
        rwa [show i - 1 + 1 = i by omega] at this
      have hanti : η.getD i 0 ≤ η.getD (i - 1) 0 := hη.getD_antitone (by omega)
      have hμanti : μ.getD i 0 ≤ μ.getD s 0 := hμ.getD_antitone (le_of_lt hlt)
      omega
  have hpos : mnPos η r k = s := by
    have hle : mnPos η r k ≤ s := by
      by_contra hcon
      exact absurd ((lt_mnPos_iff (r := r) hη hsk).1 (by omega)) (by
        have := hB s (le_refl s) hsk
        omega)
    have hge : s ≤ mnPos η r k := by
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · exact Nat.zero_le _
      · have := (lt_mnPos_iff (r := r) hη (show s - 1 ≤ k by omega)).2
          (hA (s - 1) (by omega))
        omega
    omega
  have hadd : MNAddable η r k := by
    intro i hi
    rcases Nat.lt_or_ge i s with h | h
    · have := hA i h
      omega
    · have := hB i h (le_of_lt hi)
      omega
  refine ⟨hpos, hadd, IsPart.ext_getD (isPart_mnShape hη hr hadd) hμ fun i => ?_⟩
  rw [getD_mnShape hη]
  rcases Nat.lt_or_ge i s with hi | hi
  · rw [mnFn_of_lt (by omega), (hrib.getD_eq_of_lt hi).symm]
  rcases Nat.eq_or_lt_of_le hi with rfl | hi'
  · rw [mnFn, ite_eq_right (by omega), ite_eq_left hpos.symm, hpos]
    omega
  rcases Nat.lt_or_ge k i with hik | hik
  · rw [mnFn_of_gt hη hik, (hrib.getD_eq_of_gt hik).symm]
  · rw [mnFn_of_mid (by omega) hik]
    have := hrib.getD_succ (i := i - 1) (by omega) (by omega)
    rw [show i - 1 + 1 = i by omega] at this
    omega

/-- **The Murnaghan-Nakayama rule**, with the sign expressed by the number of rows of the
ribbon: the sign attached to a ribbon is `(-1)` to its number of rows minus one. -/
theorem psum_mul_schurPoly_ribbonHeight (hη : IsPart η) (hlen : η.length ≤ m)
    (hr : 0 < r) :
    psum (Fin m) R r * schurPoly (Fin m) R η
      = ∑ k : Fin m, if MNAddable η r (k : ℕ) then
          ((-1 : ℤ) ^ (ribbonHeight η (mnShape η r (k : ℕ)) - 1))
            • schurPoly (Fin m) R (mnShape η r (k : ℕ))
        else 0 := by
  rw [psum_mul_schurPoly hη hlen hr]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hadd : MNAddable η r (k : ℕ)
  · rw [ite_eq_left hadd, ite_eq_left hadd, ribbonHeight_mnShape hη hr hadd, Nat.add_sub_cancel]
  · rw [ite_eq_right hadd, ite_eq_right hadd]

/-- A row where a ribbon grows is a row of the outer shape. -/
lemma lt_length_of_ribbonOn {μ : List ℕ} {s k : ℕ} (hη : IsPart η)
    (hrib : RibbonOn s k η μ) : k < μ.length := by
  have hgt : η.getD k 0 < μ.getD k 0 :=
    RibbonOn.getD_lt hη hrib hrib.start_le_stop (le_refl k)
  by_contra hcon
  rw [List.getD_eq_default μ 0 (by omega)] at hgt
  omega

open scoped Classical in
/-- **The Murnaghan-Nakayama rule as a sum over shapes**: the product of a Schur polynomial
`s_η` by the power sum `p_r` is the sum, over the partitions `μ` of `|η| + r` such
that the skew shape `μ / η` is a ribbon, of `(-1)` to the number of rows of the ribbon
minus one, times `s_μ`. -/
theorem psum_mul_schurPoly_sum_ribbon (hη : IsPart η) (hlen : η.length ≤ m)
    (hr : 0 < r) :
    psum (Fin m) R r * schurPoly (Fin m) R η
      = ∑ μ : PartIdx (η.sum + r) m,
          if ∃ s k, RibbonOn s k η μ.1 then
            ((-1 : ℤ) ^ (ribbonHeight η μ.1 - 1)) • schurPoly (Fin m) R μ.1
          else 0 := by
  classical
  rw [psum_mul_schurPoly_ribbonHeight hη hlen hr, ← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij
    (fun (k : Fin m) (hk : k ∈ Finset.univ.filter fun k : Fin m => MNAddable η r (k : ℕ)) =>
      (⟨mnShape η r (k : ℕ), isPart_mnShape hη hr (Finset.mem_filter.1 hk).2,
        sum_mnShape hη hr,
        (length_mnShape_le _ _ _).trans (max_le k.isLt hlen)⟩ : PartIdx (η.sum + r) m))
    (fun k hk => ?_) (fun k1 hk1 k2 hk2 heq => ?_) (fun μ hμ => ?_) (fun k hk => rfl)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      mnPos η r (k : ℕ), (k : ℕ),
      ribbonOn_mnShape hη hr (Finset.mem_filter.1 hk).2⟩
  · have h1 := ribbonOn_mnShape hη hr (Finset.mem_filter.1 hk1).2
    have h2 := ribbonOn_mnShape hη hr (Finset.mem_filter.1 hk2).2
    have hs : mnShape η r (k1 : ℕ) = mnShape η r (k2 : ℕ) := congrArg Subtype.val heq
    rw [hs] at h1
    exact Fin.ext (RibbonOn.unique hη h1 h2).2
  · obtain ⟨s, k, hrib⟩ := (Finset.mem_filter.1 hμ).2
    obtain ⟨-, hadd, hshape⟩ := mnShape_of_ribbonOn hη μ.2.1 hrib hr μ.2.2.1
    have hk : k < m := lt_of_lt_of_le (lt_length_of_ribbonOn hη hrib) μ.2.2.2
    exact ⟨⟨k, hk⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hadd⟩, Subtype.ext hshape⟩

end MvPolynomial
