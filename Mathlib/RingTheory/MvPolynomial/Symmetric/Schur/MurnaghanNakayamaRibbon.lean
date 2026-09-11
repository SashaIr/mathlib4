/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.List.Ribbon.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.MurnaghanNakayama

/-!
# The shapes of the Murnaghan-Nakayama rule are ribbons

The Murnaghan-Nakayama rule of
`Mathlib/RingTheory/MvPolynomial/Symmetric/Schur/MurnaghanNakayama.lean` is stated in the
language of the bialternant formula: the shape `mnShape μ r k` is obtained by adding `r` to the
entry of row `k` of the staircase shift of `μ` and sorting the result.  Here we check that this is
the same thing as adding a *ribbon* (a border strip) of `r` boxes to `μ`, in the combinatorial
sense of `Mathlib/Combinatorics/Enumerative/Partition/List/Ribbon/Defs.lean` (Coq `ribbon_on`),
and that the sign
`(-1)^(mnHeight μ r k)` of the rule is `(-1)` to the number of rows of the ribbon minus one.

## Main results

* `MvPolynomial.ribbonOn_mnShape` : the skew shape `mnShape μ r k / μ` is a ribbon occupying
  the rows `mnPos μ r k, …, k`.
* `MvPolynomial.ribbonHeight_mnShape` : its height is `mnHeight μ r k + 1`.
* `MvPolynomial.psum_mul_schurPoly_ribbonHeight` : the Murnaghan-Nakayama rule with the sign
  written in terms of the number of rows of the ribbon.
* `MvPolynomial.mnShape_of_ribbonOn` : conversely, every ribbon of `r` boxes added to `μ` is
  obtained from the rule, in the row where the ribbon stops.
* `MvPolynomial.psum_mul_schurPoly_sum_ribbon` : the Murnaghan-Nakayama rule as a sum over the
  shapes `ν` such that `ν / μ` is a ribbon.
-/

@[expose] public section

open Young

open List

namespace MvPolynomial

open MvPolynomial

variable {m : ℕ} {R : Type*} [CommRing R] {μ : List ℕ} {r k : ℕ}

/-- **The shapes of the Murnaghan-Nakayama rule are ribbons**: the skew shape
`mnShape μ r k / μ` is a ribbon occupying the rows `mnPos μ r k, …, k`. -/
theorem ribbonOn_mnShape (hμ : IsPart μ) (hr : 0 < r) (hadd : MNAddable μ r k) :
    RibbonOn (mnPos μ r k) k μ (mnShape μ r k) := by
  have hjk : mnPos μ r k ≤ k := mnPos_le (r := r) hμ k
  refine ⟨fun i hi => ?_, fun i h1 h2 => ?_, ?_, fun i hi => ?_⟩
  · rw [getD_mnShape hμ, mnFn_of_gt hμ hi]
  · rw [getD_mnShape hμ, mnFn_of_mid (by omega) (by omega)]
    simp
  · rw [getD_mnShape hμ, mnFn_mnPos]
    rcases Nat.eq_or_lt_of_le hjk with hjk' | hjk'
    · rw [hjk']
      omega
    · have hnot : ¬ (μ.getD k 0 + r + mnPos μ r k < μ.getD (mnPos μ r k) 0 + k) :=
        fun hcon => absurd ((lt_mnPos_iff (r := r) hμ hjk).2 hcon) (lt_irrefl _)
      have hne := hadd (mnPos μ r k) hjk'
      omega
  · rw [getD_mnShape hμ, mnFn_of_lt hi]

/-- The number of rows of the ribbon added by the Murnaghan-Nakayama rule is
`mnHeight μ r k + 1`. -/
theorem ribbonHeight_mnShape (hμ : IsPart μ) (hr : 0 < r) (hadd : MNAddable μ r k) :
    ribbonHeight μ (mnShape μ r k) = mnHeight μ r k + 1 :=
  RibbonOn.ribbonHeight_eq hμ (ribbonOn_mnShape hμ hr hadd)

/-! ### Every ribbon comes from the rule -/

/-- **The converse**: if the skew shape `ν / μ` is a ribbon of `r` boxes occupying the
rows `s, …, k`, then the ribbon can be added in row `k` in the sense of the
Murnaghan-Nakayama rule, it starts in row `s`, and the resulting shape is `ν`. -/
theorem mnShape_of_ribbonOn (hμ : IsPart μ) {ν : List ℕ} (hν : IsPart ν) {s k : ℕ}
    (hrib : RibbonOn s k μ ν) (hr : 0 < r) (hsum : ν.sum = μ.sum + r) :
    mnPos μ r k = s ∧ MNAddable μ r k ∧ mnShape μ r k = ν := by
  have hsk : s ≤ k := hrib.start_le_stop
  have hkey : ν.getD s 0 + (k - s) = μ.getD k 0 + r := by
    have := hrib.sum_add
    omega
  have hA : ∀ i, i < s → μ.getD k 0 + r + i < μ.getD i 0 + k := by
    intro i hi
    have h1 : ν.getD i 0 = μ.getD i 0 := hrib.getD_eq_of_lt hi
    have h2 : ν.getD s 0 ≤ ν.getD i 0 := hν.getD_antitone (le_of_lt hi)
    omega
  have hB : ∀ i, s ≤ i → i ≤ k → μ.getD i 0 + k < μ.getD k 0 + r + i := by
    intro i h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · have := hrib.getD_start_lt
      omega
    · have hstep : ν.getD i 0 = μ.getD (i - 1) 0 + 1 := by
        have := hrib.getD_succ (i := i - 1) (by omega) (by omega)
        rwa [show i - 1 + 1 = i by omega] at this
      have hanti : μ.getD i 0 ≤ μ.getD (i - 1) 0 := hμ.getD_antitone (by omega)
      have hνanti : ν.getD i 0 ≤ ν.getD s 0 := hν.getD_antitone (le_of_lt hlt)
      omega
  have hpos : mnPos μ r k = s := by
    have hle : mnPos μ r k ≤ s := by
      by_contra hcon
      exact absurd ((lt_mnPos_iff (r := r) hμ hsk).1 (by omega)) (by
        have := hB s (le_refl s) hsk
        omega)
    have hge : s ≤ mnPos μ r k := by
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · exact Nat.zero_le _
      · have := (lt_mnPos_iff (r := r) hμ (show s - 1 ≤ k by omega)).2
          (hA (s - 1) (by omega))
        omega
    omega
  have hadd : MNAddable μ r k := by
    intro i hi
    rcases Nat.lt_or_ge i s with h | h
    · have := hA i h
      omega
    · have := hB i h (le_of_lt hi)
      omega
  refine ⟨hpos, hadd, IsPart.ext_getD (isPart_mnShape hμ hr hadd) hν fun i => ?_⟩
  rw [getD_mnShape hμ]
  rcases Nat.lt_or_ge i s with hi | hi
  · rw [mnFn_of_lt (by omega), (hrib.getD_eq_of_lt hi).symm]
  rcases Nat.eq_or_lt_of_le hi with rfl | hi'
  · rw [mnFn, ite_eq_right (by omega), ite_eq_left hpos.symm, hpos]
    omega
  rcases Nat.lt_or_ge k i with hik | hik
  · rw [mnFn_of_gt hμ hik, (hrib.getD_eq_of_gt hik).symm]
  · rw [mnFn_of_mid (by omega) hik]
    have := hrib.getD_succ (i := i - 1) (by omega) (by omega)
    rw [show i - 1 + 1 = i by omega] at this
    omega

/-- **The Murnaghan-Nakayama rule**, with the sign expressed by the number of rows of the
ribbon: the sign attached to a ribbon is `(-1)` to its number of rows minus one. -/
theorem psum_mul_schurPoly_ribbonHeight (hμ : IsPart μ) (hlen : μ.length ≤ m)
    (hr : 0 < r) :
    psum (Fin m) R r * schurPoly (Fin m) R μ
      = ∑ k : Fin m, if MNAddable μ r (k : ℕ) then
          ((-1 : ℤ) ^ (ribbonHeight μ (mnShape μ r (k : ℕ)) - 1))
            • schurPoly (Fin m) R (mnShape μ r (k : ℕ))
        else 0 := by
  rw [psum_mul_schurPoly hμ hlen hr]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hadd : MNAddable μ r (k : ℕ)
  · rw [ite_eq_left hadd, ite_eq_left hadd, ribbonHeight_mnShape hμ hr hadd, Nat.add_sub_cancel]
  · rw [ite_eq_right hadd, ite_eq_right hadd]

/-- A row where a ribbon grows is a row of the outer shape. -/
lemma lt_length_of_ribbonOn {ν : List ℕ} {s k : ℕ} (hμ : IsPart μ)
    (hrib : RibbonOn s k μ ν) : k < ν.length := by
  have hgt : μ.getD k 0 < ν.getD k 0 :=
    RibbonOn.getD_lt hμ hrib hrib.start_le_stop (le_refl k)
  by_contra hcon
  rw [List.getD_eq_default ν 0 (by omega)] at hgt
  omega

open scoped Classical in
/-- **The Murnaghan-Nakayama rule as a sum over shapes**: the product of a Schur polynomial
`s_μ` by the power sum `p_r` is the sum, over the partitions `ν` of `|μ| + r` such
that the skew shape `ν / μ` is a ribbon, of `(-1)` to the number of rows of the ribbon
minus one, times `s_ν`. -/
theorem psum_mul_schurPoly_sum_ribbon (hμ : IsPart μ) (hlen : μ.length ≤ m)
    (hr : 0 < r) :
    psum (Fin m) R r * schurPoly (Fin m) R μ
      = ∑ ν : PartIdx (μ.sum + r) m,
          if ∃ s k, RibbonOn s k μ ν.1 then
            ((-1 : ℤ) ^ (ribbonHeight μ ν.1 - 1)) • schurPoly (Fin m) R ν.1
          else 0 := by
  classical
  rw [psum_mul_schurPoly_ribbonHeight hμ hlen hr, ← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij
    (fun (k : Fin m) (hk : k ∈ Finset.univ.filter fun k : Fin m => MNAddable μ r (k : ℕ)) =>
      (⟨mnShape μ r (k : ℕ), isPart_mnShape hμ hr (Finset.mem_filter.1 hk).2,
        sum_mnShape hμ hr,
        (length_mnShape_le _ _ _).trans (max_le k.isLt hlen)⟩ : PartIdx (μ.sum + r) m))
    (fun k hk => ?_) (fun k1 hk1 k2 hk2 heq => ?_) (fun ν hν => ?_) (fun k hk => rfl)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      mnPos μ r (k : ℕ), (k : ℕ),
      ribbonOn_mnShape hμ hr (Finset.mem_filter.1 hk).2⟩
  · have h1 := ribbonOn_mnShape hμ hr (Finset.mem_filter.1 hk1).2
    have h2 := ribbonOn_mnShape hμ hr (Finset.mem_filter.1 hk2).2
    have hs : mnShape μ r (k1 : ℕ) = mnShape μ r (k2 : ℕ) := congrArg Subtype.val heq
    rw [hs] at h1
    exact Fin.ext (RibbonOn.unique hμ h1 h2).2
  · obtain ⟨s, k, hrib⟩ := (Finset.mem_filter.1 hν).2
    obtain ⟨-, hadd, hshape⟩ := mnShape_of_ribbonOn hμ ν.2.1 hrib hr ν.2.2.1
    have hk : k < m := lt_of_lt_of_le (lt_length_of_ribbonOn hμ hrib) ν.2.2.2
    exact ⟨⟨k, hk⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hadd⟩, Subtype.ext hshape⟩

end MvPolynomial
