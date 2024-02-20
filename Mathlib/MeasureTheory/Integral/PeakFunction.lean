/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

#align_import measure_theory.integral.peak_function from "leanprover-community/mathlib"@"13b0d72fd8533ba459ac66e9a885e35ffabb32b2"

/-!
# Integrals against peak functions

A sequence of peak functions is a sequence of functions with average one concentrating around
a point `x₀`. Given such a sequence `φₙ`, then `∫ φₙ g` tends to `g x₀` in many situations, with
a whole zoo of possible assumptions on `φₙ` and `g`. This file is devoted to such results. Such
functions are also called approximations of unity, or approximations of identity.

## Main results

* `tendsto_set_integral_peak_smul_of_integrableOn_of_continuousWithinAt`: If a sequence of peak
  functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
  `g` is integrable and continuous at `x₀`, then `∫ φᵢ • g` converges to `g x₀`.
* `tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`:
  If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
  then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
  concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀`
  if `g` is continuous on `s`.

Note that there are related results about convolution with respect to peak functions in the file
`Analysis.Convolution`, such as `convolution_tendsto_right` there.
-/

open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Metric

open scoped Topology ENNReal

/-- This lemma exists for finsets, but not for sets currently. porting note: move to
data.set.basic after the port. -/
theorem Set.disjoint_sdiff_inter {α : Type*} (s t : Set α) : Disjoint (s \ t) (s ∩ t) :=
  disjoint_of_subset_right (inter_subset_right _ _) disjoint_sdiff_left
#align set.disjoint_sdiff_inter Set.disjoint_sdiff_inter


/-!
### General convergent result for integrals against a sequence of peak functions
-/

open Set

variable {α E ι : Type*} {hm : MeasurableSpace α} {μ : Measure α} [TopologicalSpace α]
  [BorelSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] {g : α → E} {l : Filter ι} {x₀ : α}
  {s t : Set α} {φ : ι → α → ℝ} {a : E}

/-- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
`g` is integrable and has a limit at `x₀`, then `φᵢ • g` is eventually integrable. -/
theorem integrableOn_peak_smul_of_integrableOn_of_tendsto
    (hs : MeasurableSet s) (h'st : t ∈ 𝓝[s] x₀)
    (hlφ : ∀ u : Set α, IsOpen u → x₀ ∈ u → TendstoUniformlyOn φ 0 l (s \ u))
    (hiφ : Tendsto (fun i ↦ ∫ x in t, φ i x ∂μ) l (𝓝 1))
    (h'iφ : ∀ᶠ i in l, AEStronglyMeasurable (φ i) (μ.restrict s))
    (hmg : IntegrableOn g s μ) (hcg : Tendsto g (𝓝[s] x₀) (𝓝 a)) :
    ∀ᶠ i in l, IntegrableOn (fun x => φ i x • g x) s μ := by
  obtain ⟨u, u_open, x₀u, ut, hu⟩ :
      ∃ u, IsOpen u ∧ x₀ ∈ u ∧ s ∩ u ⊆ t ∧ ∀ x ∈ u ∩ s, g x ∈ ball a 1 := by
    rcases mem_nhdsWithin.1 (Filter.inter_mem h'st (hcg (ball_mem_nhds _ zero_lt_one)))
      with ⟨u, u_open, x₀u, hu⟩
    refine ⟨u, u_open, x₀u, ?_, hu.trans (inter_subset_right _ _)⟩
    rw [inter_comm]
    exact hu.trans (inter_subset_left _ _)
  rw [tendsto_iff_norm_sub_tendsto_zero] at hiφ
  filter_upwards [tendstoUniformlyOn_iff.1 (hlφ u u_open x₀u) 1 zero_lt_one,
    (tendsto_order.1 hiφ).2 1 zero_lt_one, h'iφ] with i hi h'i h''i
  have I : IntegrableOn (φ i) t μ := .of_integral_ne_zero (fun h ↦ by simp [h] at h'i)
  have A : IntegrableOn (fun x => φ i x • g x) (s \ u) μ := by
    refine' Integrable.smul_of_top_right (hmg.mono (diff_subset _ _) le_rfl) _
    apply memℒp_top_of_bound (h''i.mono_set (diff_subset _ _)) 1
    filter_upwards [self_mem_ae_restrict (hs.diff u_open.measurableSet)] with x hx
    simpa only [Pi.zero_apply, dist_zero_left] using (hi x hx).le
  have B : IntegrableOn (fun x => φ i x • g x) (s ∩ u) μ := by
    apply Integrable.smul_of_top_left
    · exact IntegrableOn.mono_set I ut
    · apply
        memℒp_top_of_bound (hmg.mono_set (inter_subset_left _ _)).aestronglyMeasurable (‖a‖ + 1)
      filter_upwards [self_mem_ae_restrict (hs.inter u_open.measurableSet)] with x hx
      rw [inter_comm] at hx
      exact (norm_lt_of_mem_ball (hu x hx)).le
  convert A.union B
  simp only [diff_union_inter]
#align integrable_on_peak_smul_of_integrable_on_of_continuous_within_at integrableOn_peak_smul_of_integrableOn_of_tendsto
@[deprecated] alias integrableOn_peak_smul_of_integrableOn_of_continuousWithinAt :=
  integrableOn_peak_smul_of_integrableOn_of_tendsto -- deprecated on 2024-02-20

variable [CompleteSpace E]

/-- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀` and its
integral on some finite-measure neighborhood of `x₀` converges to `1`, and `g` is integrable and
has a limit `a` at `x₀`, then `∫ φᵢ • g` converges to `a`.
Auxiliary lemma where one assumes additionally `a = 0`. -/
theorem tendsto_set_integral_peak_smul_of_integrableOn_of_tendsto_aux
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : t ⊆ s) (h'ts : t ∈ 𝓝[s] x₀)
    (hnφ : ∀ᶠ i in l, ∀ x ∈ s, 0 ≤ φ i x)
    (hlφ : ∀ u : Set α, IsOpen u → x₀ ∈ u → TendstoUniformlyOn φ 0 l (s \ u))
    (hiφ : Tendsto (fun i ↦ ∫ x in t, φ i x ∂μ) l (𝓝 1))
    (h'iφ : ∀ᶠ i in l, AEStronglyMeasurable (φ i) (μ.restrict s))
    (hmg : IntegrableOn g s μ) (hcg : Tendsto g (𝓝[s] x₀) (𝓝 0)) :
    Tendsto (fun i : ι => ∫ x in s, φ i x • g x ∂μ) l (𝓝 0) := by
  refine' Metric.tendsto_nhds.2 fun ε εpos => _
  obtain ⟨δ, hδ, δpos, δone⟩ : ∃ δ, (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ < ε ∧ 0 < δ ∧ δ < 1:= by
    have A :
      Tendsto (fun δ => (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ) (𝓝[>] 0)
        (𝓝 ((0 * ∫ x in s, ‖g x‖ ∂μ) + 2 * 0)) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact (tendsto_id.mul tendsto_const_nhds).add (tendsto_id.const_mul _)
    rw [zero_mul, zero_add, mul_zero] at A
    have : Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0 := Ioo_mem_nhdsWithin_Ioi ⟨le_rfl, zero_lt_one⟩
    rcases (((tendsto_order.1 A).2 ε εpos).and this).exists with ⟨δ, hδ, h'δ⟩
    exact ⟨δ, hδ, h'δ.1, h'δ.2⟩
  suffices ∀ᶠ i in l, ‖∫ x in s, φ i x • g x ∂μ‖ ≤ (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ by
    filter_upwards [this] with i hi
    simp only [dist_zero_right]
    exact hi.trans_lt hδ
  obtain ⟨u, u_open, x₀u, ut, hu⟩ :
      ∃ u, IsOpen u ∧ x₀ ∈ u ∧ s ∩ u ⊆ t ∧ ∀ x ∈ u ∩ s, g x ∈ ball 0 δ := by
    rcases mem_nhdsWithin.1 (Filter.inter_mem h'ts (hcg (ball_mem_nhds _ δpos)))
      with ⟨u, u_open, x₀u, hu⟩
    refine ⟨u, u_open, x₀u, ?_, hu.trans (inter_subset_right _ _)⟩
    rw [inter_comm]
    exact hu.trans (inter_subset_left _ _)
  filter_upwards [tendstoUniformlyOn_iff.1 (hlφ u u_open x₀u) δ δpos,
    (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 hiφ)).2 δ δpos, hnφ,
    integrableOn_peak_smul_of_integrableOn_of_tendsto hs h'ts hlφ hiφ h'iφ hmg hcg]
    with i hi h'i hφpos h''i
  have I : IntegrableOn (φ i) t μ := by
    apply Integrable.of_integral_ne_zero (fun h ↦ ?_)
    simp [h] at h'i
    linarith
  have B : ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ ≤ 2 * δ :=
    calc
      ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ ≤ ∫ x in s ∩ u, ‖φ i x • g x‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x in s ∩ u, ‖φ i x‖ * δ ∂μ := by
        refine' set_integral_mono_on _ _ (hs.inter u_open.measurableSet) fun x hx => _
        · exact IntegrableOn.mono_set h''i.norm (inter_subset_left _ _)
        · exact IntegrableOn.mono_set (I.norm.mul_const _) ut
        rw [norm_smul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [inter_comm] at hu
        exact (mem_ball_zero_iff.1 (hu x hx)).le
      _ ≤ ∫ x in t, ‖φ i x‖ * δ ∂μ := by
        apply set_integral_mono_set
        · exact I.norm.mul_const _
        · exact eventually_of_forall fun x => mul_nonneg (norm_nonneg _) δpos.le
        · apply eventually_of_forall ut
      _ = ∫ x in t, φ i x * δ ∂μ := by
        apply set_integral_congr ht fun x hx => ?_
        rw [Real.norm_of_nonneg (hφpos _ (hts hx))]
      _ = (∫ x in t, φ i x ∂μ) * δ := by rw [integral_mul_right]
      _ ≤ 2 * δ := by gcongr; linarith [(le_abs_self _).trans h'i.le]
  have C : ‖∫ x in s \ u, φ i x • g x ∂μ‖ ≤ δ * ∫ x in s, ‖g x‖ ∂μ :=
    calc
      ‖∫ x in s \ u, φ i x • g x ∂μ‖ ≤ ∫ x in s \ u, ‖φ i x • g x‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x in s \ u, δ * ‖g x‖ ∂μ := by
        refine' set_integral_mono_on _ _ (hs.diff u_open.measurableSet) fun x hx => _
        · exact IntegrableOn.mono_set h''i.norm (diff_subset _ _)
        · exact IntegrableOn.mono_set (hmg.norm.const_mul _) (diff_subset _ _)
        rw [norm_smul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [Pi.zero_apply, dist_zero_left] using (hi x hx).le
      _ ≤ δ * ∫ x in s, ‖g x‖ ∂μ := by
        rw [integral_mul_left]
        apply mul_le_mul_of_nonneg_left (set_integral_mono_set hmg.norm _ _) δpos.le
        · exact eventually_of_forall fun x => norm_nonneg _
        · apply eventually_of_forall; exact diff_subset s u
  calc
    ‖∫ x in s, φ i x • g x ∂μ‖ =
      ‖(∫ x in s \ u, φ i x • g x ∂μ) + ∫ x in s ∩ u, φ i x • g x ∂μ‖ := by
      conv_lhs => rw [← diff_union_inter s u]
      rw [integral_union (disjoint_sdiff_inter _ _) (hs.inter u_open.measurableSet)
          (h''i.mono_set (diff_subset _ _)) (h''i.mono_set (inter_subset_left _ _))]
    _ ≤ ‖∫ x in s \ u, φ i x • g x ∂μ‖ + ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ := (norm_add_le _ _)
    _ ≤ (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ := add_le_add C B
#align tendsto_set_integral_peak_smul_of_integrable_on_of_continuous_within_at_aux tendsto_set_integral_peak_smul_of_integrableOn_of_tendsto_aux
@[deprecated] alias tendsto_set_integral_peak_smul_of_integrableOn_of_continuousWithinAt_aux :=
  tendsto_set_integral_peak_smul_of_integrableOn_of_tendsto_aux -- deprecated on 2024-02-20

/-- If a sequence of peak functions `φᵢ` converges uniformly to zero away from a point `x₀` and its
integral on some finite-measure neighborhood of `x₀` converges to `1`, and `g` is integrable and
has a limit `a` at `x₀`, then `∫ φᵢ • g` converges to `a`. -/
theorem tendsto_set_integral_peak_smul_of_integrableOn_of_tendsto
    (hs : MeasurableSet s) {t : Set α} (ht : MeasurableSet t) (hts : t ⊆ s) (h'ts : t ∈ 𝓝[s] x₀)
    (h't : μ t ≠ ∞) (hnφ : ∀ᶠ i in l, ∀ x ∈ s, 0 ≤ φ i x)
    (hlφ : ∀ u : Set α, IsOpen u → x₀ ∈ u → TendstoUniformlyOn φ 0 l (s \ u))
    (hiφ : Tendsto (fun i ↦ ∫ x in t, φ i x ∂μ) l (𝓝 1))
    (h'iφ : ∀ᶠ i in l, AEStronglyMeasurable (φ i) (μ.restrict s))
    (hmg : IntegrableOn g s μ) (hcg : Tendsto g (𝓝[s] x₀) (𝓝 a)) :
    Tendsto (fun i : ι ↦ ∫ x in s, φ i x • g x ∂μ) l (𝓝 a) := by
  let h := g - t.indicator (fun _ ↦ a)
  have A : Tendsto (fun i : ι => (∫ x in s, φ i x • h x ∂μ) + (∫ x in t, φ i x ∂μ) • a) l
      (𝓝 (0 + (1 : ℝ) • a)) := by
    refine' Tendsto.add _ (Tendsto.smul hiφ tendsto_const_nhds)
    apply tendsto_set_integral_peak_smul_of_integrableOn_of_tendsto_aux hs ht hts h'ts
        hnφ hlφ hiφ h'iφ
    · apply hmg.sub
      simp only [integrable_indicator_iff ht, integrableOn_const, ht, Measure.restrict_apply]
      right
      exact lt_of_le_of_lt (measure_mono (inter_subset_left _ _)) (h't.lt_top)
    · rw [← sub_self a]
      apply Tendsto.sub hcg
      apply tendsto_const_nhds.congr'
      filter_upwards [h'ts] with x hx using by simp [hx]
  simp only [one_smul, zero_add] at A
  refine' Tendsto.congr' _ A
  filter_upwards [integrableOn_peak_smul_of_integrableOn_of_tendsto hs h'ts
    hlφ hiφ h'iφ hmg hcg,
    (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 hiφ)).2 1 zero_lt_one] with i hi h'i
  simp only [Pi.sub_apply, smul_sub, ← indicator_smul_apply]
  rw [integral_sub hi, set_integral_indicator ht, inter_eq_right.mpr hts,
    integral_smul_const, sub_add_cancel]
  rw [integrable_indicator_iff ht]
  apply Integrable.smul_const
  rw [restrict_restrict ht, inter_eq_left.mpr hts]
  exact .of_integral_ne_zero (fun h ↦ by simp [h] at h'i)
#align tendsto_set_integral_peak_smul_of_integrable_on_of_continuous_within_at tendsto_set_integral_peak_smul_of_integrableOn_of_tendsto
@[deprecated] alias tendsto_set_integral_peak_smul_of_integrableOn_of_continuousWithinAt :=
  tendsto_set_integral_peak_smul_of_integrableOn_of_tendsto -- deprecated on 2024-02-20

/-!
### Peak functions of the form `x ↦ (c x) ^ n / ∫ (c y) ^ n`
-/

/-- If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀` if `g` is
integrable on `s` and continuous at `x₀`.

Version assuming that `μ` gives positive mass to all neighborhoods of `x₀` within `s`.
For a less precise but more usable version, see
`tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`.
 -/
theorem tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos
    [MetrizableSpace α] [IsLocallyFiniteMeasure μ] (hs : IsCompact s)
    (hμ : ∀ u, IsOpen u → x₀ ∈ u → 0 < μ (u ∩ s)) {c : α → ℝ} (hc : ContinuousOn c s)
    (h'c : ∀ y ∈ s, y ≠ x₀ → c y < c x₀) (hnc : ∀ x ∈ s, 0 ≤ c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ ∈ s)
    (hmg : IntegrableOn g s μ) (hcg : ContinuousWithinAt g s x₀) :
    Tendsto (fun n : ℕ => (∫ x in s, c x ^ n ∂μ)⁻¹ • ∫ x in s, c x ^ n • g x ∂μ)
      atTop (𝓝 (g x₀)) := by
  /- We apply the general result
    `tendsto_set_integral_peak_smul_of_integrableOn_of_continuousWithinAt` to the sequence of
    peak functions `φₙ = (c x) ^ n / ∫ (c x) ^ n`. The only nontrivial bit is to check that this
    sequence converges uniformly to zero on any set `s \ u` away from `x₀`. By compactness, the
    function `c` is bounded by `t < c x₀` there. Consider `t' ∈ (t, c x₀)`, and a neighborhood `v`
    of `x₀` where `c x ≥ t'`, by continuity. Then `∫ (c x) ^ n` is bounded below by `t' ^ n μ v`.
    It follows that, on `s \ u`, then `φₙ x ≤ t ^ n / (t' ^ n μ v)`,
    which tends (exponentially fast) to zero with `n`. -/
  let φ : ℕ → α → ℝ := fun n x => (∫ x in s, c x ^ n ∂μ)⁻¹ * c x ^ n
  have hnφ : ∀ n, ∀ x ∈ s, 0 ≤ φ n x := by
    intro n x hx
    apply mul_nonneg (inv_nonneg.2 _) (pow_nonneg (hnc x hx) _)
    exact set_integral_nonneg hs.measurableSet fun x hx => pow_nonneg (hnc x hx) _
  have I : ∀ n, IntegrableOn (fun x => c x ^ n) s μ := fun n =>
    ContinuousOn.integrableOn_compact hs (hc.pow n)
  have J : ∀ n, 0 ≤ᵐ[μ.restrict s] fun x : α => c x ^ n := by
    intro n
    filter_upwards [ae_restrict_mem hs.measurableSet] with x hx
    exact pow_nonneg (hnc x hx) n
  have P : ∀ n, (0 : ℝ) < ∫ x in s, c x ^ n ∂μ := by
    intro n
    refine' (set_integral_pos_iff_support_of_nonneg_ae (J n) (I n)).2 _
    obtain ⟨u, u_open, x₀_u, hu⟩ : ∃ u : Set α, IsOpen u ∧ x₀ ∈ u ∧ u ∩ s ⊆ c ⁻¹' Ioi 0 :=
      _root_.continuousOn_iff.1 hc x₀ h₀ (Ioi (0 : ℝ)) isOpen_Ioi hnc₀
    apply (hμ u u_open x₀_u).trans_le
    exact measure_mono fun x hx => ⟨ne_of_gt (pow_pos (a := c x) (hu hx) _), hx.2⟩
  have hiφ : ∀ n, ∫ x in s, φ n x ∂μ = 1 := fun n => by
    rw [integral_mul_left, inv_mul_cancel (P n).ne']
  have A : ∀ u : Set α, IsOpen u → x₀ ∈ u → TendstoUniformlyOn φ 0 atTop (s \ u) := by
    intro u u_open x₀u
    obtain ⟨t, t_pos, tx₀, ht⟩ : ∃ t, 0 ≤ t ∧ t < c x₀ ∧ ∀ x ∈ s \ u, c x ≤ t := by
      rcases eq_empty_or_nonempty (s \ u) with (h | h)
      · exact
          ⟨0, le_rfl, hnc₀, by simp only [h, mem_empty_iff_false, IsEmpty.forall_iff, imp_true_iff]⟩
      obtain ⟨x, hx, h'x⟩ : ∃ x ∈ s \ u, ∀ y ∈ s \ u, c y ≤ c x :=
        IsCompact.exists_isMaxOn (hs.diff u_open) h (hc.mono (diff_subset _ _))
      refine' ⟨c x, hnc x hx.1, h'c x hx.1 _, h'x⟩
      rintro rfl
      exact hx.2 x₀u
    obtain ⟨t', tt', t'x₀⟩ : ∃ t', t < t' ∧ t' < c x₀ := exists_between tx₀
    have t'_pos : 0 < t' := t_pos.trans_lt tt'
    obtain ⟨v, v_open, x₀_v, hv⟩ : ∃ v : Set α, IsOpen v ∧ x₀ ∈ v ∧ v ∩ s ⊆ c ⁻¹' Ioi t' :=
      _root_.continuousOn_iff.1 hc x₀ h₀ (Ioi t') isOpen_Ioi t'x₀
    have M : ∀ n, ∀ x ∈ s \ u, φ n x ≤ (μ (v ∩ s)).toReal⁻¹ * (t / t') ^ n := by
      intro n x hx
      have B : t' ^ n * (μ (v ∩ s)).toReal ≤ ∫ y in s, c y ^ n ∂μ :=
        calc
          t' ^ n * (μ (v ∩ s)).toReal = ∫ _ in v ∩ s, t' ^ n ∂μ := by
            simp only [integral_const, Measure.restrict_apply, MeasurableSet.univ, univ_inter,
              Algebra.id.smul_eq_mul, mul_comm]
          _ ≤ ∫ y in v ∩ s, c y ^ n ∂μ := by
            apply set_integral_mono_on _ _ (v_open.measurableSet.inter hs.measurableSet) _
            · apply integrableOn_const.2 (Or.inr _)
              exact lt_of_le_of_lt (measure_mono (inter_subset_right _ _)) hs.measure_lt_top
            · exact (I n).mono (inter_subset_right _ _) le_rfl
            · intro x hx
              exact pow_le_pow_left t'_pos.le (le_of_lt (hv hx)) _
          _ ≤ ∫ y in s, c y ^ n ∂μ :=
            set_integral_mono_set (I n) (J n) (eventually_of_forall (inter_subset_right _ _))
      simp_rw [← div_eq_inv_mul, div_pow, div_div]
      apply div_le_div (pow_nonneg t_pos n) _ _ B
      · exact pow_le_pow_left (hnc _ hx.1) (ht x hx) _
      · apply mul_pos (pow_pos (t_pos.trans_lt tt') _) (ENNReal.toReal_pos (hμ v v_open x₀_v).ne' _)
        have : μ (v ∩ s) ≤ μ s := measure_mono (inter_subset_right _ _)
        exact ne_of_lt (lt_of_le_of_lt this hs.measure_lt_top)
    have N :
      Tendsto (fun n => (μ (v ∩ s)).toReal⁻¹ * (t / t') ^ n) atTop
        (𝓝 ((μ (v ∩ s)).toReal⁻¹ * 0)) := by
      apply Tendsto.mul tendsto_const_nhds _
      apply tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg t_pos t'_pos.le)
      exact (div_lt_one t'_pos).2 tt'
    rw [mul_zero] at N
    refine' tendstoUniformlyOn_iff.2 fun ε εpos => _
    filter_upwards [(tendsto_order.1 N).2 ε εpos] with n hn x hx
    simp only [Pi.zero_apply, dist_zero_left, Real.norm_of_nonneg (hnφ n x hx.1)]
    exact (M n x hx).trans_lt hn
  have : Tendsto (fun i : ℕ => ∫ x : α in s, φ i x • g x ∂μ) atTop (𝓝 (g x₀)) := by
    have B : Tendsto (fun i ↦ ∫ (x : α) in s, φ i x ∂μ) atTop (𝓝 1) :=
      tendsto_const_nhds.congr (fun n ↦ (hiφ n).symm)
    have C : ∀ᶠ (i : ℕ) in atTop, AEStronglyMeasurable (fun x ↦ φ i x) (μ.restrict s) := by
      apply eventually_of_forall (fun n ↦ ((I n).const_mul _).aestronglyMeasurable)
    exact tendsto_set_integral_peak_smul_of_integrableOn_of_tendsto hs.measurableSet hs.measurableSet
      (Subset.rfl) (self_mem_nhdsWithin)
      hs.measure_lt_top.ne (eventually_of_forall hnφ) A B C hmg hcg
  convert this
  simp_rw [← smul_smul, integral_smul]
#align tendsto_set_integral_pow_smul_of_unique_maximum_of_is_compact_of_measure_nhds_within_pos tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos

/-- If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀` if `g` is
integrable on `s` and continuous at `x₀`.

Version assuming that `μ` gives positive mass to all open sets.
For a less precise but more usable version, see
`tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`.
-/
theorem tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn
    [MetrizableSpace α] [IsLocallyFiniteMeasure μ] [IsOpenPosMeasure μ] (hs : IsCompact s)
    {c : α → ℝ} (hc : ContinuousOn c s) (h'c : ∀ y ∈ s, y ≠ x₀ → c y < c x₀)
    (hnc : ∀ x ∈ s, 0 ≤ c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ ∈ closure (interior s))
    (hmg : IntegrableOn g s μ) (hcg : ContinuousWithinAt g s x₀) :
    Tendsto (fun n : ℕ => (∫ x in s, c x ^ n ∂μ)⁻¹ • ∫ x in s, c x ^ n • g x ∂μ) atTop
      (𝓝 (g x₀)) := by
  have : x₀ ∈ s := by rw [← hs.isClosed.closure_eq]; exact closure_mono interior_subset h₀
  apply
    tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos hs _ hc
      h'c hnc hnc₀ this hmg hcg
  intro u u_open x₀_u
  calc
    0 < μ (u ∩ interior s) :=
      (u_open.inter isOpen_interior).measure_pos μ (_root_.mem_closure_iff.1 h₀ u u_open x₀_u)
    _ ≤ μ (u ∩ s) := measure_mono (inter_subset_inter_right _ interior_subset)
#align tendsto_set_integral_pow_smul_of_unique_maximum_of_is_compact_of_integrable_on tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn

/-- If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀` if `g` is
continuous on `s`. -/
theorem tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
    [MetrizableSpace α] [IsLocallyFiniteMeasure μ] [IsOpenPosMeasure μ] (hs : IsCompact s)
    {c : α → ℝ} (hc : ContinuousOn c s) (h'c : ∀ y ∈ s, y ≠ x₀ → c y < c x₀)
    (hnc : ∀ x ∈ s, 0 ≤ c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ ∈ closure (interior s))
    (hmg : ContinuousOn g s) :
    Tendsto (fun n : ℕ => (∫ x in s, c x ^ n ∂μ)⁻¹ • ∫ x in s, c x ^ n • g x ∂μ) atTop (𝓝 (g x₀)) :=
  haveI : x₀ ∈ s := by rw [← hs.isClosed.closure_eq]; exact closure_mono interior_subset h₀
  tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn hs hc h'c hnc hnc₀ h₀
    (hmg.integrableOn_compact hs) (hmg x₀ this)
#align tendsto_set_integral_pow_smul_of_unique_maximum_of_is_compact_of_continuous_on tendsto_set_integral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn

/-!
### Peak functions of the form `x ↦ c ^ (-dim) φ (c x)`
-/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {μ : Measure F} [IsAddHaarMeasure μ]

theorem glouk (f : F → ℝ) (hf : ∀ x, 0 ≤ f x) (h'f : ∫ x, f x ∂μ = 1)
  (g : F → E) (hg : Integrable E) (h'g : ContinuousAt g 0) :
  Tendsto (fun c ↦ ∫ )
