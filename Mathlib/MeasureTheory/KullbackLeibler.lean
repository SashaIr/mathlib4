/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import Mathlib.Analysis.Convex.Integral

/-!
# Kullback-Leibler divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Real

open scoped ENNReal NNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

lemma withDensity_mono {μ : Measure α} {f g : α → ℝ≥0∞} (hfg : ∀ᵐ x ∂μ, f x ≤ g x) :
    μ.withDensity f ≤ μ.withDensity g := by
  intro s hs
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  refine set_lintegral_mono_ae' hs ?_
  filter_upwards [hfg] with x h_le using fun _ ↦ h_le

lemma withDensity_inv_same_le (μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).withDensity f⁻¹ ≤ μ := by
  change (μ.withDensity f).withDensity (fun x ↦ (f x)⁻¹) ≤ μ
  rw [← withDensity_mul _ hf hf.inv]
  suffices (f * fun x ↦ (f x)⁻¹) ≤ᵐ[μ] 1 by
    refine (withDensity_mono this).trans ?_
    rw [withDensity_one]
  refine ae_of_all _ (fun x ↦ ?_)
  simp only [Pi.mul_apply, Pi.one_apply]
  by_cases hx_top : f x = ∞
  · simp only [hx_top, ENNReal.inv_top, mul_zero, zero_le]
  by_cases hx_zero : f x = 0
  · simp only [hx_zero, ENNReal.inv_zero, zero_mul, zero_le]
  rw [ENNReal.mul_inv_cancel hx_zero hx_top]

lemma withDensity_inv_same (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : Measurable f) (hf_pos : ∀ᵐ x ∂μ, 0 < f x) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    (μ.withDensity f).withDensity f⁻¹ = μ := by
  change (μ.withDensity f).withDensity (fun x ↦ (f x)⁻¹) = μ
  rw [← withDensity_mul _ hf hf.inv]
  suffices (f * fun x ↦ (f x)⁻¹) =ᵐ[μ] 1 by
    rw [withDensity_congr_ae this, withDensity_one]
  filter_upwards [hf_pos, hf_ne_top] with x hf_pos hf_ne_top
  simp only [Pi.mul_apply]
  rw [ENNReal.mul_inv_cancel hf_pos.ne' hf_ne_top, Pi.one_apply]

lemma Measure.rnDeriv_ne_top (μ ν : Measure α) [SigmaFinite μ] : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≠ ∞ := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx using hx.ne

lemma Measure.rnDeriv_pos {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x := by
  rw [← Measure.withDensity_rnDeriv_eq _ _  hμν,
    ae_withDensity_iff (Measure.measurable_rnDeriv _ _), Measure.withDensity_rnDeriv_eq _ _  hμν]
  exact ae_of_all _ (fun x hx ↦ lt_of_le_of_ne (zero_le _) hx.symm)

lemma inv_rnDeriv {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ := by
  suffices μ.withDensity (μ.rnDeriv ν)⁻¹ = μ.withDensity (ν.rnDeriv μ) by
    calc (μ.rnDeriv ν)⁻¹ =ᵐ[μ] (μ.withDensity (μ.rnDeriv ν)⁻¹).rnDeriv μ :=
          (Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _).inv).symm
    _ = (μ.withDensity (ν.rnDeriv μ)).rnDeriv μ := by rw [this]
    _ =ᵐ[μ] ν.rnDeriv μ := Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)
  rw [Measure.withDensity_rnDeriv_eq _ _ hνμ]
  have : μ = ν.withDensity (μ.rnDeriv ν) := (Measure.withDensity_rnDeriv_eq _ _  hμν).symm
  rw [this]
  conv in (Measure.rnDeriv (Measure.withDensity ν (Measure.rnDeriv μ ν)) ν)⁻¹ => rw [← this]
  rw [withDensity_inv_same]
  · exact Measure.measurable_rnDeriv _ _
  · exact hνμ.ae_le (Measure.rnDeriv_pos hμν)
  · exact Measure.rnDeriv_ne_top _ _

lemma Measure.mutuallySingular_self {μ : Measure α} (h : μ ⟂ₘ μ) : μ = 0 := by
  obtain ⟨s, hs, hμs, hμs_compl⟩ := h
  suffices μ Set.univ = 0 by rwa [measure_univ_eq_zero] at this
  rw [← Set.union_compl_self s, measure_union disjoint_compl_right hs.compl, hμs, hμs_compl,
    add_zero]

lemma withDensity_rnDeriv_eq_zero {μ ν : Measure α} [Measure.HaveLebesgueDecomposition ν μ] :
    μ.withDensity (ν.rnDeriv μ) = 0 ↔ μ ⟂ₘ ν := by
  have h_dec := Measure.haveLebesgueDecomposition_add ν μ
  constructor
  · intro h
    rw [h, add_zero] at h_dec
    rw [h_dec]
    exact (Measure.mutuallySingular_singularPart ν μ).symm
  · intro h
    rw [h_dec] at h
    rw [Measure.MutuallySingular.add_right_iff] at h
    refine Measure.mutuallySingular_self ?_
    refine Measure.MutuallySingular.mono_ac h.2 ?_ Measure.AbsolutelyContinuous.rfl
    exact withDensity_absolutelyContinuous _ _

lemma ae_eq_of_withDensity_eq {μ : Measure α} {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hf_int : ∫⁻ x, f x ∂μ ≠ ∞)
    (hg : AEMeasurable g μ) (hg_int : ∫⁻ x, g x ∂μ ≠ ∞) (h : μ.withDensity f = μ.withDensity g) :
    f =ᵐ[μ] g := by
  -- todo: fix the name of that theorem
  refine AeMeasurable.ae_eq_of_forall_set_lintegral_eq hf hg hf_int hg_int fun s hs _ ↦ ?_
  rw [Measure.ext_iff] at h
  specialize h s hs
  rwa [withDensity_apply _ hs ,withDensity_apply _ hs] at h

lemma Measure.add_left_cancel {μ ν₁ ν₂ : Measure α} (h₁ : μ ⟂ₘ ν₁) (h₂ : μ ⟂ₘ ν₂) :
    μ + ν₁ = μ + ν₂ ↔ ν₁ = ν₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  obtain ⟨t₁, ht₁, ht₁μ, ht₁ν₁⟩ := h₁
  obtain ⟨t₂, ht₂, ht₂μ, ht₂ν₂⟩ := h₂
  ext1 s hs
  have hs_eq : s = (s ∩ (t₁ ∪ t₂)) ∪ (s ∩ (t₁ ∪ t₂)ᶜ) := (Set.inter_union_compl _ _).symm
  have h₁_eq : ν₁ s = ν₁ (s ∩ (t₁ ∪ t₂)) := by
    conv_lhs => rw [hs_eq]
    rw [measure_union _ (hs.inter (ht₁.union ht₂).compl)]
    · suffices ν₁ (s ∩ (t₁ ∪ t₂)ᶜ) = 0 by rw [this, add_zero]
      refine measure_mono_null (Set.inter_subset_right _ _) ?_
      rw [Set.compl_union]
      exact measure_mono_null (Set.inter_subset_left _ _) ht₁ν₁
    · rw [Set.disjoint_iff_inter_eq_empty]
      ext1 x
      simp only [Set.compl_union, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
        Set.mem_empty_iff_false, iff_false, not_and, not_not, and_imp]
      intro _ hxt _ hx₁
      cases hxt with
      | inl h => exact absurd h hx₁
      | inr h => exact h
  have h₂_eq : ν₂ s = ν₂ (s ∩ (t₁ ∪ t₂)) := by
    conv_lhs => rw [hs_eq]
    rw [measure_union _ (hs.inter (ht₁.union ht₂).compl)]
    · suffices ν₂ (s ∩ (t₁ ∪ t₂)ᶜ) = 0 by rw [this, add_zero]
      refine measure_mono_null (Set.inter_subset_right _ _) ?_
      rw [Set.compl_union]
      exact measure_mono_null (Set.inter_subset_right _ _) ht₂ν₂
    · rw [Set.disjoint_iff_inter_eq_empty]
      ext1 x
      simp only [Set.compl_union, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
        Set.mem_empty_iff_false, iff_false, not_and, not_not, and_imp]
      intro _ hxt _ hx₁
      cases hxt with
      | inl h => exact absurd h hx₁
      | inr h => exact h
  have hμ_eq : μ (s ∩ (t₁ ∪ t₂)) = 0 := by
    refine measure_mono_null (Set.inter_subset_right _ _) ?_
    refine le_antisymm ((measure_union_le _ _).trans ?_) (zero_le _)
    simp only [nonpos_iff_eq_zero, add_eq_zero]
    exact ⟨ht₁μ, ht₂μ⟩
  rw [Measure.ext_iff] at h
  specialize h (s ∩ (t₁ ∪ t₂)) (hs.inter (ht₁.union ht₂))
  simp only [add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply] at h
  rwa [hμ_eq, zero_add, zero_add, ← h₁_eq, ← h₂_eq] at h

lemma rnDeriv_add (ν₁ ν₂ : Measure α) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (μ : Measure α) [ν₁.HaveLebesgueDecomposition μ]
    [ν₂.HaveLebesgueDecomposition μ] [(ν₁ + ν₂).HaveLebesgueDecomposition μ] :
    (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDeriv μ + ν₂.rnDeriv μ := by
  refine ae_eq_of_withDensity_eq (Measure.measurable_rnDeriv _ _).aemeasurable ?_ ?_ ?_ ?_
  · exact (Measure.lintegral_rnDeriv_lt_top (ν₁ + ν₂) μ).ne
  · exact ((Measure.measurable_rnDeriv _ _).add (Measure.measurable_rnDeriv _ _)).aemeasurable
  · simp_rw [Pi.add_apply]
    rw [lintegral_add_left (Measure.measurable_rnDeriv _ _)]
    simp only [ne_eq, ENNReal.add_eq_top]
    push_neg
    exact ⟨(Measure.lintegral_rnDeriv_lt_top ν₁ μ).ne, (Measure.lintegral_rnDeriv_lt_top ν₂ μ).ne⟩
  · suffices (ν₁ + ν₂).singularPart μ + μ.withDensity ((ν₁ + ν₂).rnDeriv μ)
        = (ν₁ + ν₂).singularPart μ + μ.withDensity (ν₁.rnDeriv μ + ν₂.rnDeriv μ) by
      rwa [Measure.add_left_cancel] at this
      · refine Measure.MutuallySingular.mono_ac ((ν₁ + ν₂).mutuallySingular_singularPart μ)
          Measure.AbsolutelyContinuous.rfl ?_
        exact withDensity_absolutelyContinuous _ _
      · refine Measure.MutuallySingular.mono_ac ((ν₁ + ν₂).mutuallySingular_singularPart μ)
          Measure.AbsolutelyContinuous.rfl ?_
        exact withDensity_absolutelyContinuous _ _
    rw [← (ν₁ + ν₂).haveLebesgueDecomposition_add μ, Measure.singularPart_add,
      withDensity_add_left (Measure.measurable_rnDeriv _ _), add_assoc,
      add_comm (ν₂.singularPart μ), add_assoc, add_comm _ (ν₂.singularPart μ),
      ← ν₂.haveLebesgueDecomposition_add μ, ← add_assoc, ← ν₁.haveLebesgueDecomposition_add μ]

lemma rnDeriv_ae_eq_zero_of_mutuallySingular {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ⟂ₘ ν) :
    μ.rnDeriv ν =ᵐ[ν] 0 := by
  refine (Measure.eq_rnDeriv measurable_zero hμν ?_).symm
  simp only [withDensity_zero, add_zero]

lemma lintegral_rnDeriv {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∫⁻ x, μ.rnDeriv ν x ∂ν = μ Set.univ := by
  conv_rhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

lemma integral_toReal_rnDeriv {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∫ x, (μ.rnDeriv ν x).toReal ∂ν = (μ Set.univ).toReal := by
  rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable (Measure.rnDeriv_lt_top _ _),
    ENNReal.toReal_eq_toReal_iff, lintegral_rnDeriv hμν]
  simp only [Measure.measure_univ_eq_zero, true_or]

section x_log_x

namespace Real

lemma continuous_id_mul_log : Continuous (fun x ↦ x * log x) := by
  sorry

lemma convexOn_id_mul_log : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x) := by
  sorry

lemma id_mul_log_ge {x : ℝ} (hx : 0 ≤ x) : log (exp 1) / (exp 1) ≤ x * log x := by
  sorry

lemma id_mul_log_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ x * log x :=
  mul_nonneg (zero_le_one.trans hx) (log_nonneg hx)

lemma measurable_id_mul_log : Measurable (fun x ↦ x * log x) :=
  measurable_id'.mul measurable_log

end Real

end x_log_x

section tilted

noncomputable
def Λ (μ : Measure α) (f : α → ℝ) : ℝ := log (∫ x, exp (f x) ∂μ)

@[simp]
lemma Λ_zero_right (μ : Measure α) [IsProbabilityMeasure μ] : Λ μ 0 = 0 := by simp [Λ]

noncomputable
def Measure.tilted (μ : Measure α) (f : α → ℝ) : Measure α :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (exp (f x - Λ μ f)))

lemma tilted_absolutelyContinuous {μ : Measure α} {f : α → ℝ} : μ.tilted f ≪ μ :=
  withDensity_absolutelyContinuous _ _

@[simp]
lemma tilted_zero (μ : Measure α) [IsProbabilityMeasure μ] : μ.tilted 0 = μ := by
  simp only [Measure.tilted, Λ, Pi.zero_apply, exp_zero, integral_const, measure_univ,
    ENNReal.one_toReal, smul_eq_mul, mul_one, log_one, sub_self, ENNReal.ofReal_one]
  exact withDensity_one

lemma tilted_eq_withDensity_nnreal (μ : Measure α) (f : α → ℝ) :
    μ.tilted f = μ.withDensity
      (fun x ↦ ((↑) : ℝ≥0 → ℝ≥0∞) (⟨exp (f x - Λ μ f), (exp_pos _).le⟩ : ℝ≥0)) := by
  rw [Measure.tilted]
  congr
  ext1 x
  rw [ENNReal.ofReal_eq_coe_nnreal]

lemma tilted_apply (μ : Measure α) (f : α → ℝ) {s : Set α} (hs : MeasurableSet s) :
    μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a - Λ μ f)) ∂μ := by
  rw [Measure.tilted, withDensity_apply _ hs]

lemma tilted_apply_eq_ofreal_integral (μ : Measure α)
    {f : α → ℝ} (hf : Integrable (fun x ↦ exp (f x)) μ)
    {s : Set α} (hs : MeasurableSet s) :
    μ.tilted f s = ENNReal.ofReal (∫ a in s, exp (f a - Λ μ f) ∂μ) := by
  rw [tilted_apply _ _ hs, ← ofReal_integral_eq_lintegral_ofReal]
  · simp_rw [exp_sub, div_eq_mul_inv]
    refine Integrable.integrableOn ?_
    exact hf.mul_const _
  · exact ae_of_all _ (fun x ↦ (exp_pos _).le)

lemma lintegral_tilted {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ) (g : α → ℝ≥0∞) :
    ∫⁻ x, g x ∂(μ.tilted f) = ∫⁻ x, ENNReal.ofReal (exp (f x - Λ μ f)) * (g x) ∂μ := by
  rw [Measure.tilted, lintegral_withDensity_eq_lintegral_mul_non_measurable₀]
  · simp only [Pi.mul_apply]
  · refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    exact (measurable_exp.comp_aemeasurable (hf.sub aemeasurable_const))
  · refine ae_of_all _ ?_
    simp only [ENNReal.ofReal_lt_top, implies_true]

lemma set_lintegral_tilted {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ) (g : α → ℝ≥0∞)
    {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, g x ∂(μ.tilted f) = ∫⁻ x in s, ENNReal.ofReal (exp (f x - Λ μ f)) * (g x) ∂μ := by
  rw [Measure.tilted, set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀]
  · simp only [Pi.mul_apply]
  · refine AEMeasurable.restrict ?_
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    exact measurable_exp.comp_aemeasurable (hf.sub aemeasurable_const)
  · exact hs
  · refine ae_of_all _ ?_
    simp only [ENNReal.ofReal_lt_top, implies_true]

lemma integral_tilted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ) (g : α → E) :
    ∫ x, g x ∂(μ.tilted f) = ∫ x, exp (f x - Λ μ f) • (g x) ∂μ := by
  rw [tilted_eq_withDensity_nnreal, integral_withDensity_eq_integral_smul₀]
  · congr
  · suffices AEMeasurable (fun x ↦ exp (f x - Λ μ f)) μ by
      rw [← aEMeasurable_coe_nnreal_real_iff]
      simpa only [NNReal.coe_mk]
    exact measurable_exp.comp_aemeasurable (hf.sub aemeasurable_const)

lemma set_integral_tilted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ) (g : α → E)
    {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.tilted f) = ∫ x in s, exp (f x - Λ μ f) • (g x) ∂μ := by
  rw [tilted_eq_withDensity_nnreal, set_integral_withDensity_eq_set_integral_smul₀ _ _ hs]
  · congr
  · suffices AEMeasurable (fun x ↦ exp (f x - Λ μ f)) μ by
      rw [← aEMeasurable_coe_nnreal_real_iff]
      refine AEMeasurable.restrict ?_
      simpa only [NNReal.coe_mk]
    exact measurable_exp.comp_aemeasurable (hf.sub aemeasurable_const)

lemma integral_exp_pos {μ : Measure α} {f : α → ℝ} [hμ : NeZero μ]
    (hf : Integrable (fun x ↦ exp (f x)) μ) :
    0 < ∫ x, exp (f x) ∂μ := by
  rw [integral_pos_iff_support_of_nonneg]
  · suffices (Function.support fun x ↦ exp (f x)) = Set.univ by
      rw [this]
      simp only [Measure.measure_univ_pos, ne_eq]
      exact hμ.out
    ext1 x
    simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
    exact (exp_pos _).ne'
  · exact fun x ↦ (exp_pos _).le
  · exact hf

lemma isProbabilityMeasure_tilted {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Integrable (fun x ↦ exp (f x)) μ) :
    IsProbabilityMeasure (μ.tilted f) := by
  constructor
  simp only [Measure.tilted, MeasurableSet.univ, withDensity_apply, Measure.restrict_univ]
  simp_rw [exp_sub]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · suffices ∫ x, exp (f x) / exp (Λ μ f) ∂μ = 1 by
      simp only [this, ENNReal.ofReal_one]
    rw [Λ, exp_log]
    · simp_rw [div_eq_mul_inv]
      rw [integral_mul_right, mul_inv_cancel]
      refine (ne_of_lt ?_).symm
      exact integral_exp_pos hf
    · exact integral_exp_pos hf
  · exact hf.div_const _
  · exact ae_of_all _ (fun x ↦ div_nonneg (exp_pos _).le (exp_pos _).le)

lemma Λ_tilted {μ : Measure α} [NeZero μ] {f g : α → ℝ} (hf : AEMeasurable f μ)
    (hfg : Integrable (fun x ↦ exp ((f + g) x)) μ) :
    Λ (μ.tilted f) g = Λ μ (f + g) - Λ μ f := by
  rw [Λ, integral_tilted hf]
  simp_rw [smul_eq_mul, ← exp_add]
  have : (fun x ↦ exp (f x - Λ μ f + g x)) = fun x ↦ exp ((f + g) x) * exp (- Λ μ f) := by
    ext x
    rw [Pi.add_apply, ← exp_add]
    congr 1
    abel
  simp_rw [this]
  rw [integral_mul_right, log_mul (integral_exp_pos hfg).ne' (exp_pos _).ne', log_exp,
    ← sub_eq_add_neg]
  rfl

lemma tilted_tilted {μ : Measure α} {f g : α → ℝ} [NeZero μ] (hf : AEMeasurable f μ)
    (hfg : Integrable (fun x ↦ exp ((f + g) x)) μ) :
    (μ.tilted f).tilted g = μ.tilted (f + g) := by
  ext1 s hs
  rw [tilted_apply _ _ hs, tilted_apply _ _ hs, set_lintegral_tilted hf _ hs]
  congr with x
  rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add, Λ_tilted hf hfg, Pi.add_apply]
  congr 2
  abel

lemma absolutelyContinuous_tilted {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) :
    μ ≪ μ.tilted f := by
  have : μ = (μ.tilted f).tilted (-f) := by
    rw [tilted_tilted hf ?_, add_right_neg, tilted_zero]
    simp only [Pi.add_apply, Pi.neg_apply, add_right_neg, exp_zero, integrable_const]
  nth_rw 1 [this]
  exact tilted_absolutelyContinuous

lemma rnDeriv_tilted_left_self (μ : Measure α) [SigmaFinite μ] {f : α → ℝ} (hf : Measurable f) :
    (μ.tilted f).rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (exp (f x - Λ μ f)) :=
  Measure.rnDeriv_withDensity μ (hf.sub measurable_const).exp.ennreal_ofReal

lemma log_rnDeriv_tilted_left_self (μ : Measure α) [SigmaFinite μ] {f : α → ℝ} (hf : Measurable f) :
    (fun x ↦ log ((μ.tilted f).rnDeriv μ x).toReal)
      =ᵐ[μ] fun x ↦ f x - Λ μ f := by
  filter_upwards [rnDeriv_tilted_left_self μ hf] with x hx
  rw [hx, ENNReal.toReal_ofReal (exp_pos _).le, log_exp]

lemma rnDeriv_tilted_left (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {f : α → ℝ} (hf : Measurable f) :
    (fun x ↦ ((μ.tilted f).rnDeriv ν x).toReal)
      =ᵐ[ν] fun x ↦ exp (f x - Λ μ f) * (μ.rnDeriv ν x).toReal := by
  sorry

-- todo: generalize with this
theorem ae_le_of_forall_set_lintegral_le_of_sigmaFinite₀ {μ : Measure α} [SigmaFinite μ]
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ) :
    f ≤ᵐ[μ] g := by
  have h' : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, hf.mk f x ∂μ ≤ ∫⁻ x in s, hg.mk g x ∂μ := by
    intro s hs hμs
    specialize h s hs hμs
    refine (set_lintegral_congr_fun hs ?_).trans_le (h.trans_eq (set_lintegral_congr_fun hs ?_))
    · filter_upwards [hf.ae_eq_mk] with a ha using fun _ ↦ ha.symm
    · filter_upwards [hg.ae_eq_mk] with a ha using fun _ ↦ ha
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk,
    ae_le_of_forall_set_lintegral_le_of_sigmaFinite hf.measurable_mk hg.measurable_mk h']
    with a haf hag ha
  rwa [haf, hag]

-- todo: generalize with this
theorem ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite₀ {μ : Measure α} [SigmaFinite μ]
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) : f =ᵐ[μ] g := by
  have A : f ≤ᵐ[μ] g :=
    ae_le_of_forall_set_lintegral_le_of_sigmaFinite₀ hf hg fun s hs h's => le_of_eq (h s hs h's)
  have B : g ≤ᵐ[μ] f :=
    ae_le_of_forall_set_lintegral_le_of_sigmaFinite₀ hg hf fun s hs h's => ge_of_eq (h s hs h's)
  filter_upwards [A, B] with x using le_antisymm

-- todo: generalize with this
theorem Measure.eq_withDensity_rnDeriv₀ {μ ν : Measure α} {s : Measure α}
    {f : α → ℝ≥0∞} (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) :
    ν.withDensity f = ν.withDensity (μ.rnDeriv ν) := by
  rw [withDensity_congr_ae hf.ae_eq_mk] at hadd ⊢
  exact Measure.eq_withDensity_rnDeriv hf.measurable_mk hs hadd

-- todo: generalize eq_rnDeriv with this
theorem Measure.eq_rnDeriv₀ {μ ν : Measure α} [SigmaFinite ν] {s : Measure α}
    {f : α → ℝ≥0∞} (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : f =ᵐ[ν] μ.rnDeriv ν := by
  refine' ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite₀ hf
    (measurable_rnDeriv μ ν).aemeasurable _
  intro a ha _
  calc
    ∫⁻ x : α in a, f x ∂ν = ν.withDensity f a := (withDensity_apply f ha).symm
    _ = ν.withDensity (μ.rnDeriv ν) a := by rw [eq_withDensity_rnDeriv₀ hf hs hadd]
    _ = ∫⁻ x : α in a, μ.rnDeriv ν x ∂ν := withDensity_apply _ ha

lemma aemeasurable_of_aemeasurable_exp {μ : Measure α} {f : α → ℝ}
    (hf : AEMeasurable (fun x ↦ exp (f x)) μ) :
    AEMeasurable f μ := by
  have : f = fun x ↦ log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp_aemeasurable hf

lemma AEMeasurable.of_absolutelyContinuous {β : Type*} {_ : MeasurableSpace β}
    {μ ν : Measure α} {f : α → β} (hf : AEMeasurable f ν) (hμν : μ ≪ ν) :
    AEMeasurable f μ :=
  ⟨hf.mk f, hf.measurable_mk, hμν.ae_le hf.ae_eq_mk⟩

lemma rnDeriv_tilted_right_of_absolutelyContinuous (μ ν : Measure α) [SigmaFinite μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν)
    {f : α → ℝ} (hf : AEMeasurable f ν) (h_int : Integrable (fun x ↦ exp (f x)) ν) :
    (fun x ↦ (μ.rnDeriv (ν.tilted f) x).toReal)
      =ᵐ[ν] fun x ↦ exp (- f x + Λ ν f) * (μ.rnDeriv ν x).toReal := by
  suffices μ.rnDeriv (ν.tilted f)
      =ᵐ[ν] fun x ↦ (ENNReal.ofReal (exp (- f x + Λ ν f)) * μ.rnDeriv ν x) by
    suffices (fun x ↦ (μ.rnDeriv (ν.tilted f) x).toReal)
        =ᵐ[ν] fun x ↦ (ENNReal.ofReal (exp (- f x + Λ ν f)) * μ.rnDeriv ν x).toReal by
      filter_upwards [this] with x hx
      rw [hx, ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le]
    filter_upwards [this] with x hx
    rw [hx]
  symm
  refine (absolutelyContinuous_tilted hf).ae_le ?_
  have : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted h_int
  refine Measure.eq_rnDeriv₀ ?_ Measure.MutuallySingular.zero_left ?_
  · simp only
    refine AEMeasurable.mul ?_ (Measure.measurable_rnDeriv _ _).aemeasurable
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    refine measurable_exp.comp_aemeasurable ((AEMeasurable.neg ?_).add aemeasurable_const)
    exact AEMeasurable.of_absolutelyContinuous hf tilted_absolutelyContinuous
  · ext1 s hs
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    rw [zero_add]
    simp only [Measure.add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply]
    rw [withDensity_apply _ hs, withDensity_apply _ hs, set_lintegral_tilted hf _ hs]
    simp_rw [← mul_assoc, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
    congr with x
    simp only [sub_add_add_cancel, add_right_neg, exp_zero, ENNReal.ofReal_one, one_mul]

lemma rnDeriv_tilted_right (μ ν : Measure α) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    {f : α → ℝ} (hf : AEMeasurable f ν) (h_int : Integrable (fun x ↦ exp (f x)) ν) :
    (fun x ↦ (μ.rnDeriv (ν.tilted f) x).toReal)
      =ᵐ[ν] fun x ↦ exp (- f x + Λ ν f) * (μ.rnDeriv ν x).toReal := by
  have : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted h_int
  let μ' := ν.withDensity (μ.rnDeriv ν)
  have h₁ : μ.rnDeriv (ν.tilted f) =ᵐ[ν] μ'.rnDeriv (ν.tilted f) := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
    have hν_ac : ν ≪ ν.tilted f := absolutelyContinuous_tilted hf
    have h_add : (μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)).rnDeriv (ν.tilted f)
        =ᵐ[ν] (μ.singularPart ν).rnDeriv (ν.tilted f) + _ :=
      hν_ac.ae_le (rnDeriv_add (μ.singularPart ν) μ' (ν.tilted f))
    refine h_add.trans ?_
    suffices (μ.singularPart ν).rnDeriv (ν.tilted f) =ᵐ[ν] 0 by
      filter_upwards [this] with x hx
      rw [Pi.add_apply, hx, Pi.zero_apply, zero_add]
    refine hν_ac.ae_le ?_
    refine rnDeriv_ae_eq_zero_of_mutuallySingular ?_
    exact Measure.MutuallySingular.mono_ac (μ.mutuallySingular_singularPart ν)
      Measure.AbsolutelyContinuous.rfl tilted_absolutelyContinuous
  have h₂ : μ.rnDeriv ν =ᵐ[ν] μ'.rnDeriv ν :=
    (Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)).symm
  have hμ' := rnDeriv_tilted_right_of_absolutelyContinuous μ' ν
    (withDensity_absolutelyContinuous ν _) hf h_int
  filter_upwards [h₁, h₂, hμ'] with x hx₁ hx₂ hx_eq
  rw [hx₁, hx₂, hx_eq]

lemma singularPart_tilted_right {μ ν : Measure α} [SigmaFinite μ] [IsProbabilityMeasure ν]
    {f : α → ℝ} (hf : Measurable f) (h_int : Integrable (fun x ↦ exp (f x)) ν) :
    μ.singularPart (ν.tilted f) = μ.singularPart ν := by
  have : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted h_int
  sorry

end tilted

section definition

/-- Log-Likelihood Ratio. -/
noncomputable
def LLR (μ ν : Measure α) (x : α) : ℝ := log (μ.rnDeriv ν x).toReal

lemma exp_LLR (μ ν : Measure α) [SigmaFinite μ] :
    (fun x ↦ exp (LLR μ ν x))
      =ᵐ[ν] fun x ↦ if μ.rnDeriv ν x = 0 then 1 else (μ.rnDeriv ν x).toReal := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
  by_cases h_zero : μ.rnDeriv ν x = 0
  · simp only [LLR, h_zero, ENNReal.zero_toReal, log_zero, exp_zero, ite_true]
  rw [LLR, exp_log, if_neg h_zero]
  rw [ENNReal.toReal_pos_iff]
  exact ⟨lt_of_le_of_ne (zero_le _) (Ne.symm h_zero), hx⟩

-- TODO: this should be in EReal?
-- TODO: should also take value ∞ when the log is not integrable
noncomputable
def KL (μ ν : Measure α) [Decidable (μ ≪ ν)] [Decidable (Integrable (LLR μ ν) μ)] : ℝ≥0∞ :=
  if μ ≪ ν ∧ Integrable (LLR μ ν) μ
    then ENNReal.ofReal (∫ x, log (μ.rnDeriv ν x).toReal ∂μ) else ∞

lemma integrable_toReal_rnDeriv {μ ν : Measure α} [IsFiniteMeasure μ] [SigmaFinite ν] :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable
    (Measure.lintegral_rnDeriv_lt_top _ _).ne

lemma integrable_aux {μ ν : Measure α}
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    Integrable
      (fun x ↦ (Measure.rnDeriv μ ν x).toReal * log (Measure.rnDeriv μ ν x).toReal) ν := by
  rw [← memℒp_one_iff_integrable]
  constructor
  · refine (Measurable.stronglyMeasurable ?_).aestronglyMeasurable
    refine (Measure.measurable_rnDeriv _ _).ennreal_toReal.mul ?_
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal.log
  rw [snorm_one_eq_lintegral_nnnorm]
  sorry

lemma integral_LLR_nonneg_aux {μ ν : Measure α} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    (μ Set.univ).toReal * log (μ Set.univ).toReal ≤ ∫ x, LLR μ ν x ∂μ := by
  have h_eq_int : (μ Set.univ).toReal = ∫ x, (μ.rnDeriv ν x).toReal ∂ν := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    simp only [MeasurableSet.univ, withDensity_apply, Measure.restrict_univ]
    rw [integral_toReal]
    · exact (Measure.measurable_rnDeriv _ _).aemeasurable
    · exact Measure.rnDeriv_lt_top _ _
  let φ : ℝ → ℝ := fun x ↦ x * log x
  calc (μ Set.univ).toReal * log (μ Set.univ).toReal
    = φ (μ Set.univ).toReal := rfl
  _ = φ (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [h_eq_int]
  _ ≤ ∫ x, φ (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral, ← average_eq_integral]
    refine ConvexOn.map_average_le Real.convexOn_id_mul_log Real.continuous_id_mul_log.continuousOn
      isClosed_Ici ?_ integrable_toReal_rnDeriv ?_
    · simp
    · exact integrable_aux hμν h_int
  _ = ∫ x, (μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal ∂ν := rfl
  _ = ∫ x, LLR μ ν x ∂μ := by
    simp_rw [LLR]
    conv_rhs =>
      rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
      conv in (Measure.rnDeriv (ν.withDensity (μ.rnDeriv ν)) ν) =>
        rw [Measure.withDensity_rnDeriv_eq _ _ hμν]
    have h_rn_eq : μ.rnDeriv ν =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toNNReal := by
      filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
      rw [ENNReal.coe_toNNReal]
      exact hx.ne
    have h_ν_eq : ν.withDensity (μ.rnDeriv ν)
        = ν.withDensity (fun x ↦ (μ.rnDeriv ν x).toNNReal) := withDensity_congr_ae h_rn_eq
    conv_rhs => rw [h_ν_eq]
    rw [integral_withDensity_eq_integral_smul]
    swap; · exact (Measure.measurable_rnDeriv _ _).ennreal_toNNReal
    congr

lemma integral_LLR_nonneg
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    0 ≤ ∫ x, LLR μ ν x ∂μ := by
  refine le_trans ?_ (integral_LLR_nonneg_aux hμν h_int)
  simp only [measure_univ, ENNReal.one_toReal, log_one, mul_zero, le_refl]

end definition

lemma LLR_tilted_ae_eq {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) {f : α → ℝ} (hf : AEMeasurable f ν) (h_int : Integrable (fun x ↦ exp (f x)) ν) :
    (LLR μ (ν.tilted f)) =ᵐ[μ] fun x ↦ - f x + Λ ν f + LLR μ ν x := by
  filter_upwards [hμν.ae_le (rnDeriv_tilted_right μ ν hf h_int), Measure.rnDeriv_pos hμν,
    hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hx_pos hx_lt_top
  rw [LLR, hx, log_mul (exp_pos _).ne']
  · rw [log_exp, LLR]
  · rw [ne_eq, ENNReal.toReal_eq_zero_iff]
    simp only [hx_pos.ne', hx_lt_top.ne, or_self, not_false_eq_true]

lemma integrable_LLR_tilted
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) {f : α → ℝ} (hf : AEMeasurable f ν) (hfμ : Integrable f μ)
    (hfν : Integrable (fun x ↦ exp (f x)) ν)
    (h_int : Integrable (LLR μ ν) μ) :
    Integrable (LLR μ (ν.tilted f)) μ := by
  rw [integrable_congr (LLR_tilted_ae_eq hμν hf hfν)]
  exact Integrable.add (hfμ.neg.add (integrable_const _)) h_int

lemma todo_aux {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : α → ℝ}
    (hμν : μ ≪ ν) (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ exp (f x)) ν)
    (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ ν x ∂μ - ∫ x, LLR μ (ν.tilted f) x ∂μ = ∫ x, f x ∂μ - Λ ν f := by
  calc ∫ x, LLR μ ν x  ∂μ - ∫ x, LLR μ (ν.tilted f) x ∂μ
    = ∫ x, LLR μ ν x ∂μ - ∫ x, - f x + Λ ν f + LLR μ ν x ∂μ := by
        refine congr_arg₂ _ rfl ?_
        refine integral_congr_ae (LLR_tilted_ae_eq hμν ?_ hfν)
        exact aemeasurable_of_aemeasurable_exp hfν.1.aemeasurable
  _ = ∫ x, LLR μ ν x ∂μ - (- ∫ x, f x ∂μ + Λ ν f + ∫ x, LLR μ ν x ∂μ) := by
        congr
        rw [← integral_neg, integral_add ?_ h_int]
        swap; · exact hfμ.neg.add (integrable_const _)
        rw [integral_add ?_ (integrable_const _)]
        swap; · exact hfμ.neg
        simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
  _ = ∫ x, f x ∂μ - Λ ν f := by abel

-- TODO name
lemma some_le {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ)
    (f : α → ℝ) (hfμ : Integrable f μ) (hf : Integrable (fun x ↦ exp (f x)) ν) :
    ∫ x, f x ∂μ - Λ ν f ≤ ∫ x, LLR μ ν x ∂μ := by
  rw [← todo_aux hμν hfμ hf h_int]
  simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
  have : IsProbabilityMeasure (Measure.tilted ν f) := isProbabilityMeasure_tilted hf
  have hf_m : AEMeasurable f ν := aemeasurable_of_aemeasurable_exp hf.1.aemeasurable
  refine integral_LLR_nonneg (hμν.trans (absolutelyContinuous_tilted hf_m)) ?_
  exact integrable_LLR_tilted hμν hf_m hfμ hf h_int

lemma todo' {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ⨆ (f : α → ℝ) (_ : Integrable f μ)
        (_ : Integrable (fun x ↦ exp (f x)) ν), ∫ x, f x ∂μ - Λ ν f
      ≤ ∫ x, LLR μ ν x ∂μ := by
  refine ciSup_le (fun f ↦ ?_)
  by_cases hfμ : Integrable f μ
  · simp only [hfμ, ciSup_unique]
    by_cases hf : Integrable (fun x ↦ exp (f x)) ν
    · simp only [hf, ciSup_unique]
      exact some_le hμν h_int f hfμ hf
    · simp [hf, ciSup_empty]
      exact integral_LLR_nonneg hμν h_int
  · simp only [hfμ, ciSup_empty]
    exact integral_LLR_nonneg hμν h_int

lemma aux_bddAbove {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    BddAbove (Set.range fun f ↦ ⨆ (_ : Integrable f μ) (_ : Integrable (fun x ↦ exp (f x)) ν),
      ∫ x, f x ∂μ - Λ ν f) := by
  refine ⟨∫ x, LLR μ ν x ∂μ, ?_⟩
  rw [mem_upperBounds]
  intro x
  simp only [Set.mem_range, ge_iff_le, le_max_iff, forall_exists_index]
  rintro f rfl
  by_cases hfμ : Integrable f μ
  · simp only [hfμ, ciSup_unique]
    by_cases hf : Integrable (fun x ↦ exp (f x)) ν
    · simp only [hf, ciSup_unique]
      exact some_le hμν h_int f hfμ hf
    · simp only [hf, ciSup_empty]
      exact integral_LLR_nonneg hμν h_int
  · simp only [hfμ, ciSup_empty]
    exact integral_LLR_nonneg hμν h_int

lemma todo {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ ν x ∂μ
      ≤ ⨆ (f : α → ℝ) (_ : Integrable f μ) (_ : Integrable (fun x ↦ exp (f x)) ν),
        ∫ x, f x ∂μ - Λ ν f := by
  classical
  let LLRu : ℝ → α → ℝ := fun u x ↦ log ((μ.rnDeriv ν x).toReal + u)
  have hu_int : ∀ u, Integrable (LLRu u) μ := by
    sorry
  have h_exp_log : ∀ (u) (hu : 0 < u) (x),
      exp (log ((μ.rnDeriv ν x).toReal + u)) = (μ.rnDeriv ν x).toReal + u := by
    intro u hu x
    rw [exp_log]
    positivity
  have hu_exp_int : ∀ u, 0 < u → Integrable (fun x ↦ exp (LLRu u x)) ν := by
    intro u hu
    simp_rw [h_exp_log u hu]
    exact integrable_toReal_rnDeriv.add (integrable_const _)
  have hu_le : ∫ x, LLR μ ν x ∂μ ≤ ⨅ (u : {v // (0 : ℝ) < v}), ∫ x, LLRu u x ∂μ := by
    refine le_ciInf (fun u ↦ ?_)
    suffices LLR μ ν ≤ᵐ[μ] LLRu u by exact integral_mono_ae h_int (hu_int _) this
    filter_upwards [Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
      with a ha_pos ha_lt_top
    simp only [LLR]
    rw [← exp_le_exp, exp_log, exp_log]
    · rw [le_add_iff_nonneg_right]
      exact u.2.le
    · have hu_pos := u.2
      positivity
    · rw [ENNReal.toReal_pos_iff]
      simp [ha_pos, ha_lt_top]
  refine hu_le.trans ?_
  suffices ∀ u, 0 < u → ∫ x, LLRu u x ∂μ
      ≤ (⨆ (f : α → ℝ) (_ : Integrable f μ) (_ : Integrable (fun x ↦ exp (f x)) ν),
        ∫ x, f x ∂μ - Λ ν f + log (1 + u)) by
    sorry
  intro u hu
  suffices ∫ x, LLRu u x ∂μ = ∫ x, LLRu u x ∂μ - Λ ν (LLRu u) + log (1 + u) by
    rw [this]
    refine le_ciSup_of_le ?_ (LLRu u) ?_
    · refine ⟨∫ x, LLR μ ν x ∂μ + log (1 + u), ?_⟩
      rw [mem_upperBounds]
      intro x
      simp only [Set.mem_range, ge_iff_le, le_max_iff, forall_exists_index]
      rintro f rfl
      by_cases hfμ : Integrable f μ
      · simp only [hfμ, ciSup_unique]
        by_cases hf : Integrable (fun x ↦ exp (f x)) ν
        · simp only [hf, ciSup_unique]
          refine add_le_add ?_ le_rfl
          exact some_le hμν h_int f hfμ hf
        · simp only [hf, ciSup_empty]
          refine add_nonneg (integral_LLR_nonneg hμν h_int) ?_
          refine log_nonneg ?_
          simp only [le_add_iff_nonneg_right, hu.le]
      · simp only [hfμ, ciSup_empty]
        refine add_nonneg (integral_LLR_nonneg hμν h_int) ?_
        refine log_nonneg ?_
        simp only [le_add_iff_nonneg_right, hu.le]
    · simp only [hu_int u, hu_exp_int u hu, ciSup_unique]
      exact le_rfl
  suffices Λ ν (LLRu u) = log (1 + u) by
    rw [this]
    abel
  simp_rw [Λ, h_exp_log u hu]
  rw [integral_add integrable_toReal_rnDeriv (integrable_const _), integral_const]
  simp only [measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
  congr
  rw [integral_toReal_rnDeriv hμν]
  simp only [measure_univ, ENNReal.one_toReal]

-- todo: differs from the usual statement due to the `Integrable f μ` assumption
theorem DV' {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ ν x ∂μ
      = ⨆ (f : α → ℝ) (_ : Integrable f μ) (_ : Integrable (fun x ↦ exp (f x)) ν),
        ∫ x, f x ∂μ - Λ ν f :=
  le_antisymm (todo hμν h_int) (todo' hμν h_int)

end MeasureTheory
