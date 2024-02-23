/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Data.Real.Sign

/-!
# Forward-port of PR #10614
-/

section PR10614

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]

lemma hasSum_integral_of_summable_norm {F : ι → α → E}
    (hF_int : ∀  i : ι, Integrable (F i) μ)
    (hF_sum' : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    HasSum (fun n ↦ ∫ (a : α), F n a ∂μ) (∫ (a : α), (∑' (i : ι), F i a) ∂μ) := by
  suffices ∑' (i : ι), ∫⁻ (a : α), ↑‖F i a‖₊ ∂μ ≠ ⊤ by
    rw [integral_tsum (fun i ↦ (hF_int i).aestronglyMeasurable) this]
    exact (hF_sum'.of_norm_bounded _ fun i ↦ norm_integral_le_integral_norm _).hasSum
  have (i : ι) : ∫⁻ (a : α), (‖F i a‖₊ : ENNReal) ∂μ = ↑‖(∫ a : α, ‖F i a‖ ∂μ)‖₊ := by
    rw [lintegral_coe_eq_integral _ (hF_int i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
        Real.norm_of_nonneg (integral_nonneg (fun a ↦ norm_nonneg (F i a)))]
    rfl
  rw [funext this, ← ENNReal.coe_tsum]
  · apply ENNReal.coe_ne_top
  · simp_rw [← NNReal.summable_coe, coe_nnnorm]
    exact hF_sum'.abs

end PR10614

section sign

lemma Real.sign_eq_cast_sign (x : ℝ) : sign x = SignType.sign x := by
  rcases lt_trichotomy x 0 with h | h | h <;>
  simp [h, sign_of_pos, sign_of_neg]

lemma Int.sign_eq_cast_sign (x : ℤ) : sign x = SignType.sign x := by
  rcases lt_trichotomy x 0 with h | h | h <;>
  simp [h, sign_eq_one_iff_pos, sign_eq_neg_one_iff_neg]

lemma Real.sign_mul_abs (x : ℝ) : sign x * |x| = x := by
  rw [sign_eq_cast_sign, _root_.sign_mul_abs]

end sign
