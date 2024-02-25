/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.Analysis.Fourier.Inversion

/-!
# Mellin inversion formula

We derive the Mellin inversion formula as a consequence of the Fourier inversion formula.

## Main results
- `mellin_inversion`: The inverse Mellin transform of the Mellin transform applied to `x > 0` is x.
-/

open Real Complex Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

-- TODO: move elsewhere
def VerticalIntegrable (f : ℂ → E) (σ : ℝ) (μ : Measure ℝ := by volume_tac) : Prop :=
  Integrable (fun (y : ℝ) ↦ f (σ + y * I)) μ

open scoped FourierTransform

private theorem drexp_neg : ∀ x ∈ univ, HasDerivWithinAt (rexp ∘ Neg.neg) (-rexp (-x)) univ x := by
  intro x _
  rw [← neg_one_mul, mul_comm]
  exact ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem rexp_neg_image : rexp ∘ Neg.neg '' univ = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

private theorem rexp_neg_injOn : univ.InjOn (rexp ∘ Neg.neg) :=
  (Real.exp_injective.injOn _).comp (neg_injective.injOn _) (univ.mapsTo_univ _)

private theorem rexp_cexp (x : ℝ) (s : ℂ) (f : E) :
    rexp (-x) • cexp (-↑x) ^ (s - 1) • f = cexp (-s * ↑x) • f := by
  show (rexp (-x) : ℂ) • _ = _ • f
  rw [← smul_assoc, smul_eq_mul]
  push_cast
  conv in cexp _ * _ => lhs; rw [← cpow_one (cexp _)]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _), cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by norm_num; exact pi_pos) (by simpa using pi_nonneg)]
  ring_nf

theorem mellin_eq_fourierIntegral (f : ℝ → E) {s : ℂ} :
    mellin f s = 𝓕 (fun (u : ℝ) ↦ (Real.exp (-s.re * u) • f (Real.exp (-u)))) (s.im / (2 * π)) := by
  calc
    _ = ∫ (u : ℝ), Complex.exp (-s * u) • f (Real.exp (-u)) := by
      rw [mellin, ← rexp_neg_image,
        integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ drexp_neg rexp_neg_injOn]
      simp [rexp_cexp]
    _ = ∫ (u : ℝ), Complex.exp (-s.im * u * I) • (Real.exp (-s.re * u) • f (Real.exp (-u))) := by
      congr
      ext
      conv => lhs; rw [← re_add_im s]
      rw [neg_add, add_mul, Complex.exp_add, mul_comm, ← smul_eq_mul, smul_assoc]
      norm_cast
      push_cast
      ring_nf
    _ = ∫ (u : ℝ), Complex.exp (↑(-2 * π * (u * (s.im / (2 * π)))) * I) •
        (Real.exp (-s.re * u) • f (Real.exp (-u))) := by
      congr
      ext u
      congr
      rw [mul_comm (-s.im : ℂ) (u : ℂ), mul_comm (-2 * π)]
      have : 2 * (π : ℂ) ≠ 0 := by norm_num; exact pi_ne_zero
      field_simp
    _ = _ := by
      simp [fourierIntegral_eq']

theorem mellin_inv_eq_fourierIntegral_inv (σ : ℝ) (f : ℂ → E) {x : ℝ} (hx : 0 < x) :
    mellin_inv σ f x =
    (x : ℂ) ^ (-σ : ℂ) • 𝓕⁻ (fun (y : ℝ) ↦ f (σ + 2 * π * y * I)) (-Real.log x) := by
  have hx0 : (x : ℂ) ≠ 0 := (ofReal_ne_zero.mpr (ne_of_gt hx))
  calc
    _ = (x : ℂ) ^ (-σ : ℂ) • (|(2 * π)⁻¹| •
        ∫ (y : ℝ), (x : ℂ) ^ (-y * I) • f (σ + y * I)) := by
      rw [mellin_inv, one_div, abs_of_pos (by norm_num; exact pi_pos)]
      simp_rw [neg_add, cpow_add _ _ hx0, mul_smul, integral_smul, neg_mul]
      exact smul_comm _ _ _
    _ = (x : ℂ) ^ (-σ : ℂ) •
        (∫ (y : ℝ), (x : ℂ) ^ (-2 * π * y * I) • f (σ + 2 * π * y * I)) := by
      rw [← Measure.integral_comp_mul_left]
      simp
    _ = (x : ℂ) ^ (-σ : ℂ) •
        (∫ (y : ℝ), Complex.exp (2 * π * (y * (-Real.log x)) * I) • f (σ + 2 * π * y * I)) := by
      congr
      ext
      rw [cpow_def_of_ne_zero hx0, Complex.ofReal_log hx.le]
      ring_nf
    _ = _ := by simp [fourierIntegralInv_eq']

variable [CompleteSpace E]

/-- The inverse Mellin transform of the Mellin transform applied to `x > 0` is x. -/
theorem mellin_inversion (σ : ℝ) (f : ℝ → E) {x : ℝ} (hx : 0 < x) (hf : MellinConvergent f σ)
    (hFf : VerticalIntegrable (mellin f) σ) (hfx : ContinuousAt f x) :
    mellin_inv σ (mellin f) x = f x := by
  let g := fun (u : ℝ) => Real.exp (-σ * u) • f (Real.exp (-u))
  replace hf : Integrable g := by
    rw [MellinConvergent, ← rexp_neg_image, integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ drexp_neg rexp_neg_injOn] at hf
    replace hf : Integrable fun (x : ℝ) ↦ cexp (-↑σ * ↑x) • f (rexp (-x)) := by
      simpa [rexp_cexp] using hf
    norm_cast at hf
  replace hFf : Integrable (𝓕 g) := by
    change Integrable (fun (y : ℝ) ↦ mellin f (σ + y * I)) volume at hFf
    have hp : 2 * π ≠ 0 := by norm_num; exact pi_ne_zero
    simpa [mellin_eq_fourierIntegral, mul_div_cancel _ hp] using hFf.comp_mul_right' hp
  replace hfx : ContinuousAt g (-Real.log x) := by
    refine ContinuousAt.smul (by fun_prop) (ContinuousAt.comp ?_ (by fun_prop))
    simpa [Real.exp_log hx] using hfx
  calc
    _ = mellin_inv σ (fun s ↦ 𝓕 g (s.im / (2 * π))) x := by
      simp [mellin_inv, mellin_eq_fourierIntegral]
    _ = (x : ℂ) ^ (-σ : ℂ) • g (-Real.log x) := by
      rw [mellin_inv_eq_fourierIntegral_inv _ _ hx, ← fourier_inversion hf hFf hfx]
      congr
      ext
      simp [mul_div_cancel_left _ (show 2 * π ≠ 0 by norm_num; exact pi_ne_zero)]
    _ = _ := by
      suffices (x : ℂ) ^ (-σ : ℂ) • rexp (σ * Real.log x) • f (rexp (Real.log x)) = f x by simpa
      norm_cast
      rw [mul_comm σ, ← rpow_def_of_pos hx, Real.exp_log hx, ← Complex.ofReal_cpow hx.le]
      norm_cast
      rw [← smul_assoc, smul_eq_mul, Real.rpow_neg hx.le,
        inv_mul_cancel (ne_of_gt (rpow_pos_of_pos hx σ)), one_smul]
