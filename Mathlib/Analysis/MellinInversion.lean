import Mathlib.Analysis.Fourier.Inversion

open Real Complex Set MeasureTheory

open scoped FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def mellin_eq_fourierIntegral_exp (f : ℝ → E) {s : ℂ} :
    mellin f s = 𝓕 (fun (u : ℝ) ↦ Real.exp (-s.re * u) • f (Real.exp (-u))) (s.im / (2 * π)) := by
  unfold mellin
  sorry

def mellin_inv_eq_fourierIntegral_inv_log (σ : ℝ) (f : ℂ → E) {x : ℝ} (hx : 0 < x):
  mellin_inv σ f x = -I • x ^ σ • 𝓕⁻ (fun (u : ℝ) ↦ f (σ + 2 * π * u * I)) (-Real.log x) := by
  have : (fun (y : ℝ) ↦ (x : ℂ) ^ (-(σ + y * I)) • f (σ + y * I)) =
      fun (u : ℝ) ↦ (x : ℂ) ^ (-(σ + y * I)) • f (σ + y * I) := by
    sorry
  show _ • ∫ (y : ℝ), (x : ℂ) ^ (-(σ + y * I)) • f (σ + y * I) = _
  stop
  suffices (I • ((↑π)⁻¹ * 2⁻¹ : ℂ)) • ∫ (y : ℝ), (x : ℂ) ^ (-↑σ - ↑y * I) • f (↑σ + ↑y * I) =
      I • x ^ σ • ∫ (v : ℝ), cexp (-(2 * π * (↑v * ↑(Real.log x)) * I)) • f (σ + 2 * ↑π * ↑v * I) by
    simpa [mellin_inv, fourierIntegralInv_eq']
  rw [smul_assoc]
  congr 1
  sorry

lemma foo {a b : ℂ} (ha : a ≠ 0) : a * b / a = b := by exact mul_div_cancel_left b ha

def mellin_inversion (σ : ℝ) (f : ℝ → E) {x : ℝ} (hx : 0 < x) : mellin_inv σ (mellin f) x = f x := by
  stop
  let g (u : ℝ) := rexp (-σ * u) • f (rexp (-u))
  calc
    _ = mellin_inv σ (fun s ↦ 𝓕 g (s.im / (2 * π))) x := by
      simp [mellin_inv, mellin_eq_fourierIntegral_exp]
    _ = -I • x ^ σ • g (-Real.log x) := by
      rw [mellin_inv_eq_fourierIntegral_inv_log, ← fourier_inversion (f := g)]
      congr
      ext u
      have : 2 * π ≠ 0 := sorry
      simp [mul_div_cancel_left _ this]
      stop
      sorry
    _ = _ := by
      simp
      sorry
  stop
  have : f x = (f ∘ Real.exp) (Real.log x) := sorry
  rw [mellin_inv_eq_fourierIntegral_inv_log, mellin_eq_fourierIntegral_exp, this,
    ← fourier_inversion (f := f ∘ Real.exp), Function.comp_apply]
  congr
  ext y
  have : 2 * π * I ≠ 0 := sorry
  simp [mul_div_cancel _ this, fourierIntegral_eq']
  sorry
  stop
  calc
    _ = (1 / (2 * π)) • ((2 * π) • 𝓕⁻ (𝓕 (f ∘ Complex.re ∘ Complex.exp)) (Complex.log x)) := sorry
    _ = _ := by
      rw [fourier_inversion]
      sorry
  stop
  conv in _ • f _ =>
    rw [Real.rpow_def_of_pos]
    rfl
  conv in (x : ℂ) ^ _ =>
    rw []
    rfl
  sorry
-- lemma fourierIntegral_eq' (f : V → E) (w : V) :
--     𝓕 f w = ∫ v, Complex.exp ((↑(-2 * π * ⟪v, w⟫) * Complex.I)) • f v := by
--   simp_rw [fourierIntegral_eq, Real.fourierChar_apply, mul_neg, neg_mul]

-- lemma fourierIntegralInv_eq (f : V → E) (w : V) :
--     𝓕⁻ f w = ∫ v, 𝐞[⟪v, w⟫] • f v := by
--   simp [fourierIntegralInv, VectorFourier.fourierIntegral]

-- lemma fourierIntegralInv_eq' (f : V → E) (w : V) :
--     𝓕⁻ f w = ∫ v, Complex.exp ((↑(2 * π * ⟪v, w⟫) * Complex.I)) • f v := by
--   simp_rw [fourierIntegralInv_eq, Real.fourierChar_apply]
