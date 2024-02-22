/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Data.Real.Sign
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ZetaFunctions.SillySumLemma
/-!
# Dirichlet series as Mellin transforms

Here we prove general results of the form "the Mellin transform of a power series in exp (-t) is
a Dirichlet series".
-/

open Filter Topology Asymptotics Real Set MeasureTheory
open Complex hiding abs_of_nonneg

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

section Gammaℝ

/-- Deligne's archimedean Gamma factor for a real infinite place, see
"Valeurs de fonctions L et periodes d'integrales" § 5.3. -/
noncomputable def Gammaℝ (s : ℂ) := π ^ (-s / 2) * Complex.Gamma (s / 2)

/-- Deligne's archimedean Gamma factor for a complex infinite place, see
"Valeurs de fonctions L et periodes d'integrales" § 5.3. (Some authors omit the factor of 2). -/
noncomputable def Gammaℂ (s : ℂ) := 2 * (2 * π) ^ (-s) * Complex.Gamma s

@[simp] lemma Gammaℝ_def (s : ℂ) : Gammaℝ s = π ^ (-s / 2) * Complex.Gamma (s / 2) := rfl

@[simp] lemma Gammaℂ_def (s : ℂ) : Gammaℂ s = 2 * (2 * π) ^ (-s) * Complex.Gamma s := rfl

lemma Gammaℝ_add_two {s : ℂ} (hs : s ≠ 0) : Gammaℝ (s + 2) = Gammaℝ s * s / 2 / π := by
  rw [Gammaℝ, neg_div, add_div, neg_add, div_self two_ne_zero,
    Complex.Gamma_add_one _ (div_ne_zero hs two_ne_zero),
    cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero), cpow_neg_one, Gammaℝ]
  field_simp [pi_ne_zero]
  ring

lemma Gammaℂ_add_one {s : ℂ} (hs : s ≠ 0) : Gammaℂ (s + 1) = Gammaℂ s * s / 2 / π := by
  rw [Gammaℂ, Complex.Gamma_add_one _ hs, neg_add, cpow_add _ _ (mul_ne_zero two_ne_zero
    (ofReal_ne_zero.mpr pi_ne_zero)), cpow_neg_one]
  field_simp [pi_ne_zero]
  ring

/-- Reformulation of the doubling formula (expressing compatibility of Deligne's Gamma factors
with base extensions at `∞`). -/
lemma Gammaℝ_mul_Gammaℝ_add_one (s : ℂ) : Gammaℝ s * Gammaℝ (s + 1) = Gammaℂ s := by
  simp only [Gammaℝ_def, Gammaℂ_def]
  calc
  _ = (π ^ (-s / 2) * π ^ (-(s + 1) / 2)) * (Gamma (s / 2) * Gamma (s / 2 + 1 / 2)) := by ring_nf
  _ = 2 ^ (1 - s) * (π ^ (-1 / 2 - s) * π ^ (1 / 2 : ℂ)) * Gamma s := by
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero), Complex.Gamma_mul_Gamma_add_half,
      sqrt_eq_rpow, ofReal_cpow pi_pos.le, ofReal_div, ofReal_one, ofReal_ofNat]
    ring_nf
  _ = 2 * ((2 : ℝ) ^ (-s) * π ^ (-s)) * Gamma s := by
    rw [sub_eq_add_neg, cpow_add _ _ two_ne_zero, cpow_one,
      ← cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero), ofReal_ofNat]
    ring_nf
  _ = 2 * (2 * π) ^ (-s) * Gamma s := by
    rw [← mul_cpow_ofReal_nonneg two_pos.le pi_pos.le, ofReal_ofNat]

/-- Reformulation of the reflection formula (expressing compatibility of Deligne Gamma factors
with Tate duality). -/
lemma Gammaℝ_one_sub_mul_Gammaℝ_one_add (s : ℂ) :
    Gammaℝ (1 - s) * Gammaℝ (1 + s) = (cos (π * s / 2))⁻¹ :=
  calc Gammaℝ (1 - s) * Gammaℝ (1 + s)
  _ = (π ^ ((s - 1) / 2) * π ^ ((-1 - s) / 2)) *
        (Gamma ((1 - s) / 2) * Gamma (1 - (1 - s) / 2)) := by
    simp only [Gammaℝ_def]
    ring_nf
  _ = (π ^ ((s - 1) / 2) * π ^ ((-1 - s) / 2) * π ^ (1 : ℂ)) / sin (π / 2 - π * s / 2) := by
    rw [Complex.Gamma_mul_Gamma_one_sub, cpow_one]
    ring_nf
  _ = _ := by
    simp_rw [← Complex.cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero),
      Complex.sin_pi_div_two_sub]
    ring_nf
    rw [cpow_zero, one_mul]

lemma Gammaℝ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < re s) : Gammaℝ s ≠ 0 := by
  apply mul_ne_zero
  · simp [pi_ne_zero]
  · apply Complex.Gamma_ne_zero_of_re_pos
    rw [div_ofNat_re]
    exact div_pos hs two_pos

lemma Gammaℝ_eq_zero_iff {s : ℂ} : Gammaℝ s = 0 ↔ ∃ n : ℕ, s = -(2 * n) := by
  simp [pi_ne_zero, div_eq_iff (two_ne_zero' ℂ), mul_comm]

lemma Gammaℝ_one : Gammaℝ 1 = 1 := by
  rw [Gammaℝ_def, Complex.Gamma_one_half_eq]
  simp [neg_div, cpow_neg, inv_mul_cancel, pi_ne_zero]

lemma Gammaℂ_one : Gammaℂ 1 = 1 / π := by
  rw [Gammaℂ_def, cpow_neg_one, Complex.Gamma_one]
  field_simp [pi_ne_zero]

/-- Reflection formula for `Gammaℝ`. -/
lemma Gammaℝ_div_Gammaℝ_one_sub {s : ℂ} (hs : ∀ (n : ℕ), s ≠ -(2 * n + 1)) :
    Gammaℝ s / Gammaℝ (1 - s) = Gammaℂ s * cos (π * s / 2) := by
  have : Gammaℝ (s + 1) ≠ 0 := by
    simpa only [Ne.def, Gammaℝ_eq_zero_iff, not_exists, ← eq_sub_iff_add_eq,
      sub_eq_add_neg, ← neg_add]
  calc Gammaℝ s / Gammaℝ (1 - s)
  _ = (Gammaℝ s * Gammaℝ (s + 1)) / (Gammaℝ (1 - s) * Gammaℝ (1 + s)) := by
    rw [add_comm 1 s, mul_comm (Gammaℝ (1 - s)) (Gammaℝ (s + 1)), ← div_div,
      mul_div_cancel _ this]
  _ = (2 * (2 * π) ^ (-s) * Gamma s) / ((cos (π * s / 2))⁻¹) := by
    rw [Gammaℝ_one_sub_mul_Gammaℝ_one_add, Gammaℝ_mul_Gammaℝ_add_one, Gammaℂ_def]
  _ = _ := by rw [Gammaℂ_def, div_eq_mul_inv, inv_inv]

/-- Reformulation of reflection formula which is logically weaker, but easier to use in
functional equations for un-completed zeta functions. (Even version) -/
lemma inv_Gammaℝ_one_sub {s : ℂ} (hs : ∀ (n : ℕ), s ≠ -n) :
    (Gammaℝ (1 - s))⁻¹ = Gammaℂ s * cos (π * s / 2) * (Gammaℝ s)⁻¹ := by
  have h1 : Gammaℝ s ≠ 0 := by
    rw [Ne.def, Gammaℝ_eq_zero_iff, not_exists]
    intro n h
    specialize hs (2 * n)
    simp_all
  have h2 : ∀ (n : ℕ), s ≠ -(2 * ↑n + 1) := by
    intro n h
    specialize hs (2 * n + 1)
    simp_all
  rw [← Gammaℝ_div_Gammaℝ_one_sub h2, ← div_eq_mul_inv, div_right_comm, div_self h1, one_div]

/-- Reformulation of reflection formula which is logically weaker, but easier to use in
functional equations for un-completed zeta functions. (Odd version) -/
lemma inv_Gammaℝ_two_sub {s : ℂ} (hs : ∀ (n : ℕ), s ≠ -n) :
    (Gammaℝ (2 - s))⁻¹ = Gammaℂ s * Complex.sin (↑π * s / 2) * (Gammaℝ (s + 1))⁻¹ := by
  by_cases h : s = 1
  · rw [h, (by ring : 2 - 1 = (1 : ℂ)), Gammaℝ_one, Gammaℝ,
    neg_div, (by norm_num : (1 + 1) / 2 = (1 : ℂ)), Complex.Gamma_one, Gammaℂ_one,
    mul_one, Complex.sin_pi_div_two, mul_one, cpow_neg_one, mul_one, inv_inv,
    div_mul_cancel _ (ofReal_ne_zero.mpr pi_ne_zero), inv_one]
  rw [← Ne.def, ← sub_ne_zero] at h
  have h' (n : ℕ) : s - 1 ≠ -n := by
    cases' n with m
    · rwa [Nat.cast_zero, neg_zero]
    · rw [Ne.def, sub_eq_iff_eq_add]
      convert hs m using 2
      push_cast
      ring
  rw [(by ring : 2 - s = 1 - (s - 1)), inv_Gammaℝ_one_sub h',
    (by rw [sub_add_cancel] : Gammaℂ s = Gammaℂ (s - 1 + 1)), Gammaℂ_add_one h,
    (by ring : s + 1 = (s - 1) + 2), Gammaℝ_add_two h, mul_sub, sub_div, mul_one,
      Complex.cos_sub_pi_div_two]
  simp_rw [mul_div_assoc, mul_inv]
  generalize (Gammaℝ (s - 1))⁻¹ = A
  field_simp [pi_ne_zero]
  ring

lemma differentiable_Gammaℝ_inv : Differentiable ℂ (fun s ↦ (Gammaℝ s)⁻¹) := by
  conv => enter [2, s]; rw [Gammaℝ, mul_inv]
  refine Differentiable.mul (fun s ↦ .inv ?_ (by simp [pi_ne_zero])) ?_
  · refine ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow ?_)
    exact Or.inl (ofReal_ne_zero.mpr pi_ne_zero)
  · exact differentiable_one_div_Gamma.comp (differentiable_id.div_const _)

lemma Gammaℝ_residue_zero : Tendsto (fun s ↦ s * Gammaℝ s) (𝓝[≠] 0) (𝓝 2) := by
  have h : Tendsto (fun z : ℂ ↦ z / 2 * Gamma (z / 2)) (𝓝[≠] 0) (𝓝 1) := by
    refine tendsto_self_mul_Gamma_nhds_zero.comp ?_
    rw [tendsto_nhdsWithin_iff, (by simp : 𝓝 (0 : ℂ) = 𝓝 (0 / 2))]
    exact ⟨(tendsto_id.div_const _).mono_left nhdsWithin_le_nhds,
      eventually_of_mem self_mem_nhdsWithin fun x hx ↦ div_ne_zero hx two_ne_zero⟩
  have h' : Tendsto (fun s : ℂ ↦ 2 * (π : ℂ) ^ (-s / 2)) (𝓝[≠] 0) (𝓝 2) := by
    rw [(by simp : 𝓝 2 = 𝓝 (2 * (π : ℂ) ^ (-(0 : ℂ) / 2)))]
    refine Tendsto.mono_left (ContinuousAt.tendsto ?_) nhdsWithin_le_nhds
    exact continuousAt_const.mul ((continuousAt_const_cpow (ofReal_ne_zero.mpr pi_ne_zero)).comp
      (continuousAt_id.neg.div_const _))
  convert mul_one (2 : ℂ) ▸ (h'.mul h) using 2 with z
  rw [Gammaℝ]
  ring_nf

end Gammaℝ


lemma summable_int_iff_summable_nat {α : Type*}
    [AddCommGroup α] [UniformSpace α] [UniformAddGroup α] [CompleteSpace α] {f : ℤ → α} :
    Summable f ↔ (Summable fun (n : ℕ) => f ↑n) ∧ (Summable fun (n : ℕ) => f (-↑n)) := by
  refine ⟨fun p ↦ ⟨?_, ?_⟩, fun p ↦ summable_int_of_summable_nat p.1 p.2⟩ <;>
    apply p.comp_injective
  exacts [Nat.cast_injective, neg_injective.comp Nat.cast_injective]

lemma summable_one_div_nat_add_rpow (a : ℝ) (s : ℝ) :
    Summable (fun n : ℕ ↦ 1 / |n + a| ^ s) ↔ 1 < s := by
  suffices : ∀ (b c : ℝ),
      Summable (fun n : ℕ ↦ 1 / |n + b| ^ s) → Summable (fun n : ℕ ↦ 1 / |n + c| ^ s)
  · simp_rw [← summable_one_div_nat_rpow, Iff.intro (this a 0) (this 0 a), add_zero, Nat.abs_cast]
  refine fun b c h ↦ summable_of_isBigO_nat h (isBigO_of_div_tendsto_nhds ?_ 1 ?_)
  · filter_upwards [eventually_gt_atTop (Nat.ceil |b|)] with n hn hx
    have hna : 0 < n + b := by linarith [lt_of_abs_lt ((abs_neg b).symm ▸ Nat.lt_of_ceil_lt hn)]
    exfalso
    revert hx
    positivity
  · simp_rw [Pi.div_def, div_div, mul_one_div, one_div_div]
    refine (?_ : Tendsto (fun x : ℝ ↦ |x + b| ^ s / |x + c| ^ s) atTop (𝓝 1)).comp
      tendsto_nat_cast_atTop_atTop
    have : Tendsto (fun x : ℝ ↦ 1 + (b - c) / x) atTop (𝓝 1)
    · simpa using tendsto_const_nhds.add ((tendsto_const_nhds (X := ℝ)).div_atTop tendsto_id)
    have : Tendsto (fun x ↦ (x + b) / (x + c)) atTop (𝓝 1)
    · refine (this.comp (tendsto_id.atTop_add (tendsto_const_nhds (x := c)))).congr' ?_
      filter_upwards [eventually_gt_atTop (-c)] with x hx
      field_simp [(by linarith : 0 < x + c).ne']
    apply (one_rpow s ▸ (continuousAt_rpow_const _ s (by simp)).tendsto.comp this).congr'
    filter_upwards [eventually_gt_atTop (-b), eventually_gt_atTop (-c)] with x hb hc
    rw [neg_lt_iff_pos_add] at hb hc
    rw [Function.comp_apply, div_rpow hb.le hc.le, abs_of_pos hb, abs_of_pos hc]

lemma summable_one_div_int_add_rpow (a : ℝ) (s : ℝ) :
    Summable (fun n : ℤ ↦ 1 / |n + a| ^ s) ↔ 1 < s := by
  simp_rw [summable_int_iff_summable_nat, ← abs_neg (↑(-_ : ℤ) + a), neg_add, Int.cast_neg,
    neg_neg, Int.cast_ofNat, summable_one_div_nat_add_rpow, and_self]

variable {ι : Type*} [Countable ι]

/-- Most basic version of the "Mellin transform = Dirichlet series" argument. -/
lemma hasSum_mellin {a : ι → ℂ} {p : ι → ℝ} {F : ℝ → ℂ} {s : ℂ}
    (hp : ∀ i, a i = 0 ∨ 0 < p i) (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i ↦ a i * rexp (-p i * t)) (F t))
    (h_sum : Summable fun i ↦ ‖a i‖ / (p i) ^ s.re) :
    HasSum (fun i ↦ Gamma s * a i / p i ^ s) (mellin F s) := by
  simp_rw [mellin, smul_eq_mul, ← set_integral_congr measurableSet_Ioi
    (fun t ht ↦ congr_arg _ (hF t ht).tsum_eq), ← tsum_mul_left]
  convert hasSum_integral_of_summable_norm (μ := volume.restrict (Ioi 0))
    (F := fun i t ↦ t ^ (s - 1) * (a i * rexp (-p i * t))) (fun i ↦ ?_) ?_ using 2 with i
  · simp_rw [← mul_assoc, mul_comm _ (a _), mul_assoc (a _), mul_div_assoc, integral_mul_left]
    rcases hp i with hai | hpi
    · rw [hai, zero_mul, zero_mul]
    have := integral_cpow_mul_exp_neg_mul_Ioi hs hpi
    simp_rw [← ofReal_mul, ← ofReal_neg, ← ofReal_exp, ← neg_mul (p i)] at this
    rw [this, one_div, inv_cpow _ _ (arg_ofReal_of_nonneg hpi.le ▸ pi_pos.ne), div_eq_inv_mul]
  · -- integrability of terms
    rcases hp i with hai | hpi
    · simpa only [hai, zero_mul, mul_zero] using integrable_zero _ _ _
    simp_rw [← mul_assoc, mul_comm _ (a i), mul_assoc]
    have := Complex.GammaIntegral_convergent hs
    rw [← mul_zero (p i), ← integrableOn_Ioi_comp_mul_left_iff _ _ hpi] at this
    refine (IntegrableOn.congr_fun (this.const_mul (1 / p i ^ (s - 1)))
      (fun t (ht : 0 < t) ↦ ?_) measurableSet_Ioi).const_mul _
    simp_rw [mul_comm (↑(rexp _) : ℂ), ← mul_assoc, neg_mul, ofReal_mul]
    rw [mul_cpow_ofReal_nonneg hpi.le ht.le, ← mul_assoc, one_div, inv_mul_cancel, one_mul]
    · rw [Ne.def, cpow_eq_zero_iff, not_and_or]
      exact Or.inl (ofReal_ne_zero.mpr hpi.ne')
  · -- summability of integrals of norms
    apply Summable.of_norm
    convert h_sum.mul_left (Real.Gamma s.re) using 2 with i
    simp_rw [← mul_assoc, mul_comm _ (a i), mul_assoc, norm_mul (a i), integral_mul_left]
    rw [← mul_div_assoc, mul_comm (Real.Gamma _), mul_div_assoc, norm_mul ‖a i‖, norm_norm]
    rcases hp i with hai | hpi
    · simp only [hai, norm_zero, zero_mul]
    congr 1
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi hs hpi
    simp_rw [← neg_mul (p i), one_div, inv_rpow hpi.le, ← div_eq_inv_mul] at this
    rw [norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _)), ← this]
    refine set_integral_congr measurableSet_Ioi (fun t ht ↦ ?_)
    rw [norm_mul, norm_real, Real.norm_eq_abs, Real.abs_exp, Complex.norm_eq_abs,
      abs_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]

/-- Shortcut version for the commonly arising special case when `p i = π * q i` for some other
sequence `q`. -/
lemma hasSum_mellin_pi_mul {a : ι → ℂ} {q : ι → ℝ} {F : ℝ → ℂ} {s : ℂ}
    (hq : ∀ i, a i = 0 ∨ 0 < q i) (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i ↦ a i * rexp (-π * q i * t)) (F t))
    (h_sum : Summable fun i ↦ ‖a i‖ / (q i) ^ s.re) :
    HasSum (fun i ↦ π ^ (-s) * Gamma s * a i / q i ^ s) (mellin F s) := by
  have hp i : a i = 0 ∨ 0 < π * q i := by rcases hq i with h | h <;> simp [h, pi_pos]
  convert hasSum_mellin hp hs (by simpa using hF) ?_ using 2 with i
  · have : a i / ↑(π * q i) ^ s = π ^ (-s) * a i / q i ^ s := by
      rcases hq i with h | h
      · simp [h]
      · rw [ofReal_mul, mul_cpow_ofReal_nonneg pi_pos.le h.le, ← div_div, cpow_neg,
          ← div_eq_inv_mul]
    simp_rw [mul_div_assoc, this]
    ring_nf
  · have (i : ι) : ‖a i‖ / ↑(π * q i) ^ s.re = π ^ (-s.re) * ‖a i‖ / q i ^ s.re := by
      rcases hq i with h | h
      · simp [h]
      rw [mul_rpow pi_pos.le h.le, ← div_div, rpow_neg pi_pos.le, ← div_eq_inv_mul]
    simpa only [this, mul_div_assoc] using h_sum.mul_left _

/-- Version allowing some constant terms (which are omitted from the sums). -/
lemma hasSum_mellin_pi_mul₀ {a : ι → ℂ} {p : ι → ℝ} {F : ℝ → ℂ} {s : ℂ}
    (hp : ∀ i, 0 ≤ p i) (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i ↦ if p i = 0 then 0 else a i * rexp (-π * p i * t)) (F t))
    (h_sum : Summable fun i ↦ ‖a i‖ / (p i) ^ s.re) :
    HasSum (fun i ↦ π ^ (-s) * Gamma s * a i / p i ^ s) (mellin F s) := by
  have hs' : s ≠ 0 := fun h ↦ lt_irrefl _ (zero_re ▸ h ▸ hs)
  let a' i := if p i = 0 then 0 else a i
  have hp' i : a' i = 0 ∨ 0 < p i := by
    simp only [a']
    split_ifs with h <;> tauto
    exact Or.inr (lt_of_le_of_ne (hp i) (Ne.symm h))
  have (i t) : (if p i = 0 then 0 else a i * rexp (-π * p i * t)) =
    (a' i * rexp (-π * p i * t)) := by simp only [a', ite_mul, zero_mul]
  simp_rw [this] at hF
  convert hasSum_mellin_pi_mul hp' hs hF ?_ using 2 with i
  · rcases eq_or_ne (p i) 0 with h | h <;>
    simp [h, if_false, ofReal_zero, zero_cpow hs', div_zero]
  · refine h_sum.of_norm_bounded _ (fun i ↦ ?_)
    simp only
    split_ifs
    · simp only [norm_zero, zero_div]
      positivity
    · rw [norm_of_nonneg]
      have := hp i
      positivity

/-- Tailored version for even Jacobi theta functions. -/
lemma hasSum_mellin_pi_mul_sq {a : ι → ℂ} {r : ι → ℝ} {F : ℝ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i ↦ if r i = 0 then 0 else a i * rexp (-π * r i ^ 2 * t)) (F t))
    (h_sum : Summable fun i ↦ ‖a i‖ / |r i| ^ s.re) :
    HasSum (fun i ↦ Gammaℝ s * a i / |r i| ^ s) (mellin F (s / 2)) := by
  have hs' : 0 < (s / 2).re := by rw [div_ofNat_re]; positivity
  have h (i) : r i ^ 2 = 0 ↔ r i = 0 := by simp
  simp_rw [← h] at hF
  have hp i : 0 ≤ (r i) ^ 2 := sq_nonneg _
  convert hasSum_mellin_pi_mul₀ hp hs' hF ?_ using 3 with i
  · rw [← neg_div, Gammaℝ_def]
  · rw [← _root_.sq_abs, ofReal_pow, ← cpow_nat_mul']
    ring_nf
    all_goals rw [arg_ofReal_of_nonneg (abs_nonneg _)]; linarith [pi_pos]
  · convert h_sum using 3 with i
    rw [← _root_.sq_abs, ← rpow_natCast_mul (abs_nonneg _), div_ofNat_re, Nat.cast_ofNat,
      mul_div_cancel' _ two_pos.ne']

/-- Tailored version for odd Jacobi theta functions. -/
lemma hasSum_mellin_pi_mul_sq' {a : ι → ℂ} {r : ι → ℝ} {F : ℝ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i ↦ a i * r i * rexp (-π * r i ^ 2 * t)) (F t))
    (h_sum : Summable fun i ↦ ‖a i‖ / |r i| ^ s.re) :
    HasSum (fun i ↦ Gammaℝ (s + 1) * a i * Real.sign (r i) / |r i| ^ s)
    (mellin F ((s + 1) / 2)) := by
  have hs₁ : s ≠ 0 := fun h ↦ lt_irrefl _ (zero_re ▸ h ▸ hs)
  have hs₂ : 0 < (s + 1).re := by rw [add_re, one_re]; positivity
  have hs₃ : s + 1 ≠ 0 := fun h ↦ lt_irrefl _ (zero_re ▸ h ▸ hs₂)
  have (i t) : (a i * r i * rexp (-π * r i ^ 2 * t)) = if r i = 0 then 0 else
    (a i * r i * rexp (-π * r i ^ 2 * t)) := by split_ifs with h <;> simp [h]
  conv at hF => enter [t, ht, 1, i]; rw [this]
  convert hasSum_mellin_pi_mul_sq hs₂ hF ?_ using 2 with i
  · rcases eq_or_ne (r i) 0 with h | h
    · rw [h, abs_zero, ofReal_zero, zero_cpow hs₁, zero_cpow hs₃, div_zero, div_zero]
    · rw [cpow_add _ _ (ofReal_ne_zero.mpr <| abs_ne_zero.mpr h), cpow_one]
      conv_rhs => enter [1]; rw [← (r i).sign_mul_abs, ofReal_mul]
      field_simp [h]
      ring_nf
  · convert h_sum using 2 with i
    rcases eq_or_ne (r i) 0 with h | h
    · rw [h, abs_zero, ofReal_zero, zero_rpow hs₂.ne', zero_rpow hs.ne', div_zero, div_zero]
    · rw [add_re, one_re, rpow_add (abs_pos.mpr h), rpow_one, norm_mul, norm_real,
        Real.norm_eq_abs, ← div_div, div_right_comm, mul_div_cancel _ (abs_ne_zero.mpr h)]
