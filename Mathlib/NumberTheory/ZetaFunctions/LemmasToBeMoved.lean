/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Lemmas to be PR'ed separately
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

/-- `SignType.sign` respects strictly monotone zero-preserving maps. -/
lemma StrictMono.sign_comp {α β : Type*} [LinearOrder α] [Zero α]
    [Zero β] [Preorder β] [DecidableRel ((· < ·) : β → β → Prop)]
    {F: Type*} [FunLike F α β] [ZeroHomClass F α β] {f : F} (hf : StrictMono f) (a : α) :
    SignType.sign (f a) = SignType.sign a := by
  simp_rw [sign_apply, ← map_zero f, hf.lt_iff_lt]

/-- Casting out of `SignType` respects composition with functions preserving `0, 1, -1`. -/
lemma SignType.comp_cast' {α β : Type*} [One α] [One β] [Neg α] [Neg β] [Zero α] [Zero β]
    (f : α → β) (h₁ : f 1 = 1) (h₂ : f 0 = 0) (h₃ : f (-1) = -1) (s : SignType) :
    f s = s := by
  cases s <;> simp only [SignType.cast, h₁, h₂, h₃]

/-- Casting out of `SignType` respects composition with suitable bundled homomorphism types. -/
lemma SignType.comp_cast {α β : Type*} {F: Type*} (f : F) (s : SignType) [FunLike F α β] [One β]
    [AddGroupWithOne α] [SubtractionMonoid β] [AddMonoidHomClass F α β] [OneHomClass F α β] :
    f s = s :=
  SignType.comp_cast' _ (by simp) (by simp) (by simp) s

lemma SignType.coe_neg {α : Type*} [One α] [SubtractionMonoid α] (s : SignType) :
    (↑(-s) : α) = -↑s := by
  cases s <;> simp

-- /-- The cast from `SignType` to any ring factors through `Int`. Useful to avoid duplicating
-- API. -/
-- lemma sign_eq_cast_int (α : Type*) [NonAssocRing α] (s : SignType) :
--     (s : α) = ((s : ℤ) : α) := by
--   simp only [← SignType.comp_cast (Int.castRingHom α), eq_intCast]

-- lemma Complex.ofReal_sign (x : SignType) : ((x : ℝ) : ℂ) = (x : ℂ) := by
--   simp only [← SignType.comp_cast ofReal, ofReal_eq_coe]

end sign
-- section PR10883

-- namespace Real

-- @[simp]
-- lemma sign_eq_cast_sign (x : ℝ) : sign x = ↑(SignType.sign x) := by
--   rcases lt_trichotomy x 0 with h | h | h <;>
--   simp [h, sign_of_pos, sign_of_neg]

-- lemma sign_mul_abs (x : ℝ) : sign x * |x| = x := by
--   rw [sign_eq_cast_sign, _root_.sign_mul_abs]

-- end Real

-- end PR10883

section tsum_stuff

open Real Asymptotics Topology Filter

lemma Int.negSucc_injective : Function.Injective Int.negSucc := fun _ _  h ↦ Int.negSucc_inj.mp h

open Finset BigOperators in
/-- Variant of `HasSum.sum_nat_of_sum_int` directly using the two constructors of `ℤ`. Note
we do not need `[ContinuousAdd α]` for this. -/
theorem HasSum.sum_nat_of_sum_int' {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {a : α} {f : ℤ → α} (hf : HasSum f a) :
    HasSum (fun n : ℕ ↦ f n + f (Int.negSucc n)) a := by
  refine hf.hasSum_of_sum_eq fun u ↦ ?_
  refine ⟨u.preimage _ (Nat.cast_injective.injOn _) ∪ u.preimage _ (Int.negSucc_injective.injOn _),
      fun v' hv' ↦ ⟨v'.image (↑) ∪ v'.image Int.negSucc, fun x hx ↦ ?_, ?_⟩⟩
  · simp only [mem_union, mem_image]
    cases' x with y y
    · exact Or.inl ⟨y, hv' (by simpa only [mem_union, mem_preimage] using Or.inl hx), rfl⟩
    · exact Or.inr ⟨y, hv' (by simpa only [mem_union, mem_preimage] using Or.inr hx), rfl⟩
  · simp [sum_image (Nat.cast_injective.injOn _), sum_image (Int.negSucc_injective.injOn _),
      sum_add_distrib, sum_union, disjoint_iff_ne]

lemma summable_int_iff_summable_nat {α : Type*}
    [AddCommGroup α] [UniformSpace α] [UniformAddGroup α] [CompleteSpace α] {f : ℤ → α} :
    Summable f ↔ (Summable fun (n : ℕ) => f ↑n) ∧ (Summable fun (n : ℕ) => f (-↑n)) := by
  refine ⟨fun p ↦ ⟨?_, ?_⟩, fun p ↦ summable_int_of_summable_nat p.1 p.2⟩ <;>
    apply p.comp_injective
  exacts [Nat.cast_injective, neg_injective.comp Nat.cast_injective]

lemma Real.summable_pow_mul_exp_neg_nat_mul (k : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable fun n : ℕ ↦ n ^ k * Real.exp (-r * n) := by
  simp_rw [mul_comm (-r), Real.exp_nat_mul]
  apply summable_pow_mul_geometric_of_norm_lt_one
  rwa [norm_of_nonneg (exp_nonneg _), exp_lt_one_iff, neg_lt_zero]

lemma summable_one_div_nat_add_rpow (a : ℝ) (s : ℝ) :
    Summable (fun n : ℕ ↦ 1 / |n + a| ^ s) ↔ 1 < s := by
  suffices ∀ (b c : ℝ), Summable (fun n : ℕ ↦ 1 / |n + b| ^ s) →
      Summable (fun n : ℕ ↦ 1 / |n + c| ^ s) by
    simp_rw [← summable_one_div_nat_rpow, Iff.intro (this a 0) (this 0 a), add_zero, Nat.abs_cast]
  refine fun b c h ↦ summable_of_isBigO_nat h (isBigO_of_div_tendsto_nhds ?_ 1 ?_)
  · filter_upwards [eventually_gt_atTop (Nat.ceil |b|)] with n hn hx
    have hna : 0 < n + b := by linarith [lt_of_abs_lt ((abs_neg b).symm ▸ Nat.lt_of_ceil_lt hn)]
    exfalso
    revert hx
    positivity
  · simp_rw [Pi.div_def, div_div, mul_one_div, one_div_div]
    refine (?_ : Tendsto (fun x : ℝ ↦ |x + b| ^ s / |x + c| ^ s) atTop (𝓝 1)).comp
      tendsto_nat_cast_atTop_atTop
    have : Tendsto (fun x : ℝ ↦ 1 + (b - c) / x) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add ((tendsto_const_nhds (X := ℝ)).div_atTop tendsto_id)
    have : Tendsto (fun x ↦ (x + b) / (x + c)) atTop (𝓝 1) := by
      refine (this.comp (tendsto_id.atTop_add (tendsto_const_nhds (x := c)))).congr' ?_
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

end tsum_stuff

section CLM_norm

@[to_additive]
lemma Nontrivial.exists_ne_one (α : Type*) [One α] [Nontrivial α] :
    ∃ x : α, x ≠ 1 := by
  obtain ⟨x, y, h⟩ : ∃ (x y : α), x ≠ y := Nontrivial.exists_pair_ne
  rcases eq_or_ne y 1 with rfl | h
  · exact ⟨x, h⟩
  · exact ⟨y, h⟩

/-- The operator norm of the first projection `E × F → E` is at most 1. (It is 0 if `E` is zero, so
the inequality cannot be improved without further assumptions.) -/
lemma ContinuousLinearMap.norm_fst_le
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (E F : Type*)
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    ‖ContinuousLinearMap.fst 𝕜 E F‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun ⟨e, f⟩ ↦ ?_)
  simpa only [one_mul] using le_max_left ‖e‖ ‖f‖

/-- The operator norm of the first projection `E × F → E` is exactly 1 if `E` is nontrivial. -/
lemma ContinuousLinearMap.norm_fst_eq
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (E F : Type*) [Nontrivial E]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    ‖ContinuousLinearMap.fst 𝕜 E F‖ = 1 := by
  refine le_antisymm (ContinuousLinearMap.norm_fst_le E F) ?_
  obtain ⟨e, he⟩ := Nontrivial.exists_ne_zero E
  have : ‖e‖ ≤ _ * max ‖e‖ ‖0‖ := (ContinuousLinearMap.fst 𝕜 E F).le_opNorm (e, 0)
  rw [norm_zero, max_eq_left (norm_nonneg e)] at this
  rwa [← mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr he), one_mul]

/-- The operator norm of the second projection `E × F → F` is exactly 1 if `F` is nontrivial. -/
lemma ContinuousLinearMap.norm_snd_le
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (E F : Type*)
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    ‖ContinuousLinearMap.snd 𝕜 E F‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun ⟨e, f⟩ ↦ ?_)
  simpa only [one_mul] using le_max_right ‖e‖ ‖f‖

/-- The operator norm of the second projection `E × F → F` is exactly 1 if `F` is nontrivial. -/
lemma ContinuousLinearMap.norm_snd_eq
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (E F : Type*) [Nontrivial F]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
    ‖ContinuousLinearMap.snd 𝕜 E F‖ = 1 := by
  refine le_antisymm (ContinuousLinearMap.norm_snd_le E F) ?_
  obtain ⟨f, hf⟩ := Nontrivial.exists_ne_zero F
  have : ‖f‖ ≤ _ * max ‖0‖ ‖f‖ := (ContinuousLinearMap.snd 𝕜 E F).le_opNorm (0, f)
  rw [norm_zero, max_eq_right (norm_nonneg f)] at this
  rwa [← mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hf), one_mul]

end CLM_norm

section Gammaℝ

open Filter Topology Asymptotics Real Set MeasureTheory
open Complex hiding abs_of_nonneg

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
