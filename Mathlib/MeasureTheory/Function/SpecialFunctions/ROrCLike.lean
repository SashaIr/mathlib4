/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.ROrCLike.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

#align_import measure_theory.function.special_functions.is_R_or_C from "leanprover-community/mathlib"@"83a66c8775fa14ee5180c85cab98e970956401ad"

/-!
# Measurability of the basic `ROrCLike` functions

-/


noncomputable section

open NNReal ENNReal

namespace ROrCLike

variable {𝕜 : Type*} [ROrCLike 𝕜]

@[measurability]
theorem measurable_re : Measurable (re : 𝕜 → ℝ) :=
  continuous_re.measurable
#align is_R_or_C.measurable_re ROrCLike.measurable_re

@[measurability]
theorem measurable_im : Measurable (im : 𝕜 → ℝ) :=
  continuous_im.measurable
#align is_R_or_C.measurable_im ROrCLike.measurable_im

end ROrCLike

section ROrCLikeComposition

variable {α 𝕜 : Type*} [ROrCLike 𝕜] {m : MeasurableSpace α} {f : α → 𝕜} {μ : MeasureTheory.Measure α}

@[measurability]
theorem Measurable.re (hf : Measurable f) : Measurable fun x => ROrCLike.re (f x) :=
  ROrCLike.measurable_re.comp hf
#align measurable.re Measurable.re

@[measurability]
theorem AEMeasurable.re (hf : AEMeasurable f μ) : AEMeasurable (fun x => ROrCLike.re (f x)) μ :=
  ROrCLike.measurable_re.comp_aemeasurable hf
#align ae_measurable.re AEMeasurable.re

@[measurability]
theorem Measurable.im (hf : Measurable f) : Measurable fun x => ROrCLike.im (f x) :=
  ROrCLike.measurable_im.comp hf
#align measurable.im Measurable.im

@[measurability]
theorem AEMeasurable.im (hf : AEMeasurable f μ) : AEMeasurable (fun x => ROrCLike.im (f x)) μ :=
  ROrCLike.measurable_im.comp_aemeasurable hf
#align ae_measurable.im AEMeasurable.im

end ROrCLikeComposition

section

variable {α 𝕜 : Type*} [ROrCLike 𝕜] [MeasurableSpace α] {f : α → 𝕜} {μ : MeasureTheory.Measure α}

@[measurability]
theorem ROrCLike.measurable_ofReal : Measurable ((↑) : ℝ → 𝕜) :=
  ROrCLike.continuous_ofReal.measurable
#align is_R_or_C.measurable_of_real ROrCLike.measurable_ofReal

theorem measurable_of_re_im (hre : Measurable fun x => ROrCLike.re (f x))
    (him : Measurable fun x => ROrCLike.im (f x)) : Measurable f := by
  convert Measurable.add (M := 𝕜) (ROrCLike.measurable_ofReal.comp hre)
      ((ROrCLike.measurable_ofReal.comp him).mul_const ROrCLike.I)
  exact (ROrCLike.re_add_im _).symm
#align measurable_of_re_im measurable_of_re_im

theorem aemeasurable_of_re_im (hre : AEMeasurable (fun x => ROrCLike.re (f x)) μ)
    (him : AEMeasurable (fun x => ROrCLike.im (f x)) μ) : AEMeasurable f μ := by
  convert AEMeasurable.add (M := 𝕜) (ROrCLike.measurable_ofReal.comp_aemeasurable hre)
      ((ROrCLike.measurable_ofReal.comp_aemeasurable him).mul_const ROrCLike.I)
  exact (ROrCLike.re_add_im _).symm
#align ae_measurable_of_re_im aemeasurable_of_re_im

end
