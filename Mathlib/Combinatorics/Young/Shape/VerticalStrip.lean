/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Young.Shape.HorizontalStrip

/-!
# Vertical strips and the conjugation duality

A Lean 4 port of the first section of `theories/Combi/skewpart.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

A skew shape `η / μ` is a *vertical strip* when it has at most one box in each row, that is
`η_i ≤ μ_i + 1` for all `i`.  This is the transpose notion of the horizontal strips of
`Mathlib/Combinatorics/Young/Shape/HorizontalStrip.lean`, and the main results of this file
are the two conjugation dualities: the conjugate of a horizontal strip is a vertical strip and
conversely.

## Main definitions

* `Young.VertStrip η μ` : the skew shape `η / μ` is a vertical strip
  (Coq `vb_strip`).

## Main results

* `Young.vertStrip_iff_diffShape` : a vertical strip is a skew shape all of whose rows
  have at most one box (Coq `vb_strip_diffP`).
* `Young.HorizStrip.vertStrip_conjPart`, `Young.VertStrip.horizStrip_conjPart` :
  conjugation exchanges horizontal and vertical strips (Coq `hb_strip_conj`,
  `vb_strip_conj`), together with the equivalences `Young.vertStrip_conjPart_iff` and
  `Young.horizStrip_conjPart_iff` (Coq `vb_strip_conjE`, `hb_strip_conjE`).
-/

@[expose] public section

namespace Young

open List

/-- `VertStrip η μ` states that `μ` is contained in `η` and that the skew shape
`η / μ` is a vertical strip: it has at most one box in each row (Coq `vb_strip`). -/
def VertStrip (η μ : List ℕ) : Prop :=
  Included μ η ∧ ∀ i, η.getD i 0 ≤ μ.getD i 0 + 1

lemma VertStrip.included {η μ : List ℕ} (h : VertStrip η μ) : Included μ η := h.1

lemma VertStrip.getD_le_succ {η μ : List ℕ} (h : VertStrip η μ) (i : ℕ) :
    η.getD i 0 ≤ μ.getD i 0 + 1 := h.2 i

lemma VertStrip.getD_le {η μ : List ℕ} (h : VertStrip η μ) (i : ℕ) :
    μ.getD i 0 ≤ η.getD i 0 := h.1.getD_le i

lemma VertStrip.sum_le {η μ : List ℕ} (h : VertStrip η μ) : μ.sum ≤ η.sum :=
  h.1.sum_le

/-- Only the indices below the length of `η` matter in the definition of a vertical
strip; in particular the predicate is decidable. -/
lemma vertStrip_iff_range {η μ : List ℕ} :
    VertStrip η μ ↔ Included μ η ∧
      ∀ i ∈ Finset.range η.length, η.getD i 0 ≤ μ.getD i 0 + 1 := by
  refine ⟨fun h ↦ ⟨h.1, fun i _ ↦ h.2 i⟩, fun h ↦ ⟨h.1, fun i ↦ ?_⟩⟩
  by_cases hi : i < η.length
  · exact h.2 i (Finset.mem_range.2 hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

instance decidableVertStrip (η μ : List ℕ) : Decidable (VertStrip η μ) :=
  decidable_of_iff _ vertStrip_iff_range.symm

lemma vertStrip_self (μ : List ℕ) : VertStrip μ μ :=
  ⟨Included.refl μ, fun _ ↦ Nat.le_succ _⟩

/-- A vertical strip has at most one box in each row, so its size is bounded by the number
of rows of the outer shape. -/
lemma VertStrip.sum_le_sum_add_length {η μ : List ℕ} (h : VertStrip η μ) :
    η.sum ≤ μ.sum + η.length := by
  rw [sum_eq_sum_range_getD η le_rfl, sum_eq_sum_range_getD μ h.1.length_le]
  calc ∑ i ∈ Finset.range η.length, η.getD i 0
      ≤ ∑ i ∈ Finset.range η.length, (μ.getD i 0 + 1) :=
        Finset.sum_le_sum fun i _ ↦ h.2 i
    _ = (∑ i ∈ Finset.range η.length, μ.getD i 0) + η.length := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-- The usual definition of a vertical strip: a skew shape with at most one box in each
row (Coq `vb_strip_diffP`). -/
lemma vertStrip_iff_diffShape {η μ : List ℕ} :
    VertStrip η μ ↔ Included μ η ∧ ∀ x ∈ diffShape μ η, x ≤ 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x hx ↦ ?_⟩
    obtain ⟨i, hi, rfl⟩ := getElem_of_mem hx
    rw [← List.getD_eq_getElem _ _ hi, getD_diffShape]
    have := h2 i
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i ↦ ?_⟩
    rcases Nat.lt_or_ge i (diffShape μ η).length with hi | hi
    · have hle : (diffShape μ η).getD i 0 ≤ 1 := by
        rw [List.getD_eq_getElem _ _ hi]
        exact h2 _ (getElem_mem hi)
      rw [getD_diffShape] at hle
      have := h1.getD_le i
      omega
    · rw [length_diffShape] at hi
      rw [List.getD_eq_default _ _ hi]
      omega

/-! ### The conjugation duality -/

/-- Coq `hb_strip_conj`: the conjugate of a horizontal strip is a vertical strip. -/
lemma HorizStrip.vertStrip_conjPart {η μ : List ℕ} (hη : IsPart η) (hμ : IsPart μ)
    (h : HorizStrip η μ) : VertStrip (conjPart η) (conjPart μ) := by
  refine ⟨included_conjPart hμ hη h.included, fun i ↦ ?_⟩
  set a := (conjPart μ).getD i 0
  have h1 : μ.getD a 0 ≤ i := (getD_le_conjPart_iff hμ a i).2 (le_refl _)
  have h2 : η.getD (a + 1) 0 ≤ i := le_trans (h.getD_succ_le a) h1
  exact (getD_le_conjPart_iff hη (a + 1) i).1 h2

/-- Coq `vb_strip_conj`: the conjugate of a vertical strip is a horizontal strip. -/
lemma VertStrip.horizStrip_conjPart {η μ : List ℕ} (hη : IsPart η) (hμ : IsPart μ)
    (h : VertStrip η μ) : HorizStrip (conjPart η) (conjPart μ) := by
  refine ⟨included_conjPart hμ hη h.included, fun i ↦ ?_⟩
  set b := (conjPart μ).getD i 0
  have h1 : μ.getD b 0 ≤ i := (getD_le_conjPart_iff hμ b i).2 (le_refl _)
  have h2 : η.getD b 0 ≤ i + 1 := le_trans (h.getD_le_succ b) (by omega)
  exact (getD_le_conjPart_iff hη b (i + 1)).1 h2

/-- Coq `vb_strip_conjE`: conjugation exchanges horizontal and vertical strips, that is
`η / μ` is a horizontal strip if and only if `η' / μ'` is a vertical strip. -/
lemma vertStrip_conjPart_iff {η μ : List ℕ} (hη : IsPart η) (hμ : IsPart μ) :
    VertStrip (conjPart η) (conjPart μ) ↔ HorizStrip η μ := by
  refine ⟨fun h ↦ ?_, HorizStrip.vertStrip_conjPart hη hμ⟩
  have := h.horizStrip_conjPart (isPart_conjPart hη) (isPart_conjPart hμ)
  rwa [conjPart_conjPart hη, conjPart_conjPart hμ] at this

/-- Coq `hb_strip_conjE`: conjugation exchanges vertical and horizontal strips, that is
`η / μ` is a vertical strip if and only if `η' / μ'` is a horizontal strip. -/
lemma horizStrip_conjPart_iff {η μ : List ℕ} (hη : IsPart η) (hμ : IsPart μ) :
    HorizStrip (conjPart η) (conjPart μ) ↔ VertStrip η μ := by
  refine ⟨fun h ↦ ?_, VertStrip.horizStrip_conjPart hη hμ⟩
  have := h.vertStrip_conjPart (isPart_conjPart hη) (isPart_conjPart hμ)
  rwa [conjPart_conjPart hη, conjPart_conjPart hμ] at this

end Young
