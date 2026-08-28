/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Young.Shape.HorizontalStrip

/-!
# Vertical strips and the conjugation duality

A Lean 4 port of the first section of `theories/Combi/skewpart.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

A skew shape `lam / mu` is a *vertical strip* when it has at most one box in each row, that is
`lam_i ≤ mu_i + 1` for all `i`.  This is the transpose notion of the horizontal strips of
`Mathlib/Combinatorics/Young/Shape/HorizontalStrip.lean`, and the main results of this file
are the two conjugation dualities: the conjugate of a horizontal strip is a vertical strip and
conversely.

## Main definitions

* `List.VertStrip lam mu` : the skew shape `lam / mu` is a vertical strip
  (Coq `vb_strip`).

## Main results

* `List.vertStrip_iff_diffShape` : a vertical strip is a skew shape all of whose rows
  have at most one box (Coq `vb_strip_diffP`).
* `List.HorizStrip.vertStrip_conjPart`, `List.VertStrip.horizStrip_conjPart` :
  conjugation exchanges horizontal and vertical strips (Coq `hb_strip_conj`,
  `vb_strip_conj`), together with the equivalences `List.vertStrip_conjPart_iff` and
  `List.horizStrip_conjPart_iff` (Coq `vb_strip_conjE`, `hb_strip_conjE`).
-/

namespace List

open List

/-- `VertStrip lam mu` states that `mu` is contained in `lam` and that the skew shape
`lam / mu` is a vertical strip: it has at most one box in each row (Coq `vb_strip`). -/
def VertStrip (lam mu : List ℕ) : Prop :=
  Included mu lam ∧ ∀ i, lam.getD i 0 ≤ mu.getD i 0 + 1

lemma VertStrip.included {lam mu : List ℕ} (h : VertStrip lam mu) : Included mu lam := h.1

lemma VertStrip.getD_le_succ {lam mu : List ℕ} (h : VertStrip lam mu) (i : ℕ) :
    lam.getD i 0 ≤ mu.getD i 0 + 1 := h.2 i

lemma VertStrip.getD_le {lam mu : List ℕ} (h : VertStrip lam mu) (i : ℕ) :
    mu.getD i 0 ≤ lam.getD i 0 := h.1.getD_le i

lemma VertStrip.sum_le {lam mu : List ℕ} (h : VertStrip lam mu) : mu.sum ≤ lam.sum :=
  h.1.sum_le

/-- Only the indices below the length of `lam` matter in the definition of a vertical
strip; in particular the predicate is decidable. -/
lemma vertStrip_iff_range {lam mu : List ℕ} :
    VertStrip lam mu ↔ Included mu lam ∧
      ∀ i ∈ Finset.range lam.length, lam.getD i 0 ≤ mu.getD i 0 + 1 := by
  refine ⟨fun h ↦ ⟨h.1, fun i _ ↦ h.2 i⟩, fun h ↦ ⟨h.1, fun i ↦ ?_⟩⟩
  by_cases hi : i < lam.length
  · exact h.2 i (Finset.mem_range.2 hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

instance decidableVertStrip (lam mu : List ℕ) : Decidable (VertStrip lam mu) :=
  decidable_of_iff _ vertStrip_iff_range.symm

lemma vertStrip_self (sh : List ℕ) : VertStrip sh sh :=
  ⟨Included.refl sh, fun _ ↦ Nat.le_succ _⟩

/-- A vertical strip has at most one box in each row, so its size is bounded by the number
of rows of the outer shape. -/
lemma VertStrip.sum_le_sum_add_length {lam mu : List ℕ} (h : VertStrip lam mu) :
    lam.sum ≤ mu.sum + lam.length := by
  rw [sum_eq_sum_range_getD lam le_rfl, sum_eq_sum_range_getD mu h.1.length_le]
  calc ∑ i ∈ Finset.range lam.length, lam.getD i 0
      ≤ ∑ i ∈ Finset.range lam.length, (mu.getD i 0 + 1) :=
        Finset.sum_le_sum fun i _ ↦ h.2 i
    _ = (∑ i ∈ Finset.range lam.length, mu.getD i 0) + lam.length := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-- The usual definition of a vertical strip: a skew shape with at most one box in each
row (Coq `vb_strip_diffP`). -/
lemma vertStrip_iff_diffShape {lam mu : List ℕ} :
    VertStrip lam mu ↔ Included mu lam ∧ ∀ x ∈ diffShape mu lam, x ≤ 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x hx ↦ ?_⟩
    obtain ⟨i, hi, rfl⟩ := getElem_of_mem hx
    rw [← List.getD_eq_getElem _ _ hi, getD_diffShape]
    have := h2 i
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i ↦ ?_⟩
    rcases Nat.lt_or_ge i (diffShape mu lam).length with hi | hi
    · have hle : (diffShape mu lam).getD i 0 ≤ 1 := by
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
lemma HorizStrip.vertStrip_conjPart {lam mu : List ℕ} (hlam : IsPart lam) (hmu : IsPart mu)
    (h : HorizStrip lam mu) : VertStrip (conjPart lam) (conjPart mu) := by
  refine ⟨included_conjPart hmu hlam h.included, fun i ↦ ?_⟩
  set a := (conjPart mu).getD i 0
  have h1 : mu.getD a 0 ≤ i := (getD_le_conjPart_iff hmu a i).2 (le_refl _)
  have h2 : lam.getD (a + 1) 0 ≤ i := le_trans (h.getD_succ_le a) h1
  exact (getD_le_conjPart_iff hlam (a + 1) i).1 h2

/-- Coq `vb_strip_conj`: the conjugate of a vertical strip is a horizontal strip. -/
lemma VertStrip.horizStrip_conjPart {lam mu : List ℕ} (hlam : IsPart lam) (hmu : IsPart mu)
    (h : VertStrip lam mu) : HorizStrip (conjPart lam) (conjPart mu) := by
  refine ⟨included_conjPart hmu hlam h.included, fun i ↦ ?_⟩
  set b := (conjPart mu).getD i 0
  have h1 : mu.getD b 0 ≤ i := (getD_le_conjPart_iff hmu b i).2 (le_refl _)
  have h2 : lam.getD b 0 ≤ i + 1 := le_trans (h.getD_le_succ b) (by omega)
  exact (getD_le_conjPart_iff hlam b (i + 1)).1 h2

/-- Coq `vb_strip_conjE`: conjugation exchanges horizontal and vertical strips, that is
`lam / mu` is a horizontal strip if and only if `lam' / mu'` is a vertical strip. -/
lemma vertStrip_conjPart_iff {lam mu : List ℕ} (hlam : IsPart lam) (hmu : IsPart mu) :
    VertStrip (conjPart lam) (conjPart mu) ↔ HorizStrip lam mu := by
  refine ⟨fun h ↦ ?_, HorizStrip.vertStrip_conjPart hlam hmu⟩
  have := h.horizStrip_conjPart (isPart_conjPart hlam) (isPart_conjPart hmu)
  rwa [conjPart_conjPart hlam, conjPart_conjPart hmu] at this

/-- Coq `hb_strip_conjE`: conjugation exchanges vertical and horizontal strips, that is
`lam / mu` is a vertical strip if and only if `lam' / mu'` is a horizontal strip. -/
lemma horizStrip_conjPart_iff {lam mu : List ℕ} (hlam : IsPart lam) (hmu : IsPart mu) :
    HorizStrip (conjPart lam) (conjPart mu) ↔ VertStrip lam mu := by
  refine ⟨fun h ↦ ?_, VertStrip.horizStrip_conjPart hlam hmu⟩
  have := h.vertStrip_conjPart (isPart_conjPart hlam) (isPart_conjPart hmu)
  rwa [conjPart_conjPart hlam, conjPart_conjPart hmu] at this

end List
