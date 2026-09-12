/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.GetD
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Combinatorics.Enumerative.Partition.List.Included
public import Mathlib.Combinatorics.Enumerative.Partition.List.TrimZeros

/-!
# Ribbon border strips

A Lean 4 port of the combinatorial definition of ribbons of `theories/Combi/skewpart.v`
from [Coq-Combi](https://github.com/math-comp/Coq-Combi).

A skew shape `outer / inner` is a *ribbon* (or border strip) occupying the rows
`start, …, stop` when the rows outside this interval are unchanged, the row `start` grows,
and each of the following rows of `outer`, up to the row `stop`, ends exactly one box to
the right of where the previous row of `inner` ended.  The *height* of a ribbon is the
number of rows it occupies.

## Main definitions

* `Young.RibbonOn start stop inner outer` : the skew shape `outer / inner` is a ribbon
  occupying the rows `start, …, stop` (Coq `ribbon_on`).
* `Young.ribbonHeight inner outer` : the number of nonempty rows of the skew shape
  `outer / inner` (Coq `ribbon_height`).

## Main results

* `Young.RibbonOn.start_le_stop`, `Young.RibbonOn.getD_lt`, `Young.RibbonOn.included` :
  the basic properties of a ribbon (Coq `ribbon_on_start_stop`, `ribbon_on_included`).
* `Young.RibbonOn.sum_add` : the number of boxes of a ribbon, in terms of its first row and
  of the row where it stops.
* `Young.RibbonOn.ribbonHeight_eq` : the height of a ribbon occupying the rows
  `start, …, stop` is `stop - start + 1` (Coq `ribbon_on_height`).
* `Young.RibbonOn.unique` : the rows occupied by a ribbon are determined by the skew shape
  (Coq `ribbon_on_inj`).
* `Young.exists_ribbonOn_nil_iff` : a partition is a ribbon over the empty shape exactly
  when it is a hook.
-/

@[expose] public section

namespace Young

open List

/-- `RibbonOn start stop inner outer` states that the skew shape `outer / inner` is a
ribbon occupying the rows `start, …, stop` (Coq `ribbon_on`). -/
def RibbonOn (start stop : ℕ) (inner outer : List ℕ) : Prop :=
  (∀ i, stop < i → outer.getD i 0 = inner.getD i 0) ∧
    (∀ i, start ≤ i → i < stop → outer.getD (i + 1) 0 = inner.getD i 0 + 1) ∧
      inner.getD start 0 < outer.getD start 0 ∧
        ∀ i, i < start → outer.getD i 0 = inner.getD i 0

/-- The height of the skew shape `outer / inner`: the number of its nonempty rows
(Coq `ribbon_height`). -/
def ribbonHeight (inner outer : List ℕ) : ℕ :=
  (diffShape inner outer).countP (fun x ↦ decide (0 < x))

lemma ribbonHeight_eq_card (inner outer : List ℕ) :
    ribbonHeight inner outer =
      ((Finset.range outer.length).filter
        (fun i ↦ inner.getD i 0 < outer.getD i 0)).card := by
  rw [ribbonHeight, countP_eq_card_filter_range, length_diffShape]
  refine congrArg Finset.card (Finset.filter_congr fun i _ ↦ ?_)
  rw [getD_diffShape, decide_eq_true_eq]
  omega

namespace RibbonOn

variable {start stop : ℕ} {inner outer : List ℕ}

lemma getD_eq_of_gt (h : RibbonOn start stop inner outer) {i : ℕ} (hi : stop < i) :
    outer.getD i 0 = inner.getD i 0 := h.1 i hi

lemma getD_succ (h : RibbonOn start stop inner outer) {i : ℕ} (h1 : start ≤ i) (h2 : i < stop) :
    outer.getD (i + 1) 0 = inner.getD i 0 + 1 := h.2.1 i h1 h2

lemma getD_start_lt (h : RibbonOn start stop inner outer) :
    inner.getD start 0 < outer.getD start 0 := h.2.2.1

lemma getD_eq_of_lt (h : RibbonOn start stop inner outer) {i : ℕ} (hi : i < start) :
    outer.getD i 0 = inner.getD i 0 := h.2.2.2 i hi

/-- Coq `ribbon_on_start_stop`: a ribbon starts before it stops. -/
lemma start_le_stop (h : RibbonOn start stop inner outer) : start ≤ stop := by
  by_contra hcon
  have := h.getD_eq_of_gt (i := start) (by omega)
  have := h.getD_start_lt
  omega

/-- The rows occupied by a ribbon are exactly those which grow. -/
lemma getD_lt (hinner : IsPart inner) (h : RibbonOn start stop inner outer) {i : ℕ}
    (h1 : start ≤ i) (h2 : i ≤ stop) : inner.getD i 0 < outer.getD i 0 := by
  rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
  · exact h.getD_start_lt
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hstep := h.getD_succ (i := j) (by omega) (by omega)
    have := hinner.getD_antitone (i := j) (j := j + 1) (by omega)
    omega

/-- Coq `ribbon_on_included`: a ribbon shape contains the inner shape. -/
lemma included (hinner : IsPart inner) (h : RibbonOn start stop inner outer) :
    Included inner outer := by
  refine hinner.included_iff_getD.2 fun i ↦ ?_
  rcases Nat.lt_or_ge i start with hi | hi
  · rw [h.getD_eq_of_lt hi]
  · rcases Nat.lt_or_ge stop i with hi' | hi'
    · rw [h.getD_eq_of_gt hi']
    · exact le_of_lt (getD_lt hinner h hi hi')

/-- The number of boxes of a ribbon: the size of the skew shape `outer / inner` is
`outer_start + (stop - start) - inner_stop`, written here without subtraction. -/
lemma sum_add (h : RibbonOn start stop inner outer) :
    inner.sum + (outer.getD start 0 + (stop - start))
      = outer.sum + inner.getD stop 0 := by
  classical
  have hs := h.start_le_stop
  set L := max outer.length inner.length + stop + 1 with hL
  have hsplit : ∀ f : ℕ → ℕ, ∑ i ∈ Finset.range L, f i
      = ((∑ i ∈ Finset.Ico 0 start, f i) + ∑ i ∈ Finset.Ico start (stop + 1), f i)
        + ∑ i ∈ Finset.Ico (stop + 1) L, f i := by
    intro f
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive f (Nat.zero_le (stop + 1)) (show stop + 1 ≤ L by omega),
      ← Finset.sum_Ico_consecutive f (Nat.zero_le start) (show start ≤ stop + 1 by omega)]
  have hin : inner.sum = ∑ i ∈ Finset.range L, inner.getD i 0 :=
    sum_eq_sum_range_getD _ (by omega)
  have hout : outer.sum = ∑ i ∈ Finset.range L, outer.getD i 0 :=
    sum_eq_sum_range_getD _ (by omega)
  have hbot : ∑ i ∈ Finset.Ico 0 start, outer.getD i 0
      = ∑ i ∈ Finset.Ico 0 start, inner.getD i 0 :=
    Finset.sum_congr rfl fun i hi => h.getD_eq_of_lt (Finset.mem_Ico.1 hi).2
  have htop : ∑ i ∈ Finset.Ico (stop + 1) L, outer.getD i 0
      = ∑ i ∈ Finset.Ico (stop + 1) L, inner.getD i 0 :=
    Finset.sum_congr rfl fun i hi => h.getD_eq_of_gt (by have := (Finset.mem_Ico.1 hi).1; omega)
  have hmidin : ∑ i ∈ Finset.Ico start (stop + 1), inner.getD i 0
      = (∑ i ∈ Finset.Ico start stop, inner.getD i 0) + inner.getD stop 0 := by
    rw [Finset.sum_Ico_succ_top hs]
  have hmidout : ∑ i ∈ Finset.Ico start (stop + 1), outer.getD i 0
      = outer.getD start 0
        + ((∑ i ∈ Finset.Ico start stop, inner.getD i 0) + (stop - start)) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ j ∈ Finset.range (stop + 1 - (start + 1)),
        outer.getD (start + 1 + j) 0 = inner.getD (start + j) 0 + 1 := by
      intro j hj
      have hj' : j < stop - start := by
        have := Finset.mem_range.1 hj
        omega
      have := h.getD_succ (i := start + j) (by omega) (by omega)
      rw [show start + 1 + j = start + j + 1 by omega, this]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const,
      smul_eq_mul, mul_one, Finset.card_range,
      show stop + 1 - (start + 1) = stop - start from by omega]
  rw [hin, hout, hsplit (fun i => inner.getD i 0), hsplit (fun i => outer.getD i 0),
    hbot, htop, hmidin, hmidout]
  omega

/-- Coq `ribbon_on_height`: the height of a ribbon occupying the rows `start, …, stop` is
`stop - start + 1`. -/
lemma ribbonHeight_eq (hinner : IsPart inner) (h : RibbonOn start stop inner outer) :
    ribbonHeight inner outer = stop - start + 1 := by
  have hle := h.start_le_stop
  have hmem : ∀ i, (i ∈ (Finset.range outer.length).filter
      (fun i ↦ inner.getD i 0 < outer.getD i 0)) ↔ i ∈ Finset.Icc start stop := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨-, hlt⟩
      by_contra hcon
      rcases Nat.lt_or_ge i start with hi | hi
      · rw [h.getD_eq_of_lt hi] at hlt; omega
      · have hi' : stop < i := by omega
        rw [h.getD_eq_of_gt hi'] at hlt; omega
    · rintro ⟨h1, h2⟩
      have hlt := getD_lt hinner h h1 h2
      refine ⟨?_, hlt⟩
      by_contra hcon
      rw [List.getD_eq_default outer 0 (show outer.length ≤ i by omega)] at hlt
      omega
  rw [ribbonHeight_eq_card, Finset.filter_congr_decidable, Finset.ext hmem, Nat.card_Icc]
  omega

/-- Coq `ribbon_on_inj`: the rows occupied by a ribbon are determined by the skew shape. -/
lemma unique (hinner : IsPart inner) {s' t' : ℕ} (h : RibbonOn start stop inner outer)
    (h' : RibbonOn s' t' inner outer) : start = s' ∧ stop = t' := by
  have key : ∀ (a b : ℕ), RibbonOn a b inner outer → ∀ i,
      (a ≤ i ∧ i ≤ b) ↔ inner.getD i 0 < outer.getD i 0 := by
    intro a b hab i
    refine ⟨fun hi ↦ getD_lt hinner hab hi.1 hi.2, fun hlt ↦ ?_⟩
    by_contra hcon
    rcases Nat.lt_or_ge i a with hi | hi
    · rw [hab.getD_eq_of_lt hi] at hlt; omega
    · have hi' : b < i := by omega
      rw [hab.getD_eq_of_gt hi'] at hlt; omega
  have h1 := key start stop h
  have h2 := key s' t' h'
  have hs := h.start_le_stop
  have hs' := h'.start_le_stop
  constructor
  · have ha := (h2 start).2 ((h1 start).1 ⟨le_refl _, hs⟩)
    have hb := (h1 s').2 ((h2 s').1 ⟨le_refl _, hs'⟩)
    omega
  · have ha := (h2 stop).2 ((h1 stop).1 ⟨hs, le_refl _⟩)
    have hb := (h1 t').2 ((h2 t').1 ⟨hs', le_refl _⟩)
    omega

end RibbonOn

/-! ### Ribbons over the empty shape -/

/-- The height of a partition seen as a skew shape over the empty shape is its number of
rows. -/
lemma ribbonHeight_nil {μ : List ℕ} (hμ : IsPart μ) : ribbonHeight [] μ = μ.length := by
  rw [ribbonHeight, diffShape_nil]
  exact List.countP_eq_length.2 fun a ha => by simpa using hμ.pos_of_mem ha

/-- A partition is a ribbon over the empty shape exactly when it is a *hook*, that is when
its second row has at most one box. -/
lemma exists_ribbonOn_nil_iff {μ : List ℕ} (hμ : IsPart μ) (hne : μ ≠ []) :
    (∃ s k, RibbonOn s k [] μ) ↔ μ.getD 1 0 ≤ 1 := by
  have hlen : 0 < μ.length := List.length_pos_iff.2 hne
  constructor
  · rintro ⟨s, k, h⟩
    have hs : s = 0 := by
      by_contra hcon
      have h0 : μ.getD 0 0 = 0 := by simpa using h.getD_eq_of_lt (i := 0) (by omega)
      have := hμ.getD_antitone (i := 0) (j := s) (Nat.zero_le _)
      have := h.getD_start_lt
      simp only [List.getD_nil] at this
      omega
    subst hs
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h2 := h.getD_eq_of_gt (i := 1) (by omega)
      simp only [List.getD_nil] at h2
      omega
    · have h2 := h.getD_succ (i := 0) (le_refl 0) hk
      simp only [zero_add, List.getD_nil] at h2
      omega
  · intro h1
    refine ⟨0, μ.length - 1, fun i hi => ?_, fun i _ hi => ?_, ?_, fun i hi => ?_⟩
    · rw [List.getD_eq_default _ _ (by omega), List.getD_nil]
    · have hpos := hμ.getD_pos (i := i + 1) (by omega)
      have hanti := hμ.getD_antitone (i := 1) (j := i + 1) (by omega)
      simp only [List.getD_nil]
      omega
    · simpa using hμ.getD_pos hlen
    · omega

end Young
