/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.List.Included

/-!
# Adding and removing a corner box of a partition

A Lean 4 port of the corner part of `theories/Combi/partition.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

## Main definitions

* `Young.incrNth μ i` : add a box at the end of row `i` (mathcomp `incr_nth`).
* `Young.decrNth μ i` : remove the last box of row `i` (Coq `decr_nth`).
* `Young.IsRemCorner μ i` : row `i` ends with a removable corner.
* `Young.IsAddCorner μ i` : a box can be added at the end of row `i`.

## Main results

* `Young.isPart_incrNth` / `Young.isPart_decrNth` : adding a box at an addable
  corner, resp. removing a box at a removable corner, of a partition yields a
  partition.
* `Young.decrNth_incrNth` / `Young.incrNth_decrNth` : the two operations are
  mutually inverse.
-/

@[expose] public section

namespace Young

open List

/-- Add one box at the end of row `i` (the mathcomp function `incr_nth`). -/
def incrNth : List ℕ → ℕ → List ℕ
  | [], 0 => [1]
  | [], n + 1 => 0 :: incrNth [] n
  | s0 :: s, 0 => (s0 + 1) :: s
  | s0 :: s, n + 1 => s0 :: incrNth s n

/-- Remove one box at the end of row `i` (Coq `decr_nth`).  When the row has a
single box, the row is deleted together with everything below it, which is the
intended behaviour for a removable corner of a partition. -/
def decrNth : List ℕ → ℕ → List ℕ
  | [], _ => []
  | 0 :: _, 0 => []
  | 1 :: _, 0 => []
  | (n + 2) :: v, 0 => (n + 1) :: v
  | n :: v, i + 1 => n :: decrNth v i

/-- Row `i` of `μ` ends with a removable corner. -/
def IsRemCorner (μ : List ℕ) (i : ℕ) : Prop := μ.getD (i + 1) 0 < μ.getD i 0

/-- A box may be added at the end of row `i` of `μ`. -/
def IsAddCorner (μ : List ℕ) (i : ℕ) : Prop := i = 0 ∨ μ.getD i 0 < μ.getD (i - 1) 0

instance (μ : List ℕ) (i : ℕ) : Decidable (IsRemCorner μ i) :=
  inferInstanceAs (Decidable (_ < _))

instance (μ : List ℕ) (i : ℕ) : Decidable (IsAddCorner μ i) :=
  inferInstanceAs (Decidable (_ ∨ _))

@[simp] lemma incrNth_nil_zero : incrNth [] 0 = [1] := rfl

@[simp] lemma incrNth_nil_succ (n : ℕ) : incrNth [] (n + 1) = 0 :: incrNth [] n := rfl

@[simp] lemma incrNth_cons_zero (a : ℕ) (s : List ℕ) : incrNth (a :: s) 0 = (a + 1) :: s := rfl

@[simp] lemma incrNth_cons_succ (a : ℕ) (s : List ℕ) (n : ℕ) :
    incrNth (a :: s) (n + 1) = a :: incrNth s n := rfl

@[simp] lemma decrNth_nil (i : ℕ) : decrNth [] i = [] := by cases i <;> rfl

@[simp] lemma decrNth_zero_cons_zero (s : List ℕ) : decrNth (0 :: s) 0 = [] := rfl

@[simp] lemma decrNth_one_cons_zero (s : List ℕ) : decrNth (1 :: s) 0 = [] := rfl

@[simp] lemma decrNth_succ_succ_cons_zero (n : ℕ) (s : List ℕ) :
    decrNth ((n + 2) :: s) 0 = (n + 1) :: s := rfl

@[simp] lemma decrNth_cons_succ (a : ℕ) (s : List ℕ) (i : ℕ) :
    decrNth (a :: s) (i + 1) = a :: decrNth s i := by
  match a with
  | 0 => rfl
  | 1 => rfl
  | (n + 2) => rfl

/-! ### Adding a box -/

/-- Coq `nth_incr_nth`. -/
lemma getD_incrNth : ∀ (s : List ℕ) (i j : ℕ),
    (incrNth s i).getD j 0 = s.getD j 0 + (if i = j then 1 else 0)
  | [], 0, j => by cases j <;> simp
  | [], (i + 1), 0 => by simp
  | [], (i + 1), (j + 1) => by
      have := getD_incrNth [] i j
      simpa using this
  | (_ :: _), 0, 0 => by simp
  | (_ :: _), 0, (_ + 1) => by simp
  | (_ :: _), (_ + 1), 0 => by simp
  | (_ :: s), (i + 1), (j + 1) => by
      have := getD_incrNth s i j
      simpa using this

/-- Coq `sumn_incr_nth`. -/
@[simp] lemma sum_incrNth : ∀ (s : List ℕ) (i : ℕ), (incrNth s i).sum = s.sum + 1
  | [], 0 => by simp
  | [], (i + 1) => by simp [sum_incrNth [] i]
  | (a :: s), 0 => by simp; omega
  | (a :: s), (i + 1) => by
      simp only [incrNth_cons_succ, List.sum_cons, sum_incrNth s i]
      omega

lemma length_incrNth : ∀ (s : List ℕ) (i : ℕ), (incrNth s i).length = max s.length (i + 1)
  | [], 0 => by simp
  | [], (i + 1) => by simp [length_incrNth [] i]
  | (a :: s), 0 => by simp
  | (a :: s), (i + 1) => by
      simp only [incrNth_cons_succ, List.length_cons, length_incrNth s i]
      omega

/-- Coq `included_incr_nth`. -/
lemma included_incrNth (μ : List ℕ) (i : ℕ) : Included μ (incrNth μ i) := by
  refine included_iff.2 ⟨by rw [length_incrNth]; exact Nat.le_max_left _ _, fun j => ?_⟩
  rw [getD_incrNth]
  omega

lemma le_length_of_isAddCorner {μ : List ℕ} {i : ℕ} (hc : IsAddCorner μ i) :
    i ≤ μ.length := by
  rcases hc with rfl | hc
  · exact Nat.zero_le _
  · by_contra hlt
    push Not at hlt
    have : μ.getD (i - 1) 0 = 0 := List.getD_eq_default _ _ (by omega)
    omega

/-- Coq `is_part_incr_nth`. -/
lemma isPart_incrNth {μ : List ℕ} {i : ℕ} (h : IsPart μ) (hc : IsAddCorner μ i) :
    IsPart (incrNth μ i) := by
  have hlen : i ≤ μ.length := le_length_of_isAddCorner hc
  rw [isPart_iff_getD_pos]
  refine ⟨fun j => ?_, fun j hj => ?_⟩
  · rw [getD_incrNth, getD_incrNth]
    have hmono := h.getD_succ_le j
    by_cases h1 : i = j + 1
    · have hcorner : μ.getD (j + 1) 0 < μ.getD j 0 := by
        rcases hc with h0 | hc
        · omega
        · rw [h1] at hc; simpa using hc
      rw [ite_eq_left h1, ite_eq_right (by omega : ¬ (i = j))]
      omega
    · rw [ite_eq_right h1]
      by_cases h2 : i = j
      · rw [ite_eq_left h2]; omega
      · rw [ite_eq_right h2]; omega
  · rw [length_incrNth] at hj
    rw [getD_incrNth]
    by_cases h2 : i = j
    · simp [h2]
    · simp only [ite_eq_right h2, Nat.add_zero]
      refine h.getD_pos ?_
      omega

/-- Coq `rem_corner_incr_nth`. -/
lemma isRemCorner_incrNth {μ : List ℕ} {i : ℕ} (h : IsPart μ) :
    IsRemCorner (incrNth μ i) i := by
  have hmono := h.getD_succ_le i
  have e1 : (incrNth μ i).getD (i + 1) 0 = μ.getD (i + 1) 0 := by
    rw [getD_incrNth, ite_eq_right (by omega : ¬ (i = i + 1)), Nat.add_zero]
  have e2 : (incrNth μ i).getD i 0 = μ.getD i 0 + 1 := by
    rw [getD_incrNth, ite_eq_left rfl]
  simp only [IsRemCorner, e1, e2]
  omega

/-- Coq `incr_nthK`. -/
lemma decrNth_incrNth : ∀ {μ : List ℕ} {i : ℕ}, IsPart μ → IsPart (incrNth μ i) →
    decrNth (incrNth μ i) i = μ
  | [], 0, _, _ => by simp
  | [], (i + 1), _, hi => by
      exfalso
      exact hi.zero_notMem (by simp)
  | (a :: s), 0, h, _ => by
      have ha : a ≠ 0 := by
        have := h.headD_ne_zero
        simpa using this
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      simp
  | (a :: s), (i + 1), h, hi => by
      rw [incrNth_cons_succ] at hi
      simp only [incrNth_cons_succ, decrNth_cons_succ]
      rw [decrNth_incrNth h.of_cons hi.of_cons]

/-! ### Removing a box -/

/-- Coq `included_decr_nth`. -/
lemma included_decrNth : ∀ (μ : List ℕ) (i : ℕ), Included (decrNth μ i) μ
  | [], i => by simp
  | (0 :: s), 0 => by simp
  | (1 :: s), 0 => by simp
  | ((n + 2) :: s), 0 => by
      simp only [decrNth_succ_succ_cons_zero, included_cons_cons]
      exact ⟨by omega, Included.refl s⟩
  | (a :: s), (i + 1) => by
      simp only [decrNth_cons_succ, included_cons_cons]
      exact ⟨le_refl _, included_decrNth s i⟩

lemma getD_decrNth_le (μ : List ℕ) (i j : ℕ) : (decrNth μ i).getD j 0 ≤ μ.getD j 0 :=
  (included_decrNth μ i).getD_le j

/-- Coq `nth_decr_nth`. -/
lemma getD_decrNth_self : ∀ (μ : List ℕ) (i : ℕ), (decrNth μ i).getD i 0 = μ.getD i 0 - 1
  | [], i => by simp
  | (0 :: s), 0 => by simp
  | (1 :: s), 0 => by simp
  | ((n + 2) :: s), 0 => by simp
  | (a :: s), (i + 1) => by
      simp only [decrNth_cons_succ, List.getD_cons_succ]
      exact getD_decrNth_self s i

/-- Coq `is_part_decr_nth`. -/
lemma isPart_decrNth : ∀ {μ : List ℕ} {i : ℕ}, IsPart μ → IsRemCorner μ i →
    IsPart (decrNth μ i)
  | [], i, _, hc => by simp
  | (0 :: s), 0, h, hc => by
      exfalso
      have := h.headD_ne_zero
      simp at this
  | (1 :: s), 0, h, hc => by simp
  | ((n + 2) :: s), 0, h, hc => by
      simp only [decrNth_succ_succ_cons_zero, isPart_cons]
      refine ⟨?_, h.of_cons⟩
      simp only [IsRemCorner, List.getD_cons_succ, List.getD_cons_zero] at hc
      cases s with
      | nil => simp
      | cons b t =>
        simp only [List.headD_cons]
        simp only [List.getD_cons_zero] at hc
        omega
  | (a :: s), (i + 1), h, hc => by
      have hcs : IsRemCorner s i := by
        simpa [IsRemCorner] using hc
      have hrec := isPart_decrNth h.of_cons hcs
      simp only [decrNth_cons_succ, isPart_cons]
      refine ⟨?_, hrec⟩
      have ha : 1 ≤ a := by
        have := (IsPart.headD_ne_zero (μ := a :: s) h)
        simp only [List.headD_cons] at this
        omega
      cases hd : decrNth s i with
      | nil => simpa [hd] using ha
      | cons b t =>
        have hb : b ≤ s.getD 0 0 := by
          have := getD_decrNth_le s i 0
          rw [hd] at this
          simpa using this
        have hs : s.getD 0 0 ≤ a := by
          cases s with
          | nil => simp
          | cons c u =>
            simp only [List.getD_cons_zero]
            simpa using h.headD_le_of_cons
        simpa using le_trans hb hs

/-- Coq `decr_nthK`. -/
lemma incrNth_decrNth : ∀ {μ : List ℕ} {i : ℕ}, IsPart μ → IsRemCorner μ i →
    incrNth (decrNth μ i) i = μ
  | [], i, _, hc => by simp [IsRemCorner] at hc
  | (0 :: s), 0, h, hc => by simp [IsRemCorner] at hc
  | (1 :: s), 0, h, hc => by
      have hs : s = [] := by
        refine h.of_cons.eq_nil_of_headD_eq_zero ?_
        simp only [IsRemCorner, List.getD_cons_succ, List.getD_cons_zero] at hc
        cases s with
        | nil => simp
        | cons b t =>
          simp only [List.getD_cons_zero] at hc
          simpa using by omega
      subst hs
      simp
  | ((n + 2) :: s), 0, h, hc => by simp
  | (a :: s), (i + 1), h, hc => by
      have hcs : IsRemCorner s i := by simpa [IsRemCorner] using hc
      simp only [decrNth_cons_succ, incrNth_cons_succ]
      rw [incrNth_decrNth h.of_cons hcs]

/-- Coq `sumn_decr_nth`. -/
lemma sum_decrNth {μ : List ℕ} {i : ℕ} (h : IsPart μ) (hc : IsRemCorner μ i) :
    (decrNth μ i).sum = μ.sum - 1 := by
  have := sum_incrNth (decrNth μ i) i
  rw [incrNth_decrNth h hc] at this
  omega

/-- Coq `nth_decr_nth_neq`. -/
lemma getD_decrNth_of_ne {μ : List ℕ} {i : ℕ} (h : IsPart μ) (hc : IsRemCorner μ i)
    {j : ℕ} (hij : i ≠ j) : (decrNth μ i).getD j 0 = μ.getD j 0 := by
  conv_rhs => rw [← incrNth_decrNth h hc]
  rw [getD_incrNth, ite_eq_right hij, Nat.add_zero]

/-- Coq `add_corner_decr_nth`. -/
lemma isAddCorner_decrNth {μ : List ℕ} {i : ℕ} (h : IsPart μ) (hc : IsRemCorner μ i) :
    IsAddCorner (decrNth μ i) i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact Or.inl rfl
  refine Or.inr ?_
  have hne : i ≠ i - 1 := by omega
  rw [getD_decrNth_self, getD_decrNth_of_ne h hc hne]
  have hmono : μ.getD i 0 ≤ μ.getD (i - 1) 0 := h.getD_antitone (by omega)
  have hpos : 0 < μ.getD i 0 := by
    simp only [IsRemCorner] at hc
    omega
  omega

end Young
