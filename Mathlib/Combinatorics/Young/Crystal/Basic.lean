/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Data.Nat.SuccPred

/-!
# Crystal operators on words

The *crystal operators* (or Lascoux–Schützenberger operators) `e i` and `f i` act on words
over `ℕ`.  Fixing `i`, one only looks at the letters `i` and `i + 1`, viewing `i + 1` as an
opening bracket and `i` as a closing bracket, and cancels matching pairs of brackets.  After
cancellation the remaining letters form a word `i … i (i+1) … (i+1)`; the operator `e i`
changes the leftmost remaining `i + 1` into an `i`, and `f i` changes the rightmost remaining
`i` into an `i + 1`.  Both are partial operations, returning `none` when nothing remains.

## Main definitions

* `List.crystalEps i w` : the number of unmatched letters `i` in `w`.
* `List.crystalPhi i w` : the number of unmatched letters `i + 1` in `w`.
* `List.crystalE i w` : the crystal raising operator.
* `List.crystalF i w` : the crystal lowering operator.

## Main results

* `List.crystalEps_append`, `List.crystalPhi_append` : the counts of unmatched letters of a
  concatenation.
* `List.crystalE_append`, `List.crystalF_append` : the *tensor rule*, describing on which
  factor of a concatenation the operators act.
* `List.crystalF_crystalE`, `List.crystalE_crystalF` : `f i` is the inverse of `e i`.
* `List.crystalPhi_eq_zero_iff` : there is no unmatched `i + 1` iff every suffix contains at
  least as many letters `i` as letters `i + 1`.
-/

namespace List

open List

/-! ### Unmatched letters -/

/-- The number of unmatched letters `i` of `w`, viewing the letters `i + 1` as opening
brackets and the letters `i` as closing brackets. -/
def crystalEps (i : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: w =>
      if x = i then crystalEps i w + 1
      else if x = i + 1 then crystalEps i w - 1
      else crystalEps i w

/-- The number of unmatched letters `i + 1` of `w`, viewing the letters `i + 1` as opening
brackets and the letters `i` as closing brackets. -/
def crystalPhi (i : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: w => if x = i + 1 ∧ crystalEps i w = 0 then crystalPhi i w + 1 else crystalPhi i w

@[simp] lemma crystalEps_nil (i : ℕ) : crystalEps i [] = 0 := rfl

@[simp] lemma crystalPhi_nil (i : ℕ) : crystalPhi i [] = 0 := rfl

@[simp] lemma crystalEps_cons_self (i : ℕ) (w : List ℕ) :
    crystalEps i (i :: w) = crystalEps i w + 1 := by simp [crystalEps]

@[simp] lemma crystalEps_cons_succ (i : ℕ) (w : List ℕ) :
    crystalEps i ((i + 1) :: w) = crystalEps i w - 1 := by simp [crystalEps]

lemma crystalEps_cons_of_ne {i x : ℕ} (h1 : x ≠ i) (h2 : x ≠ i + 1) (w : List ℕ) :
    crystalEps i (x :: w) = crystalEps i w := by simp [crystalEps, h1, h2]

@[simp] lemma crystalPhi_cons_self (i : ℕ) (w : List ℕ) :
    crystalPhi i (i :: w) = crystalPhi i w := by simp [crystalPhi]

lemma crystalPhi_cons_succ (i : ℕ) (w : List ℕ) :
    crystalPhi i ((i + 1) :: w) =
      if crystalEps i w = 0 then crystalPhi i w + 1 else crystalPhi i w := by
  simp [crystalPhi]

lemma crystalPhi_cons_of_ne {i x : ℕ} (h2 : x ≠ i + 1) (w : List ℕ) :
    crystalPhi i (x :: w) = crystalPhi i w := by simp [crystalPhi, h2]

/-- The difference between the numbers of unmatched letters is the difference between the
numbers of letters. -/
lemma crystalPhi_add_count (i : ℕ) (w : List ℕ) :
    crystalPhi i w + w.count i = crystalEps i w + w.count (i + 1) := by
  induction w with
  | nil => simp
  | cons x w ih =>
    have hii : i ≠ i + 1 := by omega
    rcases eq_or_ne x i with rfl | hne
    · rw [crystalEps_cons_self, crystalPhi_cons_self, List.count_cons_self,
        List.count_cons_of_ne hii]
      omega
    · rcases eq_or_ne x (i + 1) with rfl | hne'
      · rw [crystalEps_cons_succ, crystalPhi_cons_succ, List.count_cons_self,
          List.count_cons_of_ne hne]
        split <;> omega
      · rw [crystalEps_cons_of_ne hne hne' w, crystalPhi_cons_of_ne hne' w,
          List.count_cons_of_ne hne, List.count_cons_of_ne hne']
        exact ih

/-! ### The crystal operators -/

/-- The crystal raising operator: it changes into an `i` the leftmost unmatched `i + 1`
of `w`, if there is one. -/
def crystalE (i : ℕ) : List ℕ → Option (List ℕ)
  | [] => none
  | x :: w =>
      if x = i + 1 ∧ crystalEps i w = 0 then some (i :: w)
      else (crystalE i w).map (x :: ·)

/-- The crystal lowering operator: it changes into an `i + 1` the rightmost unmatched `i`
of `w`, if there is one. -/
def crystalF (i : ℕ) : List ℕ → Option (List ℕ)
  | [] => none
  | x :: w =>
      if x = i ∧ crystalEps i w = 0 then some ((i + 1) :: w)
      else if x = i + 1 ∧ crystalEps i w ≤ 1 then none
      else (crystalF i w).map (x :: ·)

@[simp] lemma crystalE_nil (i : ℕ) : crystalE i [] = none := rfl

@[simp] lemma crystalF_nil (i : ℕ) : crystalF i [] = none := rfl

lemma crystalE_cons (i x : ℕ) (w : List ℕ) :
    crystalE i (x :: w) =
      if x = i + 1 ∧ crystalEps i w = 0 then some (i :: w)
      else (crystalE i w).map (x :: ·) := rfl

lemma crystalF_cons (i x : ℕ) (w : List ℕ) :
    crystalF i (x :: w) =
      if x = i ∧ crystalEps i w = 0 then some ((i + 1) :: w)
      else if x = i + 1 ∧ crystalEps i w ≤ 1 then none
      else (crystalF i w).map (x :: ·) := rfl

/-- The raising operator is defined exactly when there is an unmatched `i + 1`. -/
theorem crystalE_isSome_iff (i : ℕ) (w : List ℕ) :
    (crystalE i w).isSome ↔ crystalPhi i w ≠ 0 := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [crystalE_cons]
    by_cases hx : x = i + 1 ∧ crystalEps i w = 0
    · obtain ⟨rfl, h0⟩ := hx
      simp [crystalPhi_cons_succ, h0]
    · rw [if_neg hx]
      have hphi : crystalPhi i (x :: w) = crystalPhi i w := by
        rcases eq_or_ne x (i + 1) with rfl | hne
        · rw [crystalPhi_cons_succ, if_neg (by tauto)]
        · exact crystalPhi_cons_of_ne hne w
      rw [hphi, ← ih]
      cases crystalE i w <;> simp

/-- The lowering operator is defined exactly when there is an unmatched `i`. -/
theorem crystalF_isSome_iff (i : ℕ) (w : List ℕ) :
    (crystalF i w).isSome ↔ crystalEps i w ≠ 0 := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [crystalF_cons]
    by_cases hx : x = i ∧ crystalEps i w = 0
    · obtain ⟨rfl, h0⟩ := hx
      simp [h0]
    · rw [if_neg hx]
      by_cases hx' : x = i + 1 ∧ crystalEps i w ≤ 1
      · obtain ⟨rfl, h1⟩ := hx'
        rw [if_pos ⟨rfl, h1⟩, crystalEps_cons_succ]
        simp only [Option.isSome_none, Bool.false_eq_true, false_iff, ne_eq, Decidable.not_not]
        omega
      · rw [if_neg hx']
        have heps : crystalEps i (x :: w) ≠ 0 ↔ crystalEps i w ≠ 0 := by
          rcases eq_or_ne x i with rfl | hne
          · simp only [crystalEps_cons_self]
            constructor
            · intro _ h; exact hx ⟨rfl, h⟩
            · omega
          · rcases eq_or_ne x (i + 1) with rfl | hne'
            · rw [crystalEps_cons_succ]
              have : ¬ crystalEps i w ≤ 1 := fun h => hx' ⟨rfl, h⟩
              omega
            · rw [crystalEps_cons_of_ne hne hne']
        rw [heps, ← ih]
        cases crystalF i w <;> simp

/-! ### Concatenation -/

theorem crystalE_eq_none_iff (i : ℕ) (w : List ℕ) : crystalE i w = none ↔ crystalPhi i w = 0 := by
  rw [← Option.not_isSome_iff_eq_none, crystalE_isSome_iff]
  simp

theorem crystalF_eq_none_iff (i : ℕ) (w : List ℕ) : crystalF i w = none ↔ crystalEps i w = 0 := by
  rw [← Option.not_isSome_iff_eq_none, crystalF_isSome_iff]
  simp

theorem crystalEps_append (i : ℕ) (u v : List ℕ) :
    crystalEps i (u ++ v) = crystalEps i u + (crystalEps i v - crystalPhi i u) := by
  induction u with
  | nil => simp
  | cons x u ih =>
    rcases eq_or_ne x i with rfl | hne
    · rw [List.cons_append, crystalEps_cons_self, crystalEps_cons_self, crystalPhi_cons_self, ih]
      omega
    · rcases eq_or_ne x (i + 1) with rfl | hne'
      · rw [List.cons_append, crystalEps_cons_succ, crystalEps_cons_succ, crystalPhi_cons_succ, ih]
        split <;> omega
      · rw [List.cons_append, crystalEps_cons_of_ne hne hne', crystalEps_cons_of_ne hne hne',
          crystalPhi_cons_of_ne hne', ih]

theorem crystalPhi_append (i : ℕ) (u v : List ℕ) :
    crystalPhi i (u ++ v) = crystalPhi i v + (crystalPhi i u - crystalEps i v) := by
  induction u with
  | nil => simp
  | cons x u ih =>
    rcases eq_or_ne x i with rfl | hne
    · rw [List.cons_append, crystalPhi_cons_self, crystalPhi_cons_self, ih]
    · rcases eq_or_ne x (i + 1) with rfl | hne'
      · rw [List.cons_append, crystalPhi_cons_succ, crystalPhi_cons_succ, ih, crystalEps_append]
        split <;> split <;> omega
      · rw [List.cons_append, crystalPhi_cons_of_ne hne', crystalPhi_cons_of_ne hne', ih]

/-- The tensor rule for the raising operator: it acts on the left factor of a concatenation
as soon as the left factor has more unmatched `i + 1` than the right factor has unmatched
`i`. -/
theorem crystalE_append (i : ℕ) (u v : List ℕ) :
    crystalE i (u ++ v) =
      if crystalEps i v < crystalPhi i u then (crystalE i u).map (· ++ v)
      else (crystalE i v).map (u ++ ·) := by
  induction u with
  | nil => simp
  | cons x u ih =>
    rcases eq_or_ne x (i + 1) with rfl | hne'
    · rcases eq_or_ne (crystalEps i u) 0 with h0 | h0
      · rw [crystalPhi_cons_succ, if_pos h0]
        rcases lt_or_ge (crystalEps i v) (crystalPhi i u + 1) with hlt | hge
        · have heps : crystalEps i (u ++ v) = 0 := by rw [crystalEps_append]; omega
          rw [List.cons_append, crystalE_cons, if_pos ⟨rfl, heps⟩, if_pos hlt, crystalE_cons,
            if_pos ⟨rfl, h0⟩]
          simp
        · have heps : crystalEps i (u ++ v) ≠ 0 := by rw [crystalEps_append]; omega
          rw [List.cons_append, crystalE_cons, if_neg (by tauto), ih, if_neg (by omega),
            if_neg (by omega)]
          simp [Option.map_map, Function.comp_def]
      · have hphi : crystalPhi i ((i + 1) :: u) = crystalPhi i u := by
          rw [crystalPhi_cons_succ, if_neg h0]
        have hEcons : crystalE i ((i + 1) :: u) = (crystalE i u).map ((i + 1) :: ·) := by
          rw [crystalE_cons, if_neg (by tauto)]
        rw [List.cons_append, crystalE_cons,
          if_neg (by rw [crystalEps_append]; rintro ⟨-, h⟩; omega), ih, hphi, hEcons]
        split <;> simp [Option.map_map, Function.comp_def]
    · have hphi : crystalPhi i (x :: u) = crystalPhi i u := crystalPhi_cons_of_ne hne' u
      have hEcons : crystalE i (x :: u) = (crystalE i u).map (x :: ·) := by
        rw [crystalE_cons, if_neg (by tauto)]
      rw [List.cons_append, crystalE_cons, if_neg (by tauto), ih, hphi, hEcons]
      split <;> simp [Option.map_map, Function.comp_def]

/-- The tensor rule for the lowering operator. -/
theorem crystalF_append (i : ℕ) (u v : List ℕ) :
    crystalF i (u ++ v) =
      if crystalPhi i u < crystalEps i v then (crystalF i v).map (u ++ ·)
      else (crystalF i u).map (· ++ v) := by
  induction u with
  | nil =>
    simp only [List.nil_append, crystalPhi_nil, crystalF_nil, Option.map_none]
    split
    · simp
    · rw [(crystalF_eq_none_iff i v).2 (by omega)]
  | cons x u ih =>
    rcases eq_or_ne x i with rfl | hne
    · rcases eq_or_ne (crystalEps x u) 0 with h0 | h0
      · have hphi : crystalPhi x (x :: u) = crystalPhi x u := crystalPhi_cons_self x u
        have heps : crystalEps x (u ++ v) = crystalEps x v - crystalPhi x u := by
          rw [crystalEps_append, h0]; omega
        rcases lt_or_ge (crystalPhi x u) (crystalEps x v) with hlt | hge
        · have h1 : crystalEps x (u ++ v) ≠ 0 := by omega
          rw [List.cons_append, crystalF_cons, if_neg (by rintro ⟨-, h⟩; omega),
            if_neg (by rintro ⟨h, -⟩; omega), ih, if_pos hlt, hphi, if_pos hlt]
          simp [Option.map_map, Function.comp_def]
        · have h1 : crystalEps x (u ++ v) = 0 := by omega
          rw [List.cons_append, crystalF_cons, if_pos ⟨rfl, h1⟩, hphi, if_neg (by omega),
            crystalF_cons, if_pos ⟨rfl, h0⟩]
          simp
      · have hphi : crystalPhi x (x :: u) = crystalPhi x u := crystalPhi_cons_self x u
        have heps : crystalEps x (u ++ v) ≠ 0 := by rw [crystalEps_append]; omega
        have hFcons : crystalF x (x :: u) = (crystalF x u).map (x :: ·) := by
          rw [crystalF_cons, if_neg (by rintro ⟨-, h⟩; omega), if_neg (by rintro ⟨h, -⟩; omega)]
        rw [List.cons_append, crystalF_cons, if_neg (by rintro ⟨-, h⟩; omega),
          if_neg (by rintro ⟨h, -⟩; omega), ih, hphi, hFcons]
        split <;> simp [Option.map_map, Function.comp_def]
    · rcases eq_or_ne x (i + 1) with rfl | hne'
      · have hphi : crystalPhi i ((i + 1) :: u) =
            if crystalEps i u = 0 then crystalPhi i u + 1 else crystalPhi i u :=
          crystalPhi_cons_succ i u
        rcases eq_or_ne (crystalEps i u) 0 with h0 | h0
        · have heps : crystalEps i (u ++ v) = crystalEps i v - crystalPhi i u := by
            rw [crystalEps_append, h0]; omega
          rw [hphi, if_pos h0]
          rcases lt_or_ge (crystalPhi i u + 1) (crystalEps i v) with hlt | hge
          · have h1 : ¬ crystalEps i (u ++ v) ≤ 1 := by omega
            rw [List.cons_append, crystalF_cons, if_neg (by omega),
              if_neg (by rintro ⟨-, h⟩; omega), ih, if_pos (by omega), if_pos hlt]
            simp [Option.map_map, Function.comp_def]
          · have h1 : crystalEps i (u ++ v) ≤ 1 := by omega
            rw [List.cons_append, crystalF_cons, if_neg (by omega), if_pos ⟨rfl, h1⟩,
              if_neg (by omega), crystalF_cons, if_neg (by omega), if_pos ⟨rfl, by omega⟩]
            rfl
        · have hFcons : crystalF i ((i + 1) :: u) =
              if crystalEps i u ≤ 1 then none else (crystalF i u).map ((i + 1) :: ·) := by
            rw [crystalF_cons, if_neg (by omega)]
            by_cases h2 : crystalEps i u ≤ 1
            · rw [if_pos ⟨rfl, h2⟩, if_pos h2]
            · rw [if_neg (by rintro ⟨-, h⟩; omega), if_neg h2]
          have heps : crystalEps i (u ++ v) = crystalEps i u + (crystalEps i v - crystalPhi i u) :=
            crystalEps_append i u v
          rw [hphi, if_neg h0, hFcons]
          rcases lt_or_ge (crystalPhi i u) (crystalEps i v) with hlt | hge
          · have h1 : ¬ crystalEps i (u ++ v) ≤ 1 := by omega
            rw [List.cons_append, crystalF_cons, if_neg (by omega),
              if_neg (by rintro ⟨-, h⟩; omega), ih, if_pos hlt, if_pos hlt]
            simp [Option.map_map, Function.comp_def]
          · rcases le_or_gt (crystalEps i u) 1 with h2 | h2
            · have h1 : crystalEps i (u ++ v) ≤ 1 := by omega
              rw [List.cons_append, crystalF_cons, if_neg (by omega), if_pos ⟨rfl, h1⟩,
                if_neg (by omega), if_pos h2]
              rfl
            · have h1 : ¬ crystalEps i (u ++ v) ≤ 1 := by omega
              rw [List.cons_append, crystalF_cons, if_neg (by omega),
                if_neg (by rintro ⟨-, h⟩; omega), ih, if_neg (by omega), if_neg (by omega),
                if_neg (by omega)]
              simp [Option.map_map, Function.comp_def]
      · have hphi : crystalPhi i (x :: u) = crystalPhi i u := crystalPhi_cons_of_ne hne' u
        have hFcons : crystalF i (x :: u) = (crystalF i u).map (x :: ·) := by
          rw [crystalF_cons, if_neg (by tauto), if_neg (by tauto)]
        rw [List.cons_append, crystalF_cons, if_neg (by tauto), if_neg (by tauto), ih, hphi,
          hFcons]
        split <;> simp [Option.map_map, Function.comp_def]

/-! ### The operators change a single letter -/

/-- The raising operator replaces one letter `i + 1` by `i`. -/
theorem crystalE_eq_set {i : ℕ} {w w' : List ℕ} (h : crystalE i w = some w') :
    ∃ j, ∃ _ : j < w.length, w[j] = i + 1 ∧ w' = w.set j i := by
  induction w generalizing w' with
  | nil => simp at h
  | cons x w ih =>
    rw [crystalE_cons] at h
    by_cases hx : x = i + 1 ∧ crystalEps i w = 0
    · rw [if_pos hx] at h
      obtain ⟨hx1, -⟩ := hx
      exact ⟨0, by simp, by simp [hx1], by simp at h; simp [← h]⟩
    · rw [if_neg hx] at h
      obtain ⟨w0, hw0, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨j, hj, h1, h2⟩ := ih hw0
      exact ⟨j + 1, by simpa using hj, by simpa using h1, by simp [h2]⟩

/-- The lowering operator replaces one letter `i` by `i + 1`. -/
theorem crystalF_eq_set {i : ℕ} {w w' : List ℕ} (h : crystalF i w = some w') :
    ∃ j, ∃ _ : j < w.length, w[j] = i ∧ w' = w.set j (i + 1) := by
  induction w generalizing w' with
  | nil => simp at h
  | cons x w ih =>
    rw [crystalF_cons] at h
    by_cases hx : x = i ∧ crystalEps i w = 0
    · rw [if_pos hx] at h
      obtain ⟨hx1, -⟩ := hx
      exact ⟨0, by simp, by simp [hx1], by simp at h; simp [← h]⟩
    · rw [if_neg hx] at h
      by_cases hx' : x = i + 1 ∧ crystalEps i w ≤ 1
      · rw [if_pos hx'] at h; simp at h
      · rw [if_neg hx'] at h
        obtain ⟨w0, hw0, rfl⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨j, hj, h1, h2⟩ := ih hw0
        exact ⟨j + 1, by simpa using hj, by simpa using h1, by simp [h2]⟩

/-! ### Behaviour of the invariants -/

theorem crystalEps_crystalE {i : ℕ} {w w' : List ℕ} (h : crystalE i w = some w') :
    crystalEps i w' = crystalEps i w + 1 := by
  induction w generalizing w' with
  | nil => simp at h
  | cons x w ih =>
    rw [crystalE_cons] at h
    by_cases hx : x = i + 1 ∧ crystalEps i w = 0
    · rw [if_pos hx] at h
      obtain ⟨rfl, h0⟩ := hx
      simp only [Option.some_inj] at h
      subst h
      simp [h0]
    · rw [if_neg hx] at h
      obtain ⟨w0, hw0, rfl⟩ := Option.map_eq_some_iff.1 h
      have ihw := ih hw0
      rcases eq_or_ne x i with rfl | hne
      · rw [crystalEps_cons_self, crystalEps_cons_self, ihw]
      · rcases eq_or_ne x (i + 1) with rfl | hne'
        · have h0 : crystalEps i w ≠ 0 := fun hc => hx ⟨rfl, hc⟩
          rw [crystalEps_cons_succ, crystalEps_cons_succ, ihw]
          omega
        · rw [crystalEps_cons_of_ne hne hne', crystalEps_cons_of_ne hne hne', ihw]

theorem crystalEps_crystalF {i : ℕ} {w w' : List ℕ} (h : crystalF i w = some w') :
    crystalEps i w' + 1 = crystalEps i w := by
  induction w generalizing w' with
  | nil => simp at h
  | cons x w ih =>
    rw [crystalF_cons] at h
    by_cases hx : x = i ∧ crystalEps i w = 0
    · rw [if_pos hx] at h
      obtain ⟨rfl, h0⟩ := hx
      simp only [Option.some_inj] at h
      subst h
      rw [crystalEps_cons_succ, crystalEps_cons_self, h0]
    · rw [if_neg hx] at h
      by_cases hx' : x = i + 1 ∧ crystalEps i w ≤ 1
      · rw [if_pos hx'] at h; simp at h
      · rw [if_neg hx'] at h
        obtain ⟨w0, hw0, rfl⟩ := Option.map_eq_some_iff.1 h
        have ihw := ih hw0
        rcases eq_or_ne x i with rfl | hne
        · rw [crystalEps_cons_self, crystalEps_cons_self]
          omega
        · rcases eq_or_ne x (i + 1) with rfl | hne'
          · have h0 : ¬ crystalEps i w ≤ 1 := fun hc => hx' ⟨rfl, hc⟩
            rw [crystalEps_cons_succ, crystalEps_cons_succ]
            omega
          · rw [crystalEps_cons_of_ne hne hne', crystalEps_cons_of_ne hne hne', ihw]

theorem crystalPhi_crystalE {i : ℕ} {w w' : List ℕ} (h : crystalE i w = some w') :
    crystalPhi i w' + 1 = crystalPhi i w := by
  induction w generalizing w' with
  | nil => simp at h
  | cons x w ih =>
    rw [crystalE_cons] at h
    by_cases hx : x = i + 1 ∧ crystalEps i w = 0
    · rw [if_pos hx] at h
      obtain ⟨rfl, h0⟩ := hx
      simp only [Option.some_inj] at h
      subst h
      rw [crystalPhi_cons_self, crystalPhi_cons_succ, if_pos h0]
    · rw [if_neg hx] at h
      obtain ⟨w0, hw0, rfl⟩ := Option.map_eq_some_iff.1 h
      have ihw := ih hw0
      have heps : crystalEps i w0 = crystalEps i w + 1 := crystalEps_crystalE hw0
      rcases eq_or_ne x (i + 1) with rfl | hne'
      · have h0 : crystalEps i w ≠ 0 := fun hc => hx ⟨rfl, hc⟩
        rw [crystalPhi_cons_succ, crystalPhi_cons_succ, if_neg (by omega), if_neg h0, ihw]
      · rw [crystalPhi_cons_of_ne hne', crystalPhi_cons_of_ne hne', ihw]

/-! ### The two operators are inverse to each other -/

theorem crystalF_crystalE {i : ℕ} {w w' : List ℕ} (h : crystalE i w = some w') :
    crystalF i w' = some w := by
  induction w generalizing w' with
  | nil => simp at h
  | cons x w ih =>
    rw [crystalE_cons] at h
    by_cases hx : x = i + 1 ∧ crystalEps i w = 0
    · rw [if_pos hx] at h
      obtain ⟨rfl, h0⟩ := hx
      simp only [Option.some_inj] at h
      subst h
      rw [crystalF_cons, if_pos ⟨rfl, h0⟩]
    · rw [if_neg hx] at h
      obtain ⟨w0, hw0, rfl⟩ := Option.map_eq_some_iff.1 h
      have heps : crystalEps i w0 = crystalEps i w + 1 := crystalEps_crystalE hw0
      rcases eq_or_ne x i with rfl | hne
      · rw [crystalF_cons, if_neg (by rintro ⟨-, h⟩; omega), if_neg (by rintro ⟨h, -⟩; omega),
          ih hw0]
        rfl
      · rcases eq_or_ne x (i + 1) with rfl | hne'
        · have h0 : crystalEps i w ≠ 0 := fun hc => hx ⟨rfl, hc⟩
          rw [crystalF_cons, if_neg (by rintro ⟨h, -⟩; omega), if_neg (by rintro ⟨-, h⟩; omega),
            ih hw0]
          rfl
        · rw [crystalF_cons, if_neg (by rintro ⟨h, -⟩; exact hne h),
            if_neg (by rintro ⟨h, -⟩; exact hne' h), ih hw0]
          rfl

theorem crystalE_crystalF {i : ℕ} {w w' : List ℕ} (h : crystalF i w = some w') :
    crystalE i w' = some w := by
  induction w generalizing w' with
  | nil => simp at h
  | cons x w ih =>
    rw [crystalF_cons] at h
    by_cases hx : x = i ∧ crystalEps i w = 0
    · rw [if_pos hx] at h
      obtain ⟨rfl, h0⟩ := hx
      simp only [Option.some_inj] at h
      subst h
      rw [crystalE_cons, if_pos ⟨rfl, h0⟩]
    · rw [if_neg hx] at h
      by_cases hx' : x = i + 1 ∧ crystalEps i w ≤ 1
      · rw [if_pos hx'] at h; simp at h
      · rw [if_neg hx'] at h
        obtain ⟨w0, hw0, rfl⟩ := Option.map_eq_some_iff.1 h
        have heps : crystalEps i w0 + 1 = crystalEps i w := crystalEps_crystalF hw0
        rcases eq_or_ne x (i + 1) with rfl | hne'
        · have h0 : ¬ crystalEps i w ≤ 1 := fun hc => hx' ⟨rfl, hc⟩
          rw [crystalE_cons, if_neg (by rintro ⟨-, h⟩; omega), ih hw0]
          rfl
        · rw [crystalE_cons, if_neg (by rintro ⟨h, -⟩; exact hne' h), ih hw0]
          rfl

theorem crystalE_injective (i : ℕ) {u v w : List ℕ} (hu : crystalE i u = some w)
    (hv : crystalE i v = some w) : u = v := by
  rw [← Option.some_inj, ← crystalF_crystalE hu, ← crystalF_crystalE hv]

theorem crystalF_injective (i : ℕ) {u v w : List ℕ} (hu : crystalF i u = some w)
    (hv : crystalF i v = some w) : u = v := by
  rw [← Option.some_inj, ← crystalE_crystalF hu, ← crystalE_crystalF hv]

/-! ### Words with no unmatched letter -/

theorem crystalPhi_eq_zero_iff (i : ℕ) (w : List ℕ) :
    crystalPhi i w = 0 ↔ ∀ k, (w.drop k).count (i + 1) ≤ (w.drop k).count i := by
  induction w with
  | nil => simp
  | cons x w ih =>
    constructor
    · intro h k
      have hw : crystalPhi i w = 0 := by
        rcases eq_or_ne x (i + 1) with rfl | hne'
        · rw [crystalPhi_cons_succ] at h; split at h <;> omega
        · rwa [crystalPhi_cons_of_ne hne'] at h
      cases k with
      | zero =>
        simp only [List.drop_zero]
        have := crystalPhi_add_count i (x :: w)
        rw [h] at this
        omega
      | succ k => simpa using ih.1 hw k
    · intro h
      have hw : crystalPhi i w = 0 := ih.2 fun k => by simpa using h (k + 1)
      rcases eq_or_ne x (i + 1) with rfl | hne'
      · rw [crystalPhi_cons_succ]
        by_cases h0 : crystalEps i w = 0
        · exfalso
          have h1 := h 0
          have h2 := crystalPhi_add_count i w
          rw [hw, h0] at h2
          simp only [List.drop_zero] at h1
          rw [List.count_cons_self, List.count_cons_of_ne (by omega)] at h1
          omega
        · rw [if_neg h0]; exact hw
      · rwa [crystalPhi_cons_of_ne hne']

end List
