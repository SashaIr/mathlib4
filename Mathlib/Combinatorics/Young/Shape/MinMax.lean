/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Shape.Basic

/-!
# The componentwise minimum and maximum of two partitions

Two partitions `s` and `t`, seen as weakly decreasing sequences of natural numbers which
are eventually zero, have a componentwise minimum `partMin s t` and a componentwise
maximum `partMax s t`, both of which are again partitions.

These are used to describe the shapes lying between two partitions: a shape `nu` with
`HorizStrip s nu` and `HorizStrip t nu` is exactly a shape whose parts lie in the box
`max (s_{i+1}) (t_{i+1}) ≤ nu_i ≤ min (s_i) (t_i)`.

## Main definitions

* `List.partMin` : the componentwise minimum.
* `List.partMax` : the componentwise maximum.
-/

namespace List

open List

/-! ### The componentwise minimum -/

/-- The componentwise minimum of two partitions. -/
def partMin : List ℕ → List ℕ → List ℕ := List.zipWith min

@[simp] lemma partMin_nil_left (t : List ℕ) : partMin [] t = [] := rfl

@[simp] lemma partMin_nil_right (s : List ℕ) : partMin s [] = [] := by
  cases s <;> rfl

@[simp] lemma partMin_cons (a b : ℕ) (s t : List ℕ) :
    partMin (a :: s) (b :: t) = min a b :: partMin s t := rfl

lemma getD_partMin : ∀ (s t : List ℕ) (i : ℕ),
    (partMin s t).getD i 0 = min (s.getD i 0) (t.getD i 0)
  | [], t, i => by simp
  | a :: s, [], i => by simp
  | a :: s, b :: t, 0 => by simp
  | a :: s, b :: t, (i + 1) => by
      simp only [partMin_cons, List.getD_cons_succ]
      exact getD_partMin s t i

lemma isPart_partMin : ∀ {s t : List ℕ}, IsPart s → IsPart t → IsPart (partMin s t)
  | [], t, _, _ => by simp
  | a :: s, [], _, _ => by simp
  | a :: s, b :: t, hs, ht => by
      refine ⟨?_, isPart_partMin hs.2 ht.2⟩
      have hs0 : s.getD 0 0 ≤ a := by
        cases s with
        | nil => simp
        | cons c s' => simpa using hs.1
      have ht0 : t.getD 0 0 ≤ b := by
        cases t with
        | nil => simp
        | cons c t' => simpa using ht.1
      have key : ∀ l : List ℕ, l = partMin s t → l.headD 1 ≤ min a b := by
        rintro (_ | ⟨x, l⟩) hl
        · simp only [List.headD_nil]
          have ha : 0 < (a :: s).headD 0 := hs.headD_pos (by simp)
          have hb : 0 < (b :: t).headD 0 := ht.headD_pos (by simp)
          simp only [List.headD_cons] at ha hb
          omega
        · have hx : x = (partMin s t).getD 0 0 := by rw [← hl]; rfl
          rw [getD_partMin] at hx
          simp only [List.headD_cons]
          omega
      exact key _ rfl

/-! ### The componentwise maximum -/

/-- The componentwise maximum of two partitions. -/
def partMax : List ℕ → List ℕ → List ℕ
  | [], t => t
  | s, [] => s
  | a :: s, b :: t => max a b :: partMax s t

@[simp] lemma partMax_nil_left (t : List ℕ) : partMax [] t = t := rfl

@[simp] lemma partMax_nil_right : ∀ (s : List ℕ), partMax s [] = s
  | [] => rfl
  | _ :: _ => rfl

@[simp] lemma partMax_cons (a b : ℕ) (s t : List ℕ) :
    partMax (a :: s) (b :: t) = max a b :: partMax s t := rfl

lemma getD_partMax : ∀ (s t : List ℕ) (i : ℕ),
    (partMax s t).getD i 0 = max (s.getD i 0) (t.getD i 0)
  | [], t, i => by simp
  | a :: s, [], i => by simp
  | a :: s, b :: t, 0 => by simp
  | a :: s, b :: t, (i + 1) => by
      simp only [partMax_cons, List.getD_cons_succ]
      exact getD_partMax s t i

lemma isPart_partMax : ∀ {s t : List ℕ}, IsPart s → IsPart t → IsPart (partMax s t)
  | [], t, _, ht => by simpa using ht
  | a :: s, [], hs, _ => by simpa using hs
  | a :: s, b :: t, hs, ht => by
      refine ⟨?_, isPart_partMax hs.2 ht.2⟩
      have hs0 : s.getD 0 0 ≤ a := by
        cases s with
        | nil => simp
        | cons c s' => simpa using hs.1
      have ht0 : t.getD 0 0 ≤ b := by
        cases t with
        | nil => simp
        | cons c t' => simpa using ht.1
      have key : ∀ l : List ℕ, l = partMax s t → l.headD 1 ≤ max a b := by
        rintro (_ | ⟨x, l⟩) hl
        · simp only [List.headD_nil]
          have ha : 0 < (a :: s).headD 0 := hs.headD_pos (by simp)
          simp only [List.headD_cons] at ha
          omega
        · have hx : x = (partMax s t).getD 0 0 := by rw [← hl]; rfl
          rw [getD_partMax] at hx
          simp only [List.headD_cons]
          omega
      exact key _ rfl

/-! ### Sums -/

lemma sum_partMin_add_sum_partMax : ∀ (s t : List ℕ),
    (partMin s t).sum + (partMax s t).sum = s.sum + t.sum
  | [], t => by simp
  | a :: s, [] => by simp
  | a :: s, b :: t => by
      have := sum_partMin_add_sum_partMax s t
      simp only [partMin_cons, partMax_cons, List.sum_cons]
      omega

lemma partMax_eq_cons_tail : ∀ (s t : List ℕ), s ≠ [] ∨ t ≠ [] →
    partMax s t = max (s.getD 0 0) (t.getD 0 0) :: partMax s.tail t.tail
  | [], [], h => by simp at h
  | [], b :: t, _ => by simp
  | a :: s, [], _ => by simp
  | a :: s, b :: t, _ => by simp

end List
