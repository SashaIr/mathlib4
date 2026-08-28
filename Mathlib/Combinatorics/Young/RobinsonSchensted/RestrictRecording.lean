/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Tableau.StandardRestrict

/-!
# Restricting the recording tableau

The recording tableau `List.RSQ w` of a word is built by adding, at the `k`-th insertion,
a box containing the letter `k`.  Hence removing from it the letters `≥ k` gives the
recording tableau of the prefix of length `k` of `w`.

## Main results

* `List.dropMax_RSQ` : `dropMax k (RSQ w) = RSQ (w.take k)`.
-/

namespace List

open List

/-- Adding a box labelled by a letter `≥ k` does not change the restriction to the letters
`< k`. -/
lemma dropMax_addBox_of_le {Q : List (List ℕ)} {i m k : ℕ} (hk : k ≤ m) :
    dropMax k (addBox Q i m) = dropMax k Q := by
  induction Q generalizing i with
  | nil =>
    have : ltFilter k [m] = [] := by simp [ltFilter, Nat.not_lt.2 hk]
    simp [addBox_nil, dropMax_cons, this]
  | cons q0 Q ih =>
    cases i with
    | zero =>
      have happ : ltFilter k (q0 ++ [m]) = ltFilter k q0 := by
        simp [ltFilter, List.filter_append, Nat.not_lt.2 hk]
      rw [addBox_cons_zero, dropMax_cons, dropMax_cons, happ]
    | succ j =>
      rw [addBox_cons_succ, dropMax_cons, dropMax_cons, ih]

variable {T : Type*} [LinearOrder T]

/-- Restricting the recording tableau of a word to the letters `< k` gives the recording
tableau of the prefix of length `k` of the word. -/
theorem dropMax_RSQ (w : List T) (k : ℕ) : dropMax k (RSQ w) = RSQ (w.take k) := by
  induction w using List.reverseRecOn with
  | nil => simp [RSQ, recTab, recTabAux]
  | append_singleton w l ih =>
    rcases Nat.lt_or_ge w.length k with hk | hk
    · have htake : (w ++ [l]).take k = w ++ [l] :=
        List.take_of_length_le (by simp; omega)
      rw [htake]
      refine dropMax_of_forall_lt (isStdTab_RSQ _).1 fun x hx => ?_
      have hlt := lt_sizeTab_of_mem_flatten (isStdTab_RSQ (w ++ [l])) hx
      rw [sizeTab_RSQ] at hlt
      simp only [List.length_append, List.length_cons, List.length_nil] at hlt
      omega
    · have htake : (w ++ [l]).take k = w.take k := by
        rw [List.take_append_of_le_length hk]
      rw [htake, RSQ_concat, dropMax_addBox_of_le hk, ih]

end List
